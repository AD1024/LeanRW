use slotted_egraphs::*;
use tree_sitter::{Language, Node, Parser, Tree};

extern "C" {
    fn tree_sitter_lean() -> Language;
}

#[derive(Debug)]
pub enum LowerError {
    ParseError,
    TreeSitterError(String),
}

pub fn lower_lean_to_rec_expr(src: &str) -> Result<RecExpr<Lean>, LowerError> {
    let mut parser = Parser::new();
    unsafe {
        parser
            .set_language(tree_sitter_lean())
            .map_err(|e| LowerError::TreeSitterError(format!("Failed to set language: {e:?}")))?;
    }
    let tree = parser.parse(src, None).ok_or(LowerError::ParseError)?;

    let mut lowerer = Lowerer::new(src);
    // Adjust "source_file" if your root kind is different
    let root = tree.root_node();
    let root_id = lowerer.lower_toplevel(root)?;

    // You can return the whole RecExpr; root_id is the last node.
    Ok(lowerer.expr)
}

struct Lowerer<'a> {
    src: &'a [u8],
    pub expr: RecExpr<Lean>,
    // Map variable names to slots (or bind IDs, depending on how you represent them)
    vars: std::collections::HashMap<String, Slot>,
    next_slot: u32,
}

impl<'a> Lowerer<'a> {
    fn new(src: &'a str) -> Self {
        Self {
            src: src.as_bytes(),
            expr: RecExpr::default(),
            vars: std::collections::HashMap::new(),
            next_slot: 0,
        }
    }

    fn text(&self, node: Node) -> &str {
        &std::str::from_utf8(&self.src[node.byte_range()]).unwrap()
    }

    fn fresh_slot(&mut self) -> Slot {
        // Adjust this according to how Slot is constructed in slotted_egraphs
        let s = Slot(self.next_slot);
        self.next_slot += 1;
        s
    }

    /// Lower top-level declarations (e.g., `def`).
    fn lower_toplevel(&mut self, node: Node) -> Result<AppliedId, LowerError> {
        // Many Lean grammars use "toplevel_command" or similar
        // Here we just descend to the first child that is a def/ theorem / etc.
        let mut cur = node.walk();
        for child in node.children(&mut cur) {
            match child.kind() {
                "def" | "definition" => {
                    self.lower_def(child)?;
                }
                _ => {
                    // ignore other top-level commands for now
                }
            }
        }

        // Return last enode as root, or create some wrapper
        let last_id = self.expr.as_ref().last().map(|_| Id::from(self.expr.len() - 1));
        Ok(last_id.unwrap_or(Id::from(0)))
    }

    fn lower_def(&mut self, node: Node) -> Result<AppliedId, LowerError> {
        // Typical Lean4-style:
        // def <name> (params...) : <ret_type> := <body>
        //
        // You will have to inspect your tree-sitter grammar to see exact children.
        let mut cursor = node.walk();
        let mut name_node = None;
        let mut params = Vec::new();
        let mut ret_type = None;
        let mut body = None;

        for child in node.children(&mut cursor) {
            match child.kind() {
                "identifier" => {
                    if name_node.is_none() {
                        name_node = Some(child);
                    }
                }
                "fun_params" | "binders" => {
                    params.push(child);
                }
                "type" | "expr" => {
                    // heuristics: first type after params is ret_type (if preceded by ':')
                    // otherwise treat as body
                    if ret_type.is_none() && self.preceded_by_colon(child) {
                        ret_type = Some(child);
                    } else {
                        body = Some(child);
                    }
                }
                _ => {}
            }
        }

        let name_node = name_node.ok_or_else(|| LowerError::TreeSitterError("def without name".into()))?;
        let name_sym = self.symbol_from_identifier(name_node);

        let ret_ty_id = if let Some(rt) = ret_type {
            self.lower_expr(rt)?
        } else {
            // Default to Nat or some universe; tweak as needed
            self.expr.add(Lean::Symbol(self.symbol_from_str("Unit")))
        };

        // We fold parameters into nested Arg nodes that ultimately wrap a Begin(body)
        let body_id = self.lower_expr(body.ok_or_else(|| LowerError::TreeSitterError("def without body".into()))?)?;
        let mut fun_body = self.expr.add(Lean::FunBody(body_id));

        // Process params in reverse, building (Arg Type (Bind var body)) nest
        for param_group in params.into_iter().rev() {
            fun_body = self.lower_param_group(param_group, fun_body)?;
        }

        let def_name_id = self.expr.add(Lean::Symbol(name_sym));
        let fun_def = Lean::FunDef(def_name_id, ret_ty_id, fun_body);
        let def_id = self.expr.add(fun_def);
        Ok(def_id)
    }

    fn preceded_by_colon(&self, node: Node) -> bool {
        if let Some(prev) = node.prev_sibling() {
            self.text(prev).trim() == ":"
        } else {
            false
        }
    }

    fn symbol_from_identifier(&self, node: Node) -> Symbol {
        Symbol::from(self.text(node))
    }

    fn symbol_from_str(&self, s: &str) -> Symbol {
        Symbol::from(s)
    }

    /// Lower a parameter group like `(x y : Nat)` into nested `Arg` nodes.
    fn lower_param_group(&mut self, node: Node, body: AppliedId) -> Result<AppliedId, LowerError> {
        // Again, depends on grammar; assume children: identifiers... type
        let mut cursor = node.walk();
        let mut idents = Vec::new();
        let mut ty = None;
        for child in node.children(&mut cursor) {
            match child.kind() {
                "identifier" => idents.push(child),
                "type" | "expr" => ty = Some(child),
                _ => {}
            }
        }

        let ty_node = ty.ok_or_else(|| LowerError::TreeSitterError("param without type".into()))?;
        let ty_id = self.lower_expr(ty_node)?;

        let mut acc_body = body;
        for ident in idents.into_iter().rev() {
            let var_name = self.text(ident).to_string();
            let slot = self.fresh_slot();
            self.vars.insert(var_name.clone(), slot);

            // We represent binder as Bind<AppliedId> whose payload is the body
            // You may need a specific `Bind::new(slot, body)` or similar from slotted_egraphs.
            let bind = Bind::new(slot, acc_body); // <-- adjust to your actual API
            let arg_id = self.expr.add(Lean::FunArg(ty_id, bind));
            acc_body = arg_id;
        }

        Ok(acc_body)
    }

    /// General expression lowering.
    fn lower_expr(&mut self, node: Node) -> Result<AppliedId, LowerError> {
        match node.kind() {
            "identifier" => {
                let name = self.text(node);
                if let Some(slot) = self.vars.get(name) {
                    let id = self.expr.add(Lean::Var(*slot));
                    Ok(id)
                } else {
                    let sym = self.symbol_from_str(name);
                    Ok(self.expr.add(Lean::Symbol(sym)))
                }
            }
            "number" | "numeral" => {
                let n: u64 = self.text(node).parse().unwrap_or(0);
                Ok(self.expr.add(Lean::Nat(n)))
            }
            "true" | "false" => {
                let b = self.text(node) == "true";
                Ok(self.expr.add(Lean::Bool(b)))
            }

            // Function application
            "application" | "app" => {
                let mut cursor = node.walk();
                let mut children = node.children(&mut cursor).collect::<Vec<_>>();
                if children.len() < 2 {
                    return Err(LowerError::TreeSitterError("application with <2 children".into()));
                }

                // Left-associative: (((f a) b) c)
                let mut acc = self.lower_expr(children[0])?;
                for arg in &children[1..] {
                    let arg_id = self.lower_expr(*arg)?;
                    acc = self.expr.add(Lean::App(acc, arg_id));
                }
                Ok(acc)
            }

            // If-then-else
            "if" | "if_then_else" => {
                // Expect children: "if" cond "then" then_branch "else" else_branch
                let mut cursor = node.walk();
                let children: Vec<_> = node.children(&mut cursor).collect();
                // You will need to put the correct indices based on your grammar:
                let cond = self.lower_expr(children[1])?;
                let then_e = self.lower_expr(children[3])?;
                let else_e = self.lower_expr(children[5])?;
                Ok(self.expr.add(Lean::IfThenElse(cond, then_e, else_e)))
            }

            // Match expressions
            "match" | "match_expr" => self.lower_match(node),

            // Binary infix operators
            "infix" | "infix_expr" => {
                let mut cursor = node.walk();
                let lhs = node.child_by_field_name("lhs").unwrap();
                let rhs = node.child_by_field_name("rhs").unwrap();
                let op_node = node.child_by_field_name("op").unwrap();
                let op_str = self.text(op_node);

                let lhs_id = self.lower_expr(lhs)?;
                let rhs_id = self.lower_expr(rhs)?;
                let enode = match op_str {
                    "+" => Lean::Add(lhs_id, rhs_id),
                    "-" => Lean::Sub(lhs_id, rhs_id),
                    "*" => Lean::Mul(lhs_id, rhs_id),
                    "/" => Lean::Div(lhs_id, rhs_id),
                    "%" => Lean::Mod(lhs_id, rhs_id),

                    "=" => Lean::Eq(lhs_id, rhs_id),
                    "!=" => Lean::Ne(lhs_id, rhs_id),
                    "<" => Lean::Lt(lhs_id, rhs_id),
                    "<=" => Lean::Le(lhs_id, rhs_id),
                    ">" => Lean::Gt(lhs_id, rhs_id),
                    ">=" => Lean::Ge(lhs_id, rhs_id),

                    "&&" | "∧" => Lean::And(lhs_id, rhs_id),
                    "||" | "∨" => Lean::Or(lhs_id, rhs_id),

                    "->" | "→" => Lean::Implies(lhs_id, rhs_id),
                    "<->" | "↔" => Lean::Iff(lhs_id, rhs_id),

                    _ => {
                        // Generic infix if not recognized:
                        let op_id = self.expr.add(Lean::Symbol(self.symbol_from_str(op_str)));
                        Lean::InfixOp(op_id, lhs_id, rhs_id)
                    }
                };
                Ok(self.expr.add(enode))
            }

            // Lambda / fun
            "fun" | "lambda" => {
                // fun x => body
                // Map to `Lam(Bind<AppliedId>)`
                let mut cursor = node.walk();
                let mut params = Vec::new();
                let mut body = None;
                for child in node.children(&mut cursor) {
                    match child.kind() {
                        "identifier" => params.push(child),
                        "expr" => body = Some(child),
                        _ => {}
                    }
                }
                let mut body_id = self.lower_expr(body.unwrap())?;
                for param in params.into_iter().rev() {
                    let name = self.text(param).to_string();
                    let slot = self.fresh_slot();
                    self.vars.insert(name, slot);
                    let bind = Bind::new(slot, body_id); // adjust as needed
                    body_id = self.expr.add(Lean::Lam(bind));
                }
                Ok(body_id)
            }

            // Fallback: treat as Proj or Symbol or recurse into first child
            _ => {
                if node.child_count() == 0 {
                    // leaf we don't know about
                    let sym = self.symbol_from_str(self.text(node));
                    Ok(self.expr.add(Lean::Symbol(sym)))
                } else {
                    // default: lower first child
                    let mut cursor = node.walk();
                    if let Some(first) = node.children(&mut cursor).next() {
                        self.lower_expr(first)
                    } else {
                        Err(LowerError::TreeSitterError(format!(
                            "Unhandled node kind {} with children",
                            node.kind()
                        )))
                    }
                }
            }
        }
    }

    fn lower_match(&mut self, node: Node) -> Result<AppliedId, LowerError> {
        // Rough sketch:
        // match xs with
        // | []      => e1
        // | h :: t  => e2
        // end
        //
        // => (Match scrut (Case pat1 body1 (Case pat2 body2 MatchEnd)))
        let mut cursor = node.walk();
        let mut scrut = None;
        let mut cases = Vec::new();

        for child in node.children(&mut cursor) {
            match child.kind() {
                "expr" if scrut.is_none() => scrut = Some(child),
                "match_case" | "equation" => cases.push(child),
                _ => {}
            }
        }

        let scrut_id = self.lower_expr(scrut.ok_or_else(|| LowerError::TreeSitterError("match without scrutinee".into()))?)?;

        let mut tail = self.expr.add(Lean::MatchEnd());
        for c in cases.into_iter().rev() {
            tail = self.lower_case(c, tail)?;
        }

        let match_id = self.expr.add(Lean::Match(scrut_id, tail));
        Ok(match_id)
    }

    fn lower_case(&mut self, node: Node, next: AppliedId) -> Result<AppliedId, LowerError> {
        // Expect pattern + rhs expr
        let mut cursor = node.walk();
        let mut pat = None;
        let mut body = None;
        for child in node.children(&mut cursor) {
            match child.kind() {
                "pattern" => pat = Some(child),
                "expr" => body = Some(child),
                _ => {}
            }
        }

        let pat_id = self.lower_pattern(pat.ok_or_else(|| LowerError::TreeSitterError("case without pattern".into()))?)?;
        let body_id = self.lower_expr(body.ok_or_else(|| LowerError::TreeSitterError("case without body".into()))?)?;
        let case_id = self.expr.add(Lean::Case(pat_id, body_id, next));
        Ok(case_id)
    }

    fn lower_pattern(&mut self, node: Node) -> Result<AppliedId, LowerError> {
        // Very rough: handle `[]` and `h :: t` (Cons) and variables
        match node.kind() {
            "nil_pattern" => Ok(self.expr.add(Lean::Nil())),
            "cons_pattern" => {
                let mut cursor = node.walk();
                let mut head = None;
                let mut tail = None;
                for child in node.children(&mut cursor) {
                    match child.kind() {
                        "identifier" if head.is_none() => head = Some(child),
                        "identifier" if tail.is_none() => tail = Some(child),
                        _ => {}
                    }
                }
                let head_slot = self.fresh_slot();
                let tail_slot = self.fresh_slot();
                self.vars.insert(self.text(head.unwrap()).to_string(), head_slot);
                self.vars.insert(self.text(tail.unwrap()).to_string(), tail_slot);
                let head_id = self.expr.add(Lean::Var(head_slot));
                let tail_id = self.expr.add(Lean::Var(tail_slot));
                Ok(self.expr.add(Lean::Cons(head_id, tail_id)))
            }
            "identifier" => {
                // variable pattern
                let name = self.text(node).to_string();
                let slot = self.fresh_slot();
                self.vars.insert(name, slot);
                Ok(self.expr.add(Lean::Var(slot)))
            }
            _ => {
                // fallback
                let sym = self.symbol_from_str(self.text(node));
                Ok(self.expr.add(Lean::Symbol(sym)))
            }
        }
    }
}
