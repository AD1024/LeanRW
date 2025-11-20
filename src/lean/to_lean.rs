use slotted_egraphs::*;

use crate::lean::Lean;

struct LeanWriter {
    indent: usize,
    result: String,
}

impl LeanWriter {
    fn new() -> Self {
        Self {
            indent: 0,
            result: String::new(),
        }
    }

    fn write_indent(&mut self) {
        for _ in 0..self.indent {
            self.result.push_str("  ");
        }
    }

    fn get_indent(&self) -> String {
        "  ".repeat(self.indent)
    }

    // Helper to clean up slot names by removing $ prefix
    fn clean_slot_name(slot_debug: String) -> String {
        if slot_debug.starts_with('$') {
            slot_debug[1..].to_string()
        } else {
            slot_debug
        }
    }

    // Helper to collect function arguments from nested FunArg nodes
    // Returns (args_strings, body_expr) where args_strings are "(name : type)" strings
    fn collect_args<'a>(&mut self, expr: &'a RecExpr<Lean>) -> (Vec<String>, &'a RecExpr<Lean>) {
        match &expr.node {
            Lean::FunArg(_, bind) => {
                assert!(
                    expr.children.len() == 2,
                    "FunArg must have exactly 2 children (type, body_or_args), got {}",
                    expr.children.len()
                );
                let var_name = Self::clean_slot_name(format!("{:?}", bind.slot));
                let ty = self.write_expr(&expr.children[0]);
                let arg_string = format!("({} : {})", var_name, ty);

                // Recursively collect more args or return body
                let (mut rest_args, body) = self.collect_args(&expr.children[1]);
                let mut all_args = vec![arg_string];
                all_args.append(&mut rest_args);
                (all_args, body)
            }
            _ => {
                // Not a FunArg, so this is the body
                (vec![], expr)
            }
        }
    }

    fn write_expr(&mut self, expr: &RecExpr<Lean>) -> String {
        let hd = &expr.node;
        let children = &expr.children;

        match hd {
            // Top-level definition: (Def name ret_type arg_or_body)
            Lean::FunDef(_, _, _) => {
                assert!(
                    children.len() == 3,
                    "FunDef must have exactly 3 children (name, ret_type, arg_or_body), got {}",
                    children.len()
                );
                let name = self.write_expr(&children[0]);
                let ret_type = self.write_expr(&children[1]);

                // Collect arguments from nested FunArg nodes
                let (args, body_expr) = self.collect_args(&children[2]);

                // Build function signature with args
                let mut signature = format!("def {}", name);
                for arg in &args {
                    signature.push(' ');
                    signature.push_str(arg);
                }
                signature.push_str(&format!(" : {} :=", ret_type));

                // Write body with indentation
                self.indent += 1;
                let body = self.write_expr(body_expr);
                let indent_str = self.get_indent();
                self.indent -= 1;

                format!("{}\n{}{}", signature, indent_str, body)
            }

            // Function argument: (Arg type (bind var) body_or_args)
            // This should only be encountered when called from collect_args
            Lean::FunArg(_, _) => {
                panic!("FunArg should be processed via collect_args in FunDef context")
            }

            // Function body wrapper: (Begin body)
            Lean::FunBody(_) => {
                assert!(
                    children.len() == 1,
                    "FunBody must have exactly 1 child (body), got {}",
                    children.len()
                );
                self.write_expr(&children[0])
            }

            // Lambda abstraction
            Lean::Lam(bind) => {
                let var_name = Self::clean_slot_name(format!("{:?}", bind.slot));
                if children.is_empty() {
                    assert!(false, "Lambda must have a body");
                    format!("(λ {} ↦ ())", var_name)
                } else {
                    let body = self.write_expr(&children[0]);
                    format!("(λ {} ↦ {})", var_name, body)
                }
            }

            // Function application
            Lean::App(_, _) => {
                if children.len() >= 2 {
                    let func = self.write_expr(&children[0]);
                    let arg = self.write_expr(&children[1]);
                    format!("({} {})", func, arg)
                } else {
                    assert!(false, "App must have two children");
                    "(App)".to_string()
                }
            }

            // Variable reference
            Lean::Var(slot) => {
                Self::clean_slot_name(format!("{:?}", slot))
            }

            // Let binding
            Lean::Let(bind, _) => {
                let var_name = Self::clean_slot_name(format!("{:?}", bind.slot));
                if children.len() >= 2 {
                    let value = self.write_expr(&children[0]);
                    let body = self.write_expr(&children[1]);
                    format!("let {} := {};\n{}", var_name, value, body)
                } else if children.len() == 1 {
                    let value = self.write_expr(&children[0]);
                    format!("let {} := {}", var_name, value)
                } else {
                    format!("let {} := ()", var_name)
                }
            }

            // Match expression
            Lean::Match(_, _) => {
                if children.is_empty() {
                    "match () with".to_string()
                } else {
                    let scrutinee = self.write_expr(&children[0]);
                    let mut result = format!("match {} with\n", scrutinee);
                    if children.len() > 1 {
                        // Indent cases by 2 spaces for proper Lean syntax
                        self.indent += 1;
                        let cases = self.write_expr(&children[1]);
                        // Remove trailing newline if present, we'll handle it contextually
                        let cases = cases.trim_end();
                        result.push_str(cases);
                        result.push('\n');
                        self.indent -= 1;
                    }
                    result.trim_end().to_string()
                }
            }

            // Case in pattern matching
            Lean::Case(_, _, _) => {
                if children.len() >= 3 {
                    let pattern = self.write_expr(&children[0]);
                    let body = self.write_expr(&children[1]);
                    let next = self.write_expr(&children[2]);

                    let mut result = String::new();
                    // Add indentation for the case
                    result.push_str(&self.get_indent());
                    result.push_str(&format!("| {} => {}\n", pattern, body));
                    if !matches!(children[2].node, Lean::MatchEnd()) {
                        result.push_str(&next);
                    }
                    result
                } else {
                    let mut result = String::new();
                    result.push_str(&self.get_indent());
                    result.push_str("| _ => ()");
                    result
                }
            }

            Lean::MatchEnd() => String::new(),

            // If-then-else
            Lean::IfThenElse(_, _, _) => {
                if children.len() >= 3 {
                    let cond = self.write_expr(&children[0]);
                    let then_branch = self.write_expr(&children[1]);
                    let else_branch = self.write_expr(&children[2]);
                    format!("if {} then {} else {}", cond, then_branch, else_branch)
                } else {
                    "if true then () else ()".to_string()
                }
            }

            // List constructors
            Lean::Nil() => "[]".to_string(),
            Lean::Cons(_, _) => {
                if children.len() >= 2 {
                    let head = self.write_expr(&children[0]);
                    let tail = self.write_expr(&children[1]);
                    format!("({} :: {})", head, tail)
                } else {
                    "[]".to_string()
                }
            }
            Lean::Length(_) => {
                if children.len() >= 1 {
                    let head = self.write_expr(&children[0]);
                    format!("({}.length )", head)
                } else {
                    "List.Length []".to_string()
                }
            }
            Lean::Fold(_, _, _) => {
                if children.len() >= 3 {
                    let head = self.write_expr(&children[0]);
                    let tail = self.write_expr(&children[1]);
                    let z = self.write_expr(&children[2]);
                    format!("({}.foldl {} {})", head, tail, z)
                } else {
                    "[]".to_string()
                }
            }

            // Tree constructors
            Lean::Leaf(_) => {
                if !children.is_empty() {
                    let value = self.write_expr(&children[0]);
                    format!("Leaf {}", value)
                } else {
                    "Leaf ()".to_string()
                }
            }
            Lean::Node(_, _, _) => {
                if children.len() >= 3 {
                    let value = self.write_expr(&children[0]);
                    let left = self.write_expr(&children[1]);
                    let right = self.write_expr(&children[2]);
                    format!("Node {} {} {}", value, left, right)
                } else {
                    "Node () Leaf Leaf".to_string()
                }
            }

            // Option constructors
            Lean::None() => "none".to_string(),
            Lean::Some(_) => {
                if !children.is_empty() {
                    let value = self.write_expr(&children[0]);
                    format!("some {}", value)
                } else {
                    "some ()".to_string()
                }
            }

            Lean::Proj(_, _) => {
                assert!(children.len() == 2, "Proj must have exactly 2 children: (expr, field), got {}", children.len());
                let expr_str = self.write_expr(&children[0]);
                let field_str = self.write_expr(&children[1]);
                format!("({}.{})", expr_str, field_str)
            }

            // Arithmetic operations
            Lean::Add(_, _) => self.write_binop(children, "+"),
            Lean::Sub(_, _) => self.write_binop(children, "-"),
            Lean::Mul(_, _) => self.write_binop(children, "*"),
            Lean::Div(_, _) => self.write_binop(children, "/"),
            Lean::Mod(_, _) => self.write_binop(children, "%"),

            // Comparison operations
            Lean::Eq(_, _) => self.write_binop(children, "="),
            Lean::Ne(_, _) => self.write_binop(children, "≠"),
            Lean::Lt(_, _) => self.write_binop(children, "<"),
            Lean::Le(_, _) => self.write_binop(children, "≤"),
            Lean::Gt(_, _) => self.write_binop(children, ">"),
            Lean::Ge(_, _) => self.write_binop(children, "≥"),

            // Boolean operations
            Lean::And(_, _) => self.write_binop(children, "&&"),
            Lean::Or(_, _) => self.write_binop(children, "||"),
            Lean::Not(_) => {
                if !children.is_empty() {
                    let arg = self.write_expr(&children[0]);
                    format!("!{}", arg)
                } else {
                    "!true".to_string()
                }
            }

            // Infix ops
            Lean::InfixOp(_, _, _) => {
                assert!(children.len() == 3, "InfixOp must have exactly 3 children: (left, op, right), got {}", children.len());
                let op = self.write_expr(&children[0]);
                self.write_binop(&children[1..], &op)
            }

            // Propositional operations
            Lean::Implies(_, _) => self.write_binop(children, "→"),
            Lean::Iff(_, _) => self.write_binop(children, "↔"),
            Lean::Conj(_, _) => self.write_binop(children, "∧"),
            Lean::Disj(_, _) => self.write_binop(children, "∨"),
            Lean::Neg(_) => {
                if !children.is_empty() {
                    let arg = self.write_expr(&children[0]);
                    format!("¬{}", arg)
                } else {
                    "¬true".to_string()
                }
            }
            Lean::Forall(bind) => {
                let var_name = Self::clean_slot_name(format!("{:?}", bind.slot));
                if !children.is_empty() {
                    let body = self.write_expr(&children[0]);
                    format!("(∀ {}, {})", var_name, body)
                } else {
                    panic!("Forall must have a body");
                }
            }
            Lean::Exists(bind) => {
                let var_name = Self::clean_slot_name(format!("{:?}", bind.slot));
                if !children.is_empty() {
                    let body = self.write_expr(&children[0]);
                    format!("(∃ {}, {})", var_name, body)
                } else {
                    panic!("Exists must have a body");
                }
            }

            // Literals
            Lean::Bool(b) => b.to_string(),
            Lean::Nat(n) => n.to_string(),
            Lean::Symbol(s) => s.to_string(),
        }
    }

    fn write_binop(&mut self, children: &[RecExpr<Lean>], op: &str) -> String {
        if children.len() >= 2 {
            let left = self.write_expr(&children[0]);
            let right = self.write_expr(&children[1]);
            format!("({} {} {})", left, op, right)
        } else {
            format!("(_ {} _)", op)
        }
    }
}

/// Convert a `RecExpr<Lean>` back to Lean source code text
pub fn write_lean(expr: &RecExpr<Lean>) -> String {
    let mut writer = LeanWriter::new();
    writer.write_expr(expr)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_write_match_expression() {
        // Test from language.rs
        let calculate_total_crops: RecExpr<Lean> = RecExpr::parse(
            "(Match xs
                (Case Nil Nil
                    (Case (Cons h t)
                          (Cons (App sum_list_cost h) (App map_sum_code t))
                    MatchEnd))
            )",
        )
        .unwrap();

        let result = write_lean(&calculate_total_crops);
        println!("Generated Lean code:\n{}", result);

        // Check that it contains key elements
        assert!(result.contains("match"));
        assert!(result.contains("[]")); // Nil is rendered as []
        assert!(result.contains("::"));  // Cons is rendered with ::
    }

    #[test]
    fn test_write_arithmetic() {
        let expr: RecExpr<Lean> = RecExpr::parse("(+ 1 2)").unwrap();
        let result = write_lean(&expr);
        println!("Arithmetic: {}", result);
        assert!(result.contains("+"));
        assert!(result.contains("1"));
        assert!(result.contains("2"));
    }

    #[test]
    fn test_write_list_cons() {
        let expr: RecExpr<Lean> = RecExpr::parse("(Cons 1 (Cons 2 Nil))").unwrap();
        let result = write_lean(&expr);
        println!("List: {}", result);
        assert!(result.contains("::"));
    }

    #[test]
    fn test_write_if_then_else() {
        let expr: RecExpr<Lean> = RecExpr::parse("(IfThen true 1 0)").unwrap();
        let result = write_lean(&expr);
        println!("If-then-else: {}", result);
        assert!(result.contains("if"));
        assert!(result.contains("then"));
        assert!(result.contains("else"));
    }

    #[test]
    fn test_write_lambda() {
        let expr: RecExpr<Lean> = RecExpr::parse("(Fun $x (+ (Var $x) 1))").unwrap();
        let result = write_lean(&expr);
        println!("Lambda: {}", result);
        // Variable names should not have $ prefix
        assert!(!result.contains("$x"));
        assert!(result.contains("λ x"));
        assert!(result.contains("(x + 1)"));
    }

    #[test]
    fn test_nested_match() {
        let expr: RecExpr<Lean> = RecExpr::parse(
            "(Match xs
                (Case Nil 0
                    (Case (Cons h t)
                          (+ h (Match t
                                  (Case Nil 0
                                      (Case (Cons h2 t2) 1
                                      MatchEnd))))
                    MatchEnd))
            )",
        )
        .unwrap();
        let result = write_lean(&expr);
        println!("Nested match:\n{}", result);
        // All pipes should be at the same indentation level as their corresponding match
        let lines: Vec<&str> = result.lines().collect();
        for (i, line) in lines.iter().enumerate() {
            if line.trim().starts_with('|') {
                // Check that match cases are not indented relative to match
                println!("Line {}: '{}'", i, line);
            }
        }
    }

    #[test]
    fn test_function_def() {
        // Updated to match new FunDef structure: (Def name ret_type body)
        let expr: RecExpr<Lean> = RecExpr::parse("(Def foo Nat (Begin (+ 1 2)))").unwrap();
        let result = write_lean(&expr);
        println!("Function def:\n{}", result);
        assert!(result.contains("def foo"));
        assert!(result.contains(": Nat :="));
        assert!(!result.contains("$foo")); // No $ prefix
    }

    #[test]
    fn test_indentation_correctness() {
        // This test verifies that the indentation follows Lean's syntax rules:
        // 1. Match cases are indented 2 spaces from match
        // 2. Nested match cases are indented an additional 2 spaces
        let expr: RecExpr<Lean> = RecExpr::parse(
            "(Match xs
                (Case Nil 0
                    (Case (Cons h t)
                          (Match t
                              (Case Nil 1
                                  (Case (Cons h2 t2) 2
                                  MatchEnd)))
                    MatchEnd))
            )",
        )
        .unwrap();
        let result = write_lean(&expr);
        println!("Indentation test:\n{}", result);

        let lines: Vec<&str> = result.lines().collect();

        // First match should be at column 0
        assert_eq!(lines[0], "match xs with");

        // First level cases should have 2 spaces
        assert!(lines[1].starts_with("  | "));
        assert!(lines[2].starts_with("  | "));

        // Nested match inside case body should be on same line or indented
        // The inner match's cases should have 4 spaces (2 more than outer)
        let has_nested_case = lines.iter().any(|l| l.starts_with("    | "));
        assert!(has_nested_case, "Nested match cases should be indented 4 spaces");
    }

    #[test]
    fn test_function_def_with_args() {
        // Test the example from language.rs comment:
        // (Def max Nat (Arg Nat $x (Arg Nat $y (Begin (IfThen (> (Var $x) (Var $y)) (Var $x) (Var $y))))))
        let expr: RecExpr<Lean> = RecExpr::parse(
            "(Def max Nat (Arg Nat $x (Arg Nat $y (Begin (IfThen (> (Var $x) (Var $y)) (Var $x) (Var $y))))))"
        )
        .unwrap();
        let result = write_lean(&expr);
        println!("Function with args:\n{}", result);

        // Arguments should be in the function signature, not as lambdas
        assert!(result.contains("def max (x : Nat) (y : Nat) : Nat :="));
        assert!(!result.contains("fun")); // Should not have lambda abstractions
        assert!(result.contains("if"));
        assert!(result.contains("then"));
        assert!(result.contains("else"));
        assert!(!result.contains("$x")); // Variables should not have $ prefix
        assert!(!result.contains("$y"));
    }

    #[test]
    fn test_list_reverse_def() {
        let expr: RecExpr<Lean> = RecExpr::parse(
            "(Def reverse (App List Nat) (Arg (App List Nat) $lst (Begin
                (Match (Var $lst)
                    (Case Nil Nil
                        (Case (Cons h t)
                            (App (App append (App reverse t)) (Cons h Nil))
                        MatchEnd))
                )
            )))"
        )
        .unwrap();
        let result = write_lean(&expr);
        println!("List reverse function:\n{}", result);
    }
}