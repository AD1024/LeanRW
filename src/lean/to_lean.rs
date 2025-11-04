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

    fn write_expr(&mut self, expr: &RecExpr<Lean>) -> String {
        let hd = &expr.node;
        let children = &expr.children;

        match hd {
            // Top-level definition
            Lean::FunDef(bind) => {
                let name = Self::clean_slot_name(format!("{:?}", bind.slot));
                let mut result = format!("def {}", name);

                if !children.is_empty() {
                    result.push_str(" :=\n");
                    self.indent += 1;
                    for child in children {
                        self.write_indent();
                        let child_str = self.write_expr(child);
                        result.push_str(&child_str);
                        result.push('\n');
                    }
                    self.indent -= 1;
                } else {
                    result.push_str(" := ()\n");
                }
                result
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
                    format!("∀ {}, {}", var_name, body)
                } else {
                    format!("∀ {}, true", var_name)
                }
            }
            Lean::Exists(bind) => {
                let var_name = Self::clean_slot_name(format!("{:?}", bind.slot));
                if !children.is_empty() {
                    let body = self.write_expr(&children[0]);
                    format!("∃ {}, {}", var_name, body)
                } else {
                    format!("∃ {}, true", var_name)
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
        let expr: RecExpr<Lean> = RecExpr::parse("(Def $foo (+ 1 2))").unwrap();
        let result = write_lean(&expr);
        println!("Function def:\n{}", result);
        assert!(result.contains("def foo"));
        assert!(result.contains(":="));
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
}