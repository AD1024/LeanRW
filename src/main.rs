mod lean;
mod rewrites;
mod extraction;
mod serialize;

use lean::{Lean, write_lean};
use slotted_egraphs::*;

fn main() {
    println!("=== Lean Code Generation Demo ===\n");

    // Example 1: Match expression
    let match_expr: RecExpr<Lean> = RecExpr::parse(
        "(Match xs
            (Case Nil Nil
                (Case (Cons h t)
                      (Cons (App sum_list_cost h) (App map_sum_code t))
                MatchEnd))
        )",
    )
    .unwrap();

    println!("Example 1 - Pattern Matching:");
    println!("{}\n", write_lean(&match_expr));

    // Example 2: Nested match with proper indentation
    let nested_match: RecExpr<Lean> = RecExpr::parse(
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

    println!("Example 2 - Nested Match:");
    println!("{}\n", write_lean(&nested_match));

    // Example 3: Arithmetic
    let arith_expr: RecExpr<Lean> = RecExpr::parse("(+ (* 2 3) (- 10 5))").unwrap();
    println!("Example 3 - Arithmetic:");
    println!("{}\n", write_lean(&arith_expr));

    // Example 4: List construction
    let list_expr: RecExpr<Lean> = RecExpr::parse("(Cons 1 (Cons 2 (Cons 3 Nil)))").unwrap();
    println!("Example 4 - List:");
    println!("{}\n", write_lean(&list_expr));

    // Example 5: Lambda expression
    let lambda_expr: RecExpr<Lean> = RecExpr::parse("(Fun $x (+ (Var $x) 1))").unwrap();
    println!("Example 5 - Lambda (note: $ prefix removed):");
    println!("{}\n", write_lean(&lambda_expr));

    // Example 6: Conditional
    let cond_expr: RecExpr<Lean> = RecExpr::parse("(IfThen (< x 10) (+ x 1) (* x 2))").unwrap();
    println!("Example 6 - Conditional:");
    println!("{}\n", write_lean(&cond_expr));

    // Example 7: Boolean and propositional operators
    let bool_expr: RecExpr<Lean> = RecExpr::parse("(& (< x 10) (> x 0))").unwrap();
    println!("Example 7 - Boolean Expression:");
    println!("{}\n", write_lean(&bool_expr));

    println!("=== All examples generated successfully! ===");
}
