use slotted_egraphs::{rw, Rewrite};

use crate::lean::{Lean, LeanAnalysis};

// ============================================================================
// Arithmetic Rules - Commutativity, Associativity, Identity, Distributivity
// ============================================================================

fn arith_rules() -> Vec<Rewrite<Lean, LeanAnalysis>> {
    vec![
        // Commutativity
        rw!("add-comm"; "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("mul-comm"; "(* ?a ?b)" => "(* ?b ?a)"),

        // Associativity (bidirectional)
        rw!("add-assoc-left"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("add-assoc-right"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rw!("mul-assoc-left"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rw!("mul-assoc-right"; "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),

        // Distributivity (bidirectional)
        rw!("distrib-left"; "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
        rw!("distrib-right"; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
        rw!("distrib-left-2"; "(* (+ ?a ?b) ?c)" => "(+ (* ?a ?c) (* ?b ?c))"),
        rw!("distrib-right-2"; "(+ (* ?a ?c) (* ?b ?c))" => "(* (+ ?a ?b) ?c)"),

        // Subtraction transformations
        rw!("sub-as-add-neg"; "(- ?a ?b)" => "(+ ?a (- 0 ?b))"),
        rw!("sub-self"; "(- ?a ?a)" => "0"),

        // Identity elements (constants need to be handled carefully)
        rw!("add-zero-right"; "(+ ?a 0)" => "?a"),
        rw!("add-zero-left"; "(+ 0 ?a)" => "?a"),
        rw!("mul-one-right"; "(* ?a 1)" => "?a"),
        rw!("mul-one-left"; "(* 1 ?a)" => "?a"),
        rw!("mul-zero-right"; "(* ?a 0)" => "0"),
        rw!("mul-zero-left"; "(* 0 ?a)" => "0"),
    ]
}

// ============================================================================
// Comparison Rules - Symmetry, Transitivity, Inversions
// ============================================================================

fn comp_rules() -> Vec<Rewrite<Lean, LeanAnalysis>> {
    vec![
        // Symmetry
        rw!("eq-symm"; "(= ?a ?b)" => "(= ?b ?a)"),
        rw!("ne-symm"; "(!= ?a ?b)" => "(!= ?b ?a)"),

        // Less-than / Greater-than duality
        rw!("lt-to-gt"; "(< ?a ?b)" => "(> ?b ?a)"),
        rw!("gt-to-lt"; "(> ?a ?b)" => "(< ?b ?a)"),
        rw!("le-to-ge"; "(<= ?a ?b)" => "(>= ?b ?a)"),
        rw!("ge-to-le"; "(>= ?a ?b)" => "(<= ?b ?a)"),

        // Strict to non-strict comparisons
        rw!("lt-to-le-ne"; "(< ?a ?b)" => "(and (<= ?a ?b) (!= ?a ?b))"),
        rw!("gt-to-ge-ne"; "(> ?a ?b)" => "(and (>= ?a ?b) (!= ?a ?b))"),

        // Not-equal decompositions
        rw!("ne-to-lt-or-gt"; "(!= ?a ?b)" => "(or (< ?a ?b) (> ?a ?b))"),

        // Negated comparisons
        rw!("not-lt-to-ge"; "(not (< ?a ?b))" => "(>= ?a ?b)"),
        rw!("not-le-to-gt"; "(not (<= ?a ?b))" => "(> ?a ?b)"),
        rw!("not-gt-to-le"; "(not (> ?a ?b))" => "(<= ?a ?b)"),
        rw!("not-ge-to-lt"; "(not (>= ?a ?b))" => "(< ?a ?b)"),
        rw!("not-eq-to-ne"; "(not (= ?a ?b))" => "(!= ?a ?b)"),
        rw!("not-ne-to-eq"; "(not (!= ?a ?b))" => "(= ?a ?b)"),
    ]
}

// ============================================================================
// Boolean Logic Rules - AND, OR, NOT transformations
// ============================================================================

fn bool_rules() -> Vec<Rewrite<Lean, LeanAnalysis>> {
    vec![
        // Commutativity
        rw!("and-comm"; "(& ?a ?b)" => "(& ?b ?a)"),
        rw!("or-comm"; "(| ?a ?b)" => "(| ?b ?a)"),

        // Associativity
        rw!("and-assoc-left"; "(& ?a (& ?b ?c))" => "(& (& ?a ?b) ?c)"),
        rw!("and-assoc-right"; "(& (& ?a ?b) ?c)" => "(& ?a (& ?b ?c))"),
        rw!("or-assoc-left"; "(| ?a (| ?b ?c))" => "(| (| ?a ?b) ?c)"),
        rw!("or-assoc-right"; "(| (| ?a ?b) ?c)" => "(| ?a (| ?b ?c))"),

        // De Morgan's Laws
        rw!("de-morgan-and"; "(not (& ?a ?b))" => "(| (not ?a) (not ?b))"),
        rw!("de-morgan-or"; "(not (| ?a ?b))" => "(& (not ?a) (not ?b))"),
        rw!("de-morgan-and-rev"; "(| (not ?a) (not ?b))" => "(not (& ?a ?b))"),
        rw!("de-morgan-or-rev"; "(& (not ?a) (not ?b))" => "(not (| ?a ?b))"),

        // Distributivity
        rw!("and-over-or"; "(& ?a (| ?b ?c))" => "(| (& ?a ?b) (& ?a ?c))"),
        rw!("or-over-and"; "(| ?a (& ?b ?c))" => "(& (| ?a ?b) (| ?a ?c))"),

        // Absorption
        rw!("and-absorb"; "(& ?a (| ?a ?b))" => "?a"),
        rw!("or-absorb"; "(| ?a (& ?a ?b))" => "?a"),

        // Identity and annihilation (with constants)
        rw!("and-true"; "(& ?a true)" => "?a"),
        rw!("and-false"; "(& ?a false)" => "false"),
        rw!("or-true"; "(| ?a true)" => "true"),
        rw!("or-false"; "(| ?a false)" => "?a"),

        // Idempotence
        rw!("and-idem"; "(& ?a ?a)" => "?a"),
        rw!("or-idem"; "(| ?a ?a)" => "?a"),
    ]
}

// ============================================================================
// Propositional Logic Rules - Implications, Quantifiers
// ============================================================================

fn prop_rules() -> Vec<Rewrite<Lean, LeanAnalysis>> {
    vec![
        // Implication transformations
        rw!("impl-to-disj"; "(-> ?a ?b)" => "(or (neg ?a) ?b)"),
        rw!("impl-from-disj"; "(or (neg ?a) ?b)" => "(-> ?a ?b)"),

        // Biconditional (iff) transformations
        rw!("iff-to-conj"; "(<-> ?a ?b)" => "(and (-> ?a ?b) (-> ?b ?a))"),
        rw!("iff-from-conj"; "(and (-> ?a ?b) (-> ?b ?a))" => "(<-> ?a ?b)"),
        rw!("iff-to-eq"; "(<-> ?a ?b)" => "(and (or (neg ?a) ?b) (or (neg ?b) ?a))"),

        // De Morgan's Laws for propositions
        rw!("de-morgan-conj"; "(neg (and ?a ?b))" => "(or (neg ?a) (neg ?b))"),
        rw!("de-morgan-disj"; "(neg (or ?a ?b))" => "(and (neg ?a) (neg ?b))"),

        // Quantifier duality
        rw!("forall-to-neg-exists"; "(forall $x ?P)" => "(neg (exists $x (neg ?P)))"),
        rw!("exists-to-neg-forall"; "(exists $x ?P)" => "(neg (forall $x (neg ?P)))"),

        // Quantifier distribution
        rw!("forall-conj"; "(forall $x (and ?P ?Q))" => "(and (forall $x ?P) (forall $x ?Q))"),
        rw!("exists-disj"; "(exists $x (or ?P ?Q))" => "(or (exists $x ?P) (exists $x ?Q))"),

        // Contrapositive
        rw!("contrapositive"; "(-> ?a ?b)" => "(-> (neg ?b) (neg ?a))"),

        // Material implication variants
        rw!("impl-as-disj-conj"; "(-> ?a ?b)" => "(or (neg ?a) (and ?a ?b))"),
    ]
}

// ============================================================================
// Control Flow Transformations - If-then-else, Pattern matching
// ============================================================================

fn control_flow_rules() -> Vec<Rewrite<Lean, LeanAnalysis>> {
    vec![
        // If-then-else transformations
        rw!("if-swap-branches"; "(IfThen ?cond ?then ?else)" => "(IfThen (not ?cond) ?else ?then)"),
        rw!("if-true"; "(IfThen true ?then ?else)" => "?then"),
        rw!("if-false"; "(IfThen false ?then ?else)" => "?else"),
        rw!("if-same-branches"; "(IfThen ?cond ?x ?x)" => "?x"),

        // Nested if normalization
        rw!("if-factor-cond"; "(IfThen ?c1 (IfThen ?c2 ?a ?b) (IfThen ?c2 ?x ?y))" =>
            "(IfThen ?c2 (IfThen ?c1 ?a ?x) (IfThen ?c1 ?b ?y))"),

        // If to match (for simple cases)
        rw!("if-to-match-true"; "(IfThen ?cond ?then ?else)" =>
            "(Match ?cond (Case true ?then (Case false ?else MatchEnd)))"),
    ]
}

// ============================================================================
// Lambda Calculus / Function Application Rules
// ============================================================================

fn lambda_rules() -> Vec<Rewrite<Lean, LeanAnalysis>> {
    vec![
        // Beta reduction (application of lambda)
        rw!("beta-reduce"; "(App (Fun $x ?body) ?arg)" => "(Let $x ?arg ?body)"),
    ]
}

// ============================================================================
// Let-binding transformations
// ============================================================================

fn let_rules() -> Vec<Rewrite<Lean, LeanAnalysis>> {
    vec![
        // Let floating (move let outward)
        rw!("let-float-add"; "(+ (Let $x ?v ?body) ?e)" => "(Let $x ?v (+ ?body ?e))"),
        rw!("let-float-mul"; "(* (Let $x ?v ?body) ?e)" => "(Let $x ?v (* ?body ?e))"),
        rw!("let-float-if-cond"; "(IfThen (Let $x ?v ?body) ?then ?else)" =>
            "(Let $x ?v (IfThen ?body ?then ?else))"),

        // Let inlining (if variable is used only once)
        rw!("let-conseq"; "(Let $x ?v1 (Let $y ?v2 ?body))" => "(Let $y ?v2 (Let $x ?v1 ?body))"),
    ]
}

// ============================================================================
// Option/Maybe monad transformations
// ============================================================================

fn option_rules() -> Vec<Rewrite<Lean, LeanAnalysis>> {
    vec![
        // Match on None
        rw!("match-none"; "(Match None (Case None ?none_body (Case (Some ?x) ?some_body MatchEnd)))" => "?none_body"),

        // Match on Some
        rw!("match-some"; "(Match (Some ?v) (Case None ?none_body (Case (Some ?x) ?some_body MatchEnd)))" =>
            "(Let $x ?v ?some_body)"),

        // Option map fusion
        rw!("option-map-fusion"; "(Match (Match ?opt (Case None None (Case (Some ?x) (Some ?f1) MatchEnd))) (Case None None (Case (Some ?y) (Some ?f2) MatchEnd)))" =>
            "(Match ?opt (Case None None (Case (Some ?x) (Some (Let $y ?f1 ?f2)) MatchEnd)))"),
    ]
}

// ============================================================================
// Aggregation function - Export all rules
// ============================================================================

pub fn all_rules() -> Vec<Rewrite<Lean, LeanAnalysis>> {
    let mut rules = Vec::new();
    rules.extend(arith_rules());
    rules.extend(comp_rules());
    rules.extend(bool_rules());
    rules.extend(prop_rules());
    rules.extend(control_flow_rules());
    rules.extend(lambda_rules());
    rules.extend(let_rules());
    rules.extend(option_rules());
    rules
}

// Export individual rule categories for fine-grained control
pub fn get_rules_by_category(category: &str) -> Vec<Rewrite<Lean, LeanAnalysis>> {
    match category {
        "arith" => arith_rules(),
        "comp" => comp_rules(),
        "bool" => bool_rules(),
        "prop" => prop_rules(),
        "control_flow" => control_flow_rules(),
        "lambda" => lambda_rules(),
        "let" => let_rules(),
        "option" => option_rules(),
        _ => vec![],
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use slotted_egraphs::*;

    fn test_rewrite(rules: Vec<Rewrite<Lean, LeanAnalysis>>, start: &str, expected: &str) {
        let start_expr: RecExpr<Lean> = RecExpr::parse(start).unwrap();
        let expected_expr: RecExpr<Lean> = RecExpr::parse(expected).unwrap();

        let mut egraph = EGraph::<Lean, LeanAnalysis>::new(LeanAnalysis);
        let start_id = egraph.add_syn_expr(start_expr.clone());

        let mut runner: Runner<Lean, LeanAnalysis> = Runner::new(LeanAnalysis)
            .with_egraph(egraph)
            .with_iter_limit(10)
            .with_node_limit(10000);
        runner.run(&rules);

        let mut egraph = runner.egraph;
        let expected_id = egraph.add_expr(expected_expr);
        // egraph.dump();

        assert_eq!(
            egraph.find_applied_id(&start_id),
            egraph.find_applied_id(&expected_id),
            "Failed to prove equivalence:\nStart: {}\nExpected: {}",
            start,
            expected
        );
    }

    // ========================================================================
    // Arithmetic Rules Tests
    // ========================================================================

    #[test]
    fn test_add_comm() {
        test_rewrite(arith_rules(), "(+ 1 2)", "(+ 2 1)");
    }

    #[test]
    fn test_mul_comm() {
        test_rewrite(arith_rules(), "(* x y)", "(* y x)");
    }

    #[test]
    fn test_add_assoc() {
        test_rewrite(arith_rules(), "(+ a (+ b c))", "(+ (+ a b) c)");
    }

    #[test]
    fn test_distributivity() {
        test_rewrite(arith_rules(), "(* a (+ b c))", "(+ (* a b) (* a c))");
    }

    #[test]
    fn test_distributivity_reverse() {
        test_rewrite(arith_rules(), "(+ (* x y) (* x z))", "(* x (+ y z))");
    }

    // ========================================================================
    // Comparison Rules Tests
    // ========================================================================

    #[test]
    fn test_eq_symm() {
        test_rewrite(comp_rules(), "(= a b)", "(= b a)");
    }

    #[test]
    fn test_lt_gt_duality() {
        test_rewrite(comp_rules(), "(< x y)", "(> y x)");
    }

    #[test]
    fn test_not_lt_to_ge() {
        test_rewrite(comp_rules(), "(not (< a b))", "(>= a b)");
    }

    #[test]
    fn test_lt_to_le_ne() {
        test_rewrite(comp_rules(), "(< x y)", "(and (<= x y) (!= x y))");
    }

    // ========================================================================
    // Boolean Logic Tests
    // ========================================================================

    #[test]
    fn test_and_comm() {
        test_rewrite(bool_rules(), "(& p q)", "(& q p)");
    }

    #[test]
    fn test_de_morgan_and() {
        test_rewrite(bool_rules(), "(not (& a b))", "(| (not a) (not b))");
    }

    #[test]
    fn test_de_morgan_or() {
        test_rewrite(bool_rules(), "(not (| a b))", "(& (not a) (not b))");
    }

    #[test]
    fn test_double_negation() {
        test_rewrite(bool_rules(), "(not (not p))", "p");
    }

    #[test]
    fn test_and_over_or_distributivity() {
        test_rewrite(bool_rules(), "(& a (| b c))", "(| (& a b) (& a c))");
    }

    #[test]
    fn test_absorption() {
        test_rewrite(bool_rules(), "(& a (| a b))", "a");
    }

    // ========================================================================
    // Propositional Logic Tests
    // ========================================================================

    #[test]
    fn test_impl_to_disj() {
        test_rewrite(prop_rules(), "(-> p q)", "(or (neg p) q)");
    }

    #[test]
    fn test_iff_to_conj() {
        test_rewrite(prop_rules(), "(<-> a b)", "(and (-> a b) (-> b a))");
    }

    #[test]
    fn test_contrapositive() {
        test_rewrite(prop_rules(), "(-> p q)", "(-> (neg q) (neg p))");
    }

    #[test]
    fn test_forall_exists_duality() {
        test_rewrite(
            prop_rules(),
            "(forall $x P)",
            "(neg (exists $x (neg P)))",
        );
    }

    #[test]
    fn test_exists_forall_duality() {
        test_rewrite(
            prop_rules(),
            "(exists $x P)",
            "(neg (forall $x (neg P)))",
        );
    }

    // ========================================================================
    // Control Flow Tests
    // ========================================================================

    #[test]
    fn test_if_swap_branches() {
        test_rewrite(
            control_flow_rules(),
            "(IfThen cond then_branch else_branch)",
            "(IfThen (not cond) else_branch then_branch)",
        );
    }

    #[test]
    fn test_if_true() {
        test_rewrite(control_flow_rules(), "(IfThen true x y)", "x");
    }

    #[test]
    fn test_if_false() {
        test_rewrite(control_flow_rules(), "(IfThen false x y)", "y");
    }

    #[test]
    fn test_if_same_branches() {
        test_rewrite(control_flow_rules(), "(IfThen cond result result)", "result");
    }

    // ========================================================================
    // Lambda Calculus Tests
    // ========================================================================

    #[test]
    fn test_beta_reduction() {
        test_rewrite(
            lambda_rules(),
            "(App (Fun $x (+ (Var $x) 1)) 5)",
            "(Let $x 5 (+ (Var $x) 1))",
        );
    }

    // ========================================================================
    // Let-binding Tests
    // ========================================================================

    #[test]
    fn test_let_float_add() {
        test_rewrite(
            let_rules(),
            "(+ (Let $x v body) e)",
            "(Let $x v (+ body e))",
        );
    }

    // ========================================================================
    // Option Tests
    // ========================================================================

    #[test]
    fn test_match_none() {
        test_rewrite(
            option_rules(),
            "(Match None (Case None result (Case (Some x) other MatchEnd)))",
            "result",
        );
    }

    #[test]
    fn test_match_some() {
        test_rewrite(
            option_rules(),
            "(Match (Some val) (Case None none_case (Case (Some x) some_case MatchEnd)))",
            "(Let $x val some_case)",
        );
    }

    // ========================================================================
    // Integration Tests - Multiple rules applied
    // ========================================================================

    #[test]
    fn test_complex_arith_simplification() {
        // (a + b) * c  ==>  a*c + b*c
        test_rewrite(
            arith_rules(),
            "(* (+ a b) c)",
            "(+ (* a c) (* b c))",
        );
    }

    #[test]
    fn test_complex_bool_simplification() {
        // !(a && b) ==> !a || !b
        let mut rules = bool_rules();
        rules.extend(prop_rules());
        test_rewrite(
            rules,
            "(not (& p q))",
            "(| (not p) (not q))",
        );
    }

    #[test]
    fn test_comparison_chain() {
        // < to > and back demonstrates equivalence
        test_rewrite(comp_rules(), "(< x y)", "(> y x)");
    }

    #[test]
    fn test_impl_chain() {
        // p -> q can be transformed to !q -> !p (contrapositive)
        test_rewrite(prop_rules(), "(-> a b)", "(-> (neg b) (neg a))");
    }
}