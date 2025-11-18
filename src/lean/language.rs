use slotted_egraphs::*;

define_language! {
    pub enum Lean {
        // Function defs
        // (def <name> <ret type> <arg | body>)
        FunDef(AppliedId, AppliedId, AppliedId) = "Def",
        // (arg <type> <arg> <body | args>)
        FunArg(AppliedId, Bind<AppliedId>) = "Arg",
        // (Begin <body>)
        FunBody(AppliedId) = "Begin",
        // E.g., a max function can be written as:
        // (Def max Nat (Arg Nat $x (Arg Nat $y (Begin (IfThen (> (Var $x) (Var $y) (Var $x) (Var $y)))))))

        // Lambdas
        Lam(Bind<AppliedId>) = "Fun",
        App(AppliedId, AppliedId) = "App",
        Var(Slot) = "Var",
        
        // let name := value
        // body
        Let(Bind<AppliedId>, AppliedId) = "Let",

        // Pattern Matching
        Match(AppliedId, AppliedId) = "Match",
        // `case PAT BODY NEXT`
        Case(AppliedId, AppliedId, AppliedId) = "Case",
        MatchEnd() = "MatchEnd",
        IfThenElse(AppliedId, AppliedId, AppliedId) = "IfThen",

        // List
        Nil() = "Nil",
        Cons(AppliedId, AppliedId) = "Cons",
        Length(AppliedId) = "Length",
        Fold(AppliedId, AppliedId, AppliedId) = "Fold",

        // Trees
        Leaf(AppliedId) = "Leaf",
        Node(AppliedId, AppliedId, AppliedId) = "Node",

        // Options
        None() = "None",
        Some(AppliedId) = "Some",

        // Arith
        Add(AppliedId, AppliedId) = "+",
        Sub(AppliedId, AppliedId) = "-",
        Mul(AppliedId, AppliedId) = "*",
        Div(AppliedId, AppliedId) = "/",
        Mod(AppliedId, AppliedId) = "%",
        
        // Comp
        Eq(AppliedId, AppliedId) = "=",
        Ne(AppliedId, AppliedId) = "!=",
        Lt(AppliedId, AppliedId) = "<",
        Le(AppliedId, AppliedId) = "<=",
        Gt(AppliedId, AppliedId) = ">",
        Ge(AppliedId, AppliedId) = ">=",

        // BoolOps
        And(AppliedId, AppliedId) = "&",
        Or(AppliedId, AppliedId) = "|",
        Not(AppliedId) = "not",

        // PropOps
        Implies(AppliedId, AppliedId) = "->",
        Iff(AppliedId, AppliedId) = "<->",
        Conj(AppliedId, AppliedId) = "and",
        Disj(AppliedId, AppliedId) = "or",
        Neg(AppliedId) = "neg",
        Forall(Bind<AppliedId>) = "forall",
        Exists(Bind<AppliedId>) = "exists",

        Bool(bool),
        Nat(u64),
        Symbol(Symbol),
    }
}

// A dummy analysis for now: we only want to run eqsat on function defs
pub struct LeanAnalysis;

impl Analysis<Lean> for LeanAnalysis {
    type Data = ();

    fn make(_eg: &EGraph<Lean, Self>, _enode: &Lean) -> Self::Data {}

    fn merge(_l: Self::Data, _r: Self::Data) -> Self::Data {}
}

#[cfg(test)]
mod tests {

    #[test]
    fn test_parsing() {
        use super::*;
        let calculate_totoal_crops: RecExpr<Lean> =
        RecExpr::parse("(Match xs
            (Case Nil Nil
                (Case (Cons h t)
                      (Cons (App sum_list_cost h) (App map_sum_code t))
                MatchEnd))
        )").unwrap();
        let mut egraph = EGraph::<Lean, LeanAnalysis>::new(LeanAnalysis {});
        egraph.add_syn_expr(calculate_totoal_crops);
    }
}