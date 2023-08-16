use std::vec;

use egg::*;

define_language! {
    pub enum RA {
        Num(i32),

        "atom" = Atom([Id; 3]),
        "mat" = Mat(Id),
        "idx" = Idx(Id),

        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),

        "=" = Eq([Id; 2]),
        "<" = Lt([Id; 2]),
        ">" = Gt([Id; 2]),

        // Indicator
        "I" = I(Id),

        "sum" = Sum(Id),
        "let" = Let([Id; 3]),

        Symbol(egg::Symbol),
    }
}

fn axioms() -> Vec<Rewrite<RA, ()>> {
    let mut rules = vec![
        rewrite!("commute-add"; "(+ ?a ?b)" <=> "(+ ?b ?a)"),
        rewrite!("commute-mul"; "(* ?a ?b)" <=> "(* ?b ?a)"),
        rewrite!("assoc-add"; "(+ ?a (+ ?b ?c))" <=> "(+ (+ ?a ?b) ?c)"),
        rewrite!("assoc-mul"; "(* ?a (* ?b ?c))" <=> "(* (* ?a ?b) ?c)"),
        rewrite!("mul-distr-add"; "(+ (* ?a ?b) (?a ?c))" <=> "(* ?a (+ ?b ?c))"),
        rewrite!("sum-distr-add"; "(sum ?x (+ ?a ?b))" <=> "(+ (sum ?x ?a) (sum ?x ?b))"),
    ]
    .concat();

    rules.append(&mut vec![
        rewrite!("mul-0"; "(* ?a 0)" => "0"),
        rewrite!("let-mul"; "(let ?x ?y (* ?a ?b))" => "(* (let ?x ?y ?a) (let ?x ?y ?b))"),
        rewrite!("let-add"; "(let ?x ?y (+ ?a ?b))" => "(+ (let ?x ?y ?a) (let ?x ?y ?b))"),
    ]);

    rules
}

fn main() {}
