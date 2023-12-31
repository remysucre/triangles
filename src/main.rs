use indexmap::IndexMap;
use std::vec;

use egg::{rewrite as rw, *};
use std::collections::HashSet;

#[derive(Default, Clone)]
pub struct FvAnalysis;

type EGraph = egg::EGraph<LARA, FvAnalysis>;

#[derive(Debug)]
pub struct EScheduler {
    default_match_limit: usize,
    default_ban_length: usize,
    stats: IndexMap<Id, EStats>,
}

impl Default for EScheduler {
    fn default() -> Self {
        Self {
            stats: Default::default(),
            default_match_limit: 10,
            default_ban_length: 3,
        }
    }
}

impl EScheduler {
    pub fn with_initial_match_limit(mut self, limit: usize) -> Self {
        self.default_match_limit = limit;
        self
    }

    pub fn with_ban_length(mut self, ban_length: usize) -> Self {
        self.default_ban_length = ban_length;
        self
    }

    fn e_stats(&mut self, class: Id) -> &mut EStats {
        if self.stats.contains_key(&class) {
            &mut self.stats[&class]
        } else {
            self.stats.entry(class).or_insert(EStats {
                banned_until: 0,
                times_banned: 0,
                match_limit: self.default_match_limit,
                ban_length: self.default_ban_length,
            })
        }
    }
}

#[derive(Debug)]
struct EStats {
    banned_until: usize,
    times_banned: usize,
    match_limit: usize,
    ban_length: usize,
}

impl<L, N> RewriteScheduler<L, N> for EScheduler
where
    L: Language,
    N: Analysis<L>,
{
    fn can_stop(&mut self, iteration: usize) -> bool {
        // let n_stats = self.stats.len();

        let mut banned: Vec<_> = self
            .stats
            .iter_mut()
            .filter(|(_, s)| s.banned_until > iteration)
            .collect();

        if banned.is_empty() {
            true
        } else {
            let min_ban = banned
                .iter()
                .map(|(_, s)| s.banned_until)
                .min()
                .expect("banned cannot be empty here");

            assert!(min_ban >= iteration);
            let delta = min_ban - iteration;

            let mut unbanned = vec![];
            for (name, s) in &mut banned {
                s.banned_until -= delta;
                if s.banned_until == iteration {
                    unbanned.push(*name);
                }
            }

            assert!(!unbanned.is_empty());
            // info!(
            //     "Banned {}/{}, fast-forwarded by {} to unban {}",
            //     banned.len(),
            //     n_stats,
            //     delta,
            //     unbanned.join(", "),
            // );

            false
        }
    }

    fn search_rewrite<'a>(
        &mut self,
        iteration: usize,
        egraph: &egg::EGraph<L, N>,
        rewrite: &'a Rewrite<L, N>,
    ) -> Vec<SearchMatches<'a, L>> {
        let mut ms = rewrite.search(egraph);
        ms.retain(|m| {
            let stats = self.e_stats(m.eclass);
            if stats.banned_until > iteration {
                false
            } else {
                let threshold = stats.match_limit + 3 * stats.times_banned;
                // let threshold = stats.match_limit + stats.times_banned;
                let len: usize = egraph[m.eclass].len();
                if len > threshold {
                    let ban_length = stats.ban_length + 2 * stats.times_banned;
                    // let ban_length = stats.ban_length;
                    stats.times_banned += 1;
                    stats.banned_until = iteration + ban_length;
                    false
                } else {
                    true
                }
            }
        });
        ms
    }
}

// Metadata for each class
#[derive(Debug, PartialEq, Eq)]
pub struct Data {
    // Set of free variables by their class ID
    pub free: HashSet<Id>,
}

impl Analysis<LARA> for FvAnalysis {
    type Data = Data;

    fn merge(&mut self, to: &mut Data, from: Data) -> DidMerge {
        let before_len = to.free.len();
        // to.free.extend(from.free);
        to.free.retain(|i| from.free.contains(i));
        DidMerge(before_len != to.free.len(), true)
    }

    fn make(egraph: &EGraph, enode: &LARA) -> Data {
        let fvs = |i: &Id| egraph[*i].data.free.iter().copied();
        let mut free = HashSet::default();
        match enode {
            LARA::Var(v) => {
                free.insert(*v);
            }
            LARA::Let([v, a, b]) => {
                free.extend(fvs(b));
                // NOTE only do this if v free in b?
                free.remove(v);
                free.extend(fvs(a));
            }
            LARA::Sum([v, a]) => {
                free.extend(fvs(a));
                free.remove(v);
            }
            LARA::Other(_, xs) => {
                for x in xs {
                    free.extend(fvs(x));
                }
            }
            _ => enode.for_each(|c| free.extend(&egraph[c].data.free)),
        }

        Data { free }
    }

    fn modify(egraph: &mut egg::EGraph<LARA, Self>, id: Id) {
        if egraph[id].nodes.iter().any(|n| matches!(n, LARA::Num(0))) {
            egraph[id].nodes.retain(|n| matches!(n, LARA::Num(0)));
        }
    }
}

define_language! {
    pub enum LARA {
        Num(i32),

        "m*" = MMul([Id; 2]),
        ".*" = PMul([Id; 2]), // pointwise mult
        "m+" = MAdd([Id; 2]),
        "m/" = MDiv([Id; 2]),

        "tr" = Trace(Id),
        "msum" = MSum(Id), // sum up all entries in matrix

        "mat" = Mat(Id),

        "var" = Var(Id),

        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),

        "=" = Eq([Id; 2]),
        "<" = Lt([Id; 2]),
        ">" = Gt([Id; 2]),

        // Indicator
        "I" = I(Id),

        "sum" = Sum([Id; 2]),
        "let" = Let([Id; 3]),

        Symbol(egg::Symbol),
        Other(Symbol, Vec<Id>),
    }
}

fn var(s: &str) -> Var {
    s.parse().unwrap()
}

fn both(
    f: impl Fn(&mut EGraph, Id, &Subst) -> bool,
    g: impl Fn(&mut EGraph, Id, &Subst) -> bool,
) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, id, subst| f(egraph, id, subst) && g(egraph, id, subst)
}

fn is_not_same_var(v1: Var, v2: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| egraph.find(subst[v1]) != egraph.find(subst[v2])
}

fn free(x: Var, b: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    move |egraph, _, subst| egraph[subst[b]].data.free.contains(&subst[x])
}

fn not_free(x: Var, b: Var) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let f = free(x, b);
    move |egraph, id, subst| !f(egraph, id, subst)
}

// Rename summation variable and push down sum
pub struct RenameSum {
    fresh: Var,
    e: Pattern<LARA>,
}

impl Applier<LARA, FvAnalysis> for RenameSum {
    fn apply_one(
        &self,
        egraph: &mut EGraph,
        eclass: Id,
        subst: &Subst,
        searcher_ast: Option<&PatternAst<LARA>>,
        rule_name: Symbol,
    ) -> Vec<Id> {
        let mut subst = subst.clone();
        let sym = egraph.add(LARA::Symbol(format!("_{}", eclass).into()));
        subst.insert(self.fresh, sym);
        self.e
            .apply_one(egraph, eclass, &subst, searcher_ast, rule_name)
    }
}

pub fn rules() -> Vec<Rewrite<LARA, FvAnalysis>> {
    // semiring axioms
    let mut rls = vec![
        rw!("assoc-add";   "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
        rw!("assoc-add-r"; "(+ (+ ?a ?b) ?c)" => "(+ ?a (+ ?b ?c))"),
        rw!("assoc-mul";   "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),
        rw!("assoc-mul-r"; "(* (* ?a ?b) ?c)" => "(* ?a (* ?b ?c))"),
        rw!("comm-add";  "(+ ?a ?b)" => "(+ ?b ?a)"),
        rw!("comm-mul";  "(* ?a ?b)" => "(* ?b ?a)"),
        rw!("zero-add"; "(+ ?a 0)" => "?a"),
        rw!("zero-mul"; "(* ?a 0)" => "0"),
        rw!("one-mul";  "(* ?a 1)" => "?a"),
        rw!("add-zero"; "?a" => "(+ ?a 0)"),
        rw!("mul-one";  "?a" => "(* ?a 1)"),
        rw!("distribute"; "(* ?a (+ ?b ?c))" => "(+ (* ?a ?b) (* ?a ?c))"),
        rw!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
    ];

    // let rules
    rls.extend(vec![
        rw!("let-const"; "(let ?v ?e ?c)" => "?c" if not_free(var("?v"), var("?c"))),
        rw!("let-var-same"; "(let ?v ?e (var ?v))" => "?e"),
        rw!("let-var-diff"; "(let ?v1 ?e (var ?v2))" => "(var ?v2)"
            if is_not_same_var(var("?v1"), var("?v2"))),
        rw!("let-sum-same"; "(let ?v1 ?e (sum ?v1 ?body))" => "(sum ?v1 ?body)"),
        rw!("let-sum-diff-free";
            "(let ?v1 ?e (sum ?v2 ?body))" =>
            { RenameSum {
                fresh: var("?fresh"),
                e: "(sum ?fresh (let ?v1 ?e (let ?v2 ?fresh ?body)))".parse().unwrap()
            }}
            if both(is_not_same_var(var("?v1"), var("?v2")), free(var("?v2"), var("?e")))
        ),
        rw!("let-sum-diff-bound";
            "(let ?v1 ?e (sum ?v2 ?body))" => "(sum ?v2 (let ?v1 ?e ?body))"
            if both(is_not_same_var(var("?v1"), var("?v2")), not_free(var("?v2"), var("?e")))
        ),
        rw!("let-add";    "(let ?v ?e (+ ?a ?b))" => "(+ (let ?v ?e ?a) (let ?v ?e ?b))"),
        rw!("let-add-r";  "(+ (let ?v ?e ?a) (let ?v ?e ?b))" => "(let ?v ?e (+ ?a ?b))"),
        rw!("let-mul";    "(let ?v ?e (* ?a ?b))" => "(* (let ?v ?e ?a) (let ?v ?e ?b))"),
        rw!("let-mul-r";  "(* (let ?v ?e ?a) (let ?v ?e ?b))" => "(let ?v ?e (* ?a ?b))"),
        rw!("let-eq";     "(let ?v ?e (= ?a ?b))" => "(= (let ?v ?e ?a) (let ?v ?e ?b))"),
        rw!("let-eq-r";   "(= (let ?v ?e ?a) (let ?v ?e ?b))" => "(let ?v ?e (= ?a ?b))"),
        // HACK
        rw!("let-rel"; "(let ?x ?e (A ?i ?j))" => "(A (let ?x ?e ?i) (let ?x ?e ?j))"),
    ]);

    // summation axioms
    rls.extend(vec![
        rw!("elim-sum-ind"; "(sum ?j (* (I (= (var ?j) ?k)) ?e))" => "(let ?j ?k ?e)"),
        rw!("sum-distr-add";   "(sum ?t (+ ?a ?b))" => "(+ (sum ?t ?a) (sum ?t ?b))"),
        rw!("sum-distr-add-r"; "(+ (sum ?t ?a) (sum ?t ?b))" => "(sum ?t (+ ?a ?b))"),
        rw!("sum-swap"; "(sum ?s (sum ?t ?a))" => "(sum ?t (sum ?s ?a))"),
        rw!("sum-distr-mul-bound";   "(* ?b (sum ?x ?a))" => "(sum ?x (* ?b ?a))"
                if not_free(var("?x"), var("?b"))),
        rw!("sum-distr-mul-bound-r"; "(sum ?x (* ?b ?a))" => "(* ?b (sum ?x ?a))"
                if not_free(var("?x"), var("?b"))),
        rw!("sum-distr-mul-free";
            "(* ?b (sum ?x ?a))" =>
            { RenameSum {
                fresh: var("?fresh"),
                e: "(sum ?fresh (* ?b (let ?x ?fresh ?a)))".parse().unwrap()
            }}
            if free(var("?x"), var("?b"))),
    ]);

    // conditional axioms
    rls.extend(vec![
        rw!("eq-comm"; "(= ?x ?y)" => "(= ?y ?x)"),
        rw!("let-cond"; "(let ?x ?e (I ?c))" => "(I (let ?x ?e ?c))"),
        // HACK
        rw!("conditions"; "(A (var ?i) (var ?j))" => "(* (A (var ?i) (var ?j)) (+ (I (< (var ?i) (var ?j))) (+ (I (> (var ?i) (var ?j))) (I (= (var ?i) (var ?j))))))"), 
        rw!("comparison"; "(< ?vi ?vj)" => "(> ?vj ?vi)"),
        rw!("comparison-r"; "(> ?vi ?vj)" => "(< ?vj ?vi)"),
    ]);

    rls.extend(vec![
        rw!("no-self-loop"; "(* (I (= (var ?i) (var ?j))) (A (var ?i) (var ?j)))" => "0"),
        rw!("symmetry-sum-l"; "(sum i (sum j (* ?e (* (A (var ?i) (var ?j)) (I (< (var ?i) (var ?j)))))))" => "(sum i (sum j (* ?e (* (A (var ?i) (var ?j)) (I (> (var ?i) (var ?j)))))))"),
        rw!("symmetry-sum-r"; "(sum i (sum j (* ?e (* (A (var ?i) (var ?j)) (I (> (var ?i) (var ?j)))))))" => "(sum i (sum j (* ?e (* (A (var ?i) (var ?j)) (I (< (var ?i) (var ?j)))))))"),
        rw!("symmetry"; "(A (var ?i) (var ?j))" => "(A (var ?j) (var ?i))"),
        rw!("conflict"; "(* (I (< (var ?i) (var ?j))) (I (> (var ?i) (var ?j))))" => "0"),
        rw!("order"; "(* (I (< (var ?i) (var ?j))) (I (< (var ?j) (var ?k))))" => "(* (* (I (< (var ?i) (var ?j))) (I (< (var ?j) (var ?k)))) (I (< (var ?i) (var ?k))))"),
        rw!("id"; "(* (I ?c) (I ?c))" => "(I ?c)"),
        rw!("sum-0"; "(sum ?i 0)" => "0"),
        rw!("fold"; "(/ (+ (+ ?a (+ ?a ?a)) (+ ?a (+ ?a ?a))) 6)" => "?a"),
    ]);

    rls
}

fn main() {
    let e0: RecExpr<LARA> =
        "(/ (sum i (sum l (* (I (= (var i) (var l))) (sum k (* (sum j (* (A (var i) (var j)) (A (var j) (var k)))) (A (var k) (var l))))))) 6)"
            .parse()
            .unwrap();

    let e1: RecExpr<LARA> = "(/ (sum i (sum k (* (sum j (* (A (var i) (var j)) (A (var j) (var k)))) (A (var k) (var i))))) 6)"
        .parse()
        .unwrap();

    let e2: RecExpr<LARA> =
        "(/ (sum i (sum j (sum k (* (* (A (var i) (var j)) (+ (I (< (var i) (var j))) (+ (I (> (var i) (var j))) (I (= (var i) (var j)))))) (* (* (A (var j) (var k)) (+ (I (< (var j) (var k))) (+ (I (> (var j) (var k))) (I (= (var j) (var k)))))) (* (A (var k) (var i)) (+ (I (< (var k) (var i))) (+ (I (> (var k) (var i))) (I (= (var k) (var i))))))))))) 6)"
            .parse()
            .unwrap();

    let e3: RecExpr<LARA> =
        "(/ (sum i (sum j (sum k (+ (* (* (* (A (var j) (var k)) (+ (I (> (var j) (var k))) (I (< (var j) (var k))))) (* (A (var k) (var i)) (+ (I (> (var k) (var i))) (I (< (var k) (var i)))))) (* (A (var i) (var j)) (I (< (var i) (var j))))) (* (* (* (A (var j) (var k)) (+ (I (> (var j) (var k))) (I (< (var j) (var k))))) (* (A (var k) (var i)) (+ (I (> (var k) (var i))) (I (< (var k) (var i)))))) (* (A (var i) (var j)) (I (> (var i) (var j))))))))) 6)"
            .parse()
            .unwrap();

    let e4: RecExpr<LARA> =
        "(/ (+ (+ (+ (sum i (sum j (sum k (* (* (A (var i) (var j)) (* (A (var j) (var k)) (A (var k) (var i)))) (* (I (> (var j) (var k))) (* (I (> (var k) (var i))) (I (> (var i) (var j))))))))) (sum i (sum j (sum k (* (* (A (var i) (var j)) (* (A (var j) (var k)) (A (var k) (var i)))) (* (I (> (var j) (var k))) (* (I (> (var k) (var i))) (I (< (var i) (var j)))))))))) (+ (sum i (sum j (sum k (* (* (A (var i) (var j)) (* (A (var j) (var k)) (A (var k) (var i)))) (* (I (> (var j) (var k))) (* (I (< (var k) (var i))) (I (> (var i) (var j))))))))) (sum i (sum j (sum k (* (* (A (var i) (var j)) (* (A (var j) (var k)) (A (var k) (var i)))) (* (I (> (var j) (var k))) (* (I (< (var k) (var i))) (I (< (var i) (var j))))))))))) (+ (+ (sum i (sum j (sum k (* (* (A (var i) (var j)) (* (A (var j) (var k)) (A (var k) (var i)))) (* (I (< (var j) (var k))) (* (I (> (var k) (var i))) (I (> (var i) (var j))))))))) (sum i (sum j (sum k (* (* (A (var i) (var j)) (* (A (var j) (var k)) (A (var k) (var i)))) (* (I (< (var j) (var k))) (* (I (> (var k) (var i))) (I (< (var i) (var j)))))))))) (+ (sum i (sum j (sum k (* (* (A (var i) (var j)) (* (A (var j) (var k)) (A (var k) (var i)))) (* (I (< (var j) (var k))) (* (I (< (var k) (var i))) (I (> (var i) (var j))))))))) (sum i (sum j (sum k (* (* (A (var i) (var j)) (* (A (var j) (var k)) (A (var k) (var i)))) (* (I (< (var j) (var k))) (* (I (< (var k) (var i))) (I (< (var i) (var j)))))))))))) 6)"
            .parse()
            .unwrap();

    let e5: RecExpr<LARA> = "(/ (+ (+ (sum i (sum j (sum k (* (* (I (< (var i) (var j))) (* (I (< (var j) (var k))) (I (< (var i) (var k))))) (* (* (A (var i) (var j)) (A (var j) (var k))) (A (var i) (var k))))))) (+ (sum i (sum k (sum j (* (* (I (< (var i) (var k))) (* (I (< (var k) (var j))) (I (< (var i) (var j))))) (* (* (A (var i) (var j)) (A (var j) (var k))) (A (var i) (var k))))))) (sum j (sum i (sum k (* (* (I (< (var j) (var i))) (* (I (< (var i) (var k))) (I (< (var j) (var k))))) (* (* (A (var i) (var j)) (A (var j) (var k))) (A (var i) (var k))))))))) (+ (sum j (sum k (sum i (* (* (I (< (var j) (var k))) (* (I (< (var k) (var i))) (I (< (var j) (var i))))) (* (* (A (var i) (var j)) (A (var j) (var k))) (A (var i) (var k))))))) (+ (sum k (sum i (sum j (* (* (I (< (var k) (var i))) (* (I (< (var i) (var j))) (I (< (var k) (var j))))) (* (* (A (var i) (var j)) (A (var j) (var k))) (A (var i) (var k))))))) (sum k (sum j (sum i (* (* (I (< (var k) (var j))) (* (I (< (var j) (var i))) (I (< (var k) (var i))))) (* (* (A (var i) (var j)) (A (var j) (var k))) (A (var i) (var k)))))))))) 6)"
            .parse()
            .unwrap();

    let e5a: RecExpr<LARA> = "(/ (+ (+ (sum i (sum j (sum k (* (* (I (< (var i) (var j))) (* (I (< (var j) (var k))) (I (< (var i) (var k))))) (* (* (A (var i) (var j)) (A (var j) (var k))) (A (var i) (var k))))))) (+ (sum i (sum j (sum k (* (* (I (< (var i) (var j))) (* (I (< (var j) (var k))) (I (< (var i) (var k))))) (* (* (A (var i) (var j)) (A (var j) (var k))) (A (var i) (var k))))))) (sum i (sum j (sum k (* (* (I (< (var i) (var j))) (* (I (< (var j) (var k))) (I (< (var i) (var k))))) (* (* (A (var i) (var j)) (A (var j) (var k))) (A (var i) (var k))))))))) (+ (sum i (sum j (sum k (* (* (I (< (var i) (var j))) (* (I (< (var j) (var k))) (I (< (var i) (var k))))) (* (* (A (var i) (var j)) (A (var j) (var k))) (A (var i) (var k))))))) (+ (sum i (sum j (sum k (* (* (I (< (var i) (var j))) (* (I (< (var j) (var k))) (I (< (var i) (var k))))) (* (* (A (var i) (var j)) (A (var j) (var k))) (A (var i) (var k))))))) (sum i (sum j (sum k (* (* (I (< (var i) (var j))) (* (I (< (var j) (var k))) (I (< (var i) (var k))))) (* (* (A (var i) (var j)) (A (var j) (var k))) (A (var i) (var k)))))))))) 6)"
            .parse()
            .unwrap();

    let e5b: RecExpr<LARA> = "(sum i (sum j (sum k (* (* (I (< (var i) (var j))) (* (I (< (var j) (var k))) (I (< (var i) (var k))))) (* (* (A (var i) (var j)) (A (var j) (var k))) (A (var i) (var k)))))))"
            .parse()
            .unwrap();

    let e6: RecExpr<LARA> = "(sum i (sum j (sum k (* (* (I (< (var i) (var j))) (* (I (< (var j) (var k))) (I (< (var i) (var k))))) (* (* (A (var i) (var j)) (A (var j) (var k))) (A (var i) (var k)))))))"
            .parse()
            .unwrap();

    let e7: RecExpr<LARA> = "(sum i (sum k (* (* (A (var i) (var k)) (I (< (var i) (var k)))) (sum j (* (A (var i) (var j)) (* (I (< (var i) (var j))) (* (A (var j) (var k)) (I (> (var j) (var k))))))))))"
            .parse()
            .unwrap();

    let runner = Runner::default()
        .with_expr(&e0)
        .with_expr(&e1)
        .with_expr(&e2)
        .with_expr(&e3)
        .with_expr(&e4)
        .with_expr(&e5)
        .with_expr(&e5a)
        .with_expr(&e5b)
        .with_expr(&e6)
        .with_expr(&e7)
        // .with_scheduler(SimpleScheduler)
        .with_scheduler(EScheduler::default())
        .with_node_limit(5000000)
        .with_time_limit(std::time::Duration::new(20, 0))
        // .with_iter_limit(500)
        .run(&rules());

    // dbg!(runner.egraph.equivs(&e0, &e1));
    // dbg!(runner.egraph.equivs(&e1, &e2));
    // dbg!(runner.egraph.equivs(&e2, &e3));
    // dbg!(runner.egraph.equivs(&e3, &e4));
    // dbg!(runner.egraph.equivs(&e4, &e5));
    // dbg!(runner.egraph.equivs(&e5, &e6));
    // dbg!(runner.egraph.equivs(&e6, &e7));

    dbg!(runner.egraph.equivs(&e0, &e7));

    dbg!(runner.stop_reason);

    dbg!(runner.egraph.number_of_classes());
    dbg!(runner.egraph.total_number_of_nodes());
    dbg!(runner.egraph.classes().map(|c| c.nodes.len()).max());
}
