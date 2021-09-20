//! Constant Propagation based Argument Reduction

/// Argument Reduction by propagating consistent constants on the pure-rhs clauses.
///
/// An argument of some predicate is propagatable if
/// 1. (implication invariant condition)Expressions appears on the same positions are invariant on implication clauses(a predicate application appears on both sides of clause).
/// 2. (rhs constant condition)It is a consistent constant on all of pure-rhs clauses(a predicate application appears on only rhs of clause).
/// # Examples
///
/// ```rust
/// // See this file for a example.
/// ::std::fs::OpenOptions::new().read(true).open("rsc/sat/const_prop.smt2").unwrap();
/// ```
/// # TODO
/// - check the soundness
/// - check the dependencies between other preprocess methods
use crate::{
    common::*,
    preproc::{PreInstance, RedStrat},
};

pub struct ConstProp {
    /// Predicate arguments to keep.
    keep: PrdMap<VarSet>,
    /// Propagated constant terms for each predicates
    const_terms: PrdMap<VarMap<TermSet>>,
}

impl RedStrat for ConstProp {
    fn name(&self) -> &'static str {
        "const_prop"
    }
    fn new(_instance: &Instance) -> Self {
        ConstProp {
            const_terms: PrdMap::new(),
            keep: PrdMap::new(),
        }
    }

    // TODO: add constant constraints to model
    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        let (const_conditions, to_keep) = self.run(instance);
        // eprintln!("to_keep = \n{:#?}", to_keep);
        // add constant conditions to corresponding clauses
        for (cls_idx, cst_conds) in const_conditions {
            for cond in cst_conds {
                instance[cls_idx].insert_term(cond);
            }
        }
        for (pred, cnst_term_map) in self.const_terms.index_iter() {
            for (var, cnst_terms) in cnst_term_map.index_iter() {
                // TODO: more elaborate condition
                if cnst_terms.len() == 0
                    || (to_keep.contains_key(&pred) && to_keep[&pred].contains(&var))
                {
                    continue;
                }

                // get original varidx
                let original_var = instance[pred].original_sig_map()[var];
                // current implimentation guarantees cnst_terms' length is 1
                debug_assert!(
                    cnst_terms.len() == 1,
                    "pred{} var{} const_terms{:#?}",
                    pred,
                    var,
                    cnst_terms
                );
                for cnst in cnst_terms {
                    instance[pred].add_const_condition(original_var, cnst.clone());
                }
            }
        }

        // to avoid trivial clauses on check in rm_args
        let mut info = instance.simplify_all()?;

        info += instance.rm_args(to_keep)?;

        // for clause in instance.clauses() {
        //     eprintln!("{}", clause.to_string_info(&instance.preds()).unwrap());
        // }

        Ok(info)
    }
}
impl ConstProp {
    /// Initializes itself from an instance.
    fn init(&mut self, instance: &Instance) {
        self.const_terms.clear();
        self.keep.clear();

        // Empty constant set for each predicate.
        for (_pred_idx, p) in instance.preds().index_iter() {
            self.keep.push(VarSet::new());
            let mut v = VarMap::new();
            for _ in 0..p.sig.len() {
                v.push(TermSet::new());
            }
            self.const_terms.push(v);
        }
    }

    /// Checks if implication invariant condition for a predicate.
    ///
    /// Returns `true` if some argument satisfies the condition
    fn implication_invariant_condition(&mut self, instance: &Instance, pred: PrdIdx) -> bool {
        let (lhs_clauses, rhs_clauses) = instance.clauses_of(pred);
        let implication_clauses: HashSet<&ClsIdx> =
            lhs_clauses.intersection(&rhs_clauses).collect();

        for &cls_idx in implication_clauses {
            let leftargss = &instance[cls_idx].lhs_preds()[&pred];
            let (p, rightargs) = instance[cls_idx]
                .rhs()
                .expect(&format!("{}-clause rhs is broken", cls_idx));
            debug_assert!(p == pred);
            'all_arg: for (rightvaridx, rightarg) in rightargs.index_iter() {
                for leftargs in leftargss {
                    if leftargs[rightvaridx] != *rightarg {
                        self.keep[pred].insert(rightvaridx);
                        continue 'all_arg;
                    }
                }
            }
        }
        self.keep[pred].len() < instance[pred].sig.len()
    }

    /// Checks if rhs constant condition for a predicate.
    ///
    /// Returns `true` if some argument satisfies the condition
    fn rhs_constant_condition(&mut self, instance: &Instance, pred: PrdIdx) -> bool {
        let (lhs_clauses, rhs_clauses) = instance.clauses_of(pred);
        let pure_rhs_clauses: HashSet<&ClsIdx> = rhs_clauses.difference(&lhs_clauses).collect();
        // there are no appearance of this pred on pure rhs
        if pure_rhs_clauses.len() == 0 {
            for (var, _ty) in instance[pred].sig.index_iter() {
                self.keep[pred].insert(var);
            }
        } else {
            for &cls_idx in pure_rhs_clauses {
                let (_p, rightargs) = instance[cls_idx]
                    .rhs()
                    .expect(&format!("{}-clause rhs is broken", cls_idx));
                for (var, arg) in rightargs.index_iter() {
                    if self.keep[pred].contains(&var) {
                        continue;
                    }
                    // TODO: confirm RTerm::val(self).is_some() is equivalent to be constant
                    match arg.val() {
                        Some(_cstval) => {
                            self.const_terms[pred][var].insert(arg.clone());
                        }
                        None => {
                            self.keep[pred].insert(var);
                        }
                    }
                    // ignore the case constants are more than two kinds.
                    if 2 <= self.const_terms[pred][var].len() {
                        self.keep[pred].insert(var);
                        self.const_terms[pred][var].clear();
                    }
                }
            }
        }

        self.keep[pred].len() < instance[pred].sig.len()
    }

    fn generate_constant_conditions(
        &mut self,
        instance: &Instance,
        pred: PrdIdx,
    ) -> ClsHMap<TermSet> {
        let mut const_conditions = ClsHMap::<TermSet>::new();
        for (var_idx, _typ) in instance[pred].sig.index_iter() {
            // this aregument is not propable
            if self.keep[pred].contains(&var_idx) {
                continue;
            }

            // create constant conditions to add
            for &cls_idx in instance.lhs_clauses_of(pred) {
                let leftargss = &instance[cls_idx].lhs_preds()[&pred];
                let mut cst_conds = TermSet::new();

                for leftargs in leftargss {
                    debug_assert!(self.const_terms[pred][var_idx].len() == 1);
                    for cst in &self.const_terms[pred][var_idx] {
                        cst_conds.insert(term::eq(leftargs[var_idx].clone(), cst.clone()));
                    }
                }
                const_conditions.insert(cls_idx, cst_conds);
            }
        }
        const_conditions
    }
    /// Runs itself on all clauses of an instance.
    /// 1. check arguments are constant propagatable or not, per predicates
    ///    if it's propable, collect const_terms and left clauses' arguments
    /// 2. create constant constraints of for each clauses
    fn run(&mut self, instance: &Instance) -> (ClsHMap<TermSet>, PrdHMap<VarSet>) {
        self.init(&instance);
        // arguments' constant conditions to add pure lhs clauses
        let mut const_conditions = ClsHMap::<TermSet>::new();
        for (pred_idx, _pred) in instance.preds().index_iter() {
            // 1. check if arguments are constant propagatable, per predicate
            if self.implication_invariant_condition(instance, pred_idx)
                && self.rhs_constant_condition(instance, pred_idx)
            {
                const_conditions.extend(self.generate_constant_conditions(instance, pred_idx));
            }
        }
        let mut res = PrdHMap::new();
        for (pred, vars) in ::std::mem::replace(&mut self.keep, PrdMap::new()).into_index_iter() {
            if !instance[pred].is_defined() {
                // eprintln!("{:#?} id not defined", pred);
                let prev = res.insert(pred, vars);
                debug_assert! { prev.is_none() }
            }
        }
        (const_conditions, res)
    }
}
