//! Argument reduction.

use crate::{
    common::*,
    preproc::{PreInstance, RedStrat},
};

/// Argument reduction.
///
/// Applies the technique from
/// [Redundant argument filtering of logic programs][paper].
///
/// [paper]: https://link.springer.com/chapter/10.1007%2F3-540-62718-9_6
/// (Redundant argument filtering of logic programs)
///
/// # Examples
///
/// ```rust
/// // See this file for a non-trivial example.
/// ::std::fs::OpenOptions::new().read(true).open("rsc/sat/arg_red.smt2").unwrap();
/// ```
pub struct ArgRed {
    inner: ArgReductor,
    inner2: ArgReductor2,
}

impl RedStrat for ArgRed {
    fn name(&self) -> &'static str {
        "arg_reduce"
    }

    fn new(_: &Instance) -> Self {
        ArgRed {
            inner: ArgReductor::new(),
            inner2: ArgReductor2::new(),
        }
    }

    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        let mut res = RedInfo::new();
        let keep = self.inner.run(instance);
        let mut w = std::io::stdout();
        println!("clauses_before_RAF {{");
        for (_, cls) in instance.clauses().index_iter() {
            write!(w, "(assert (forall (")?;
            let mut inactive = 0;
            for var in &cls.vars {
                if var.active {
                    write!(w, " (")?;
                    var.idx.default_write(&mut w)?;
                    write!(w, " {})", var.typ)?;
                } else {
                    inactive += 1;
                }
            }
            if inactive == cls.vars.len() {
                write!(w, " (unused Bool)")?;
            } 
            write!(w, " ) ")?;
            cls.expr_to_smt2(&mut w, &(true, &PrdSet::new(), &PrdSet::new(), instance.preds()))?;
            writeln!(w, "))")?;
        }
        println!("}}");
        res += instance.rm_args(keep)?;
        println!("clauses_before_FAR {{");
        for (_, cls) in instance.clauses().index_iter() {
            write!(w, "(assert (forall (")?;
            let mut inactive = 0;
            for var in &cls.vars {
                if var.active {
                    write!(w, " (")?;
                    var.idx.default_write(&mut w)?;
                    write!(w, " {})", var.typ)?;
                } else {
                    inactive += 1;
                }
            }
            if inactive == cls.vars.len() {
                write!(w, " (unused Bool)")?;
            } 
            write!(w, " ) ")?;
            cls.expr_to_smt2(&mut w, &(true, &PrdSet::new(), &PrdSet::new(), instance.preds()))?;
            writeln!(w, "))")?;
        }
        println!("}}");
        let keep = self.inner2.run(instance);
        res += instance.rm_args(keep)?;
        println!("clauses_after_FAR {{");
        for (_, cls) in instance.clauses().index_iter() {
            write!(w, "(assert (forall (")?;
            let mut inactive = 0;
            for var in &cls.vars {
                if var.active {
                    write!(w, " (")?;
                    var.idx.default_write(&mut w)?;
                    write!(w, " {})", var.typ)?;
                } else {
                    inactive += 1;
                }
            }
            if inactive == cls.vars.len() {
                write!(w, " (unused Bool)")?;
            } 
            write!(w, " ) ")?;
            cls.expr_to_smt2(&mut w, &(true, &PrdSet::new(), &PrdSet::new(), instance.preds()))?;
            writeln!(w, "))")?;
        }
        println!("}}");
        Ok(res)
    }
}

/// Argument reduction context.
pub struct ArgReductor {
    /// Predicate arguments to keep.
    keep: PrdMap<VarSet>,
    /// Map from clauses to the variables appearing in their lhs.
    lhs_vars: ClsMap<VarHMap<usize>>,
    /// Map from clauses to the varibales appearing in their rhs.
    rhs_vars: ClsMap<Option<(PrdIdx, VarMap<VarSet>)>>,
}
impl Default for ArgReductor {
    fn default() -> Self {
        Self::new()
    }
}
impl ArgReductor {
    /// Constructor.
    pub fn new() -> Self {
        ArgReductor {
            keep: PrdMap::new(),
            lhs_vars: ClsMap::new(),
            rhs_vars: ClsMap::new(),
        }
    }

    /// Prints itself.
    #[allow(dead_code)]
    fn print(&mut self, instance: &Instance) {
        println!("keep {{");
        for (pred, vars) in self.keep.index_iter() {
            if instance[pred].is_defined() {
                continue;
            }
            print!("  {}:", instance[pred]);
            for var in vars {
                print!(" {},", var.default_str())
            }
            println!()
        }
        // println!("}} clauses {{") ;
        // for (idx, _) in instance.clauses().index_iter() {

        // }
        println!("}}")
    }

    /// Initializes itself from an instance.
    fn init(&mut self, instance: &Instance) {
        self.keep.clear();
        self.lhs_vars.clear();
        self.rhs_vars.clear();

        // Empty set for each predicate.
        for _ in instance.preds() {
            self.keep.push(VarSet::new())
        }

        // Work on all clauses.
        for (idx, clause) in instance.clauses().index_iter() {
            debug_assert_eq! { self.lhs_vars.next_index(), idx }
            debug_assert_eq! { self.rhs_vars.next_index(), idx }

            let mut lhs_map: VarHMap<usize> = VarHMap::new();
            macro_rules! map {
                ($map:ident: add $var:expr => $n:expr) => {{
                    use std::ops::AddAssign;
                    $map.entry($var).or_insert(0).add_assign(1)
                }};
            }

            // Increment variables appearing in terms by one.
            for term in clause.lhs_terms() {
                for var in term::vars(term) {
                    map! { lhs_map: add var => 1 }
                }
            }
            // Increment variables appearing in pred apps by one.
            for (_, argss) in clause.lhs_preds() {
                for args in argss {
                    for arg in args.iter() {
                        for var in term::vars(arg) {
                            map! { lhs_map: add var => 1 }
                        }
                    }
                }
            }

            self.lhs_vars.push(lhs_map);

            // If there's a rhs, retrieve the map from its formal arguments to the
            // variables appearing in the actual arguments.
            let rhs_map = if let Some((pred, args)) = clause.rhs() {
                let mut rhs_map = VarMap::new();
                for arg in args.iter() {
                    rhs_map.push(term::vars(arg))
                }
                Some((pred, rhs_map))
            } else {
                None
            };

            self.rhs_vars.push(rhs_map);
        }
    }

    /// Checks if a variable appears more than once in a clause.
    ///
    /// Returns `true` if `cvar` appears
    ///
    /// - in `clause.lhs_terms()`
    /// - more than once in `clause.lhs_preds()`
    /// - in the rhs `(pred args)` of the clause in position `i`, and
    ///   `self.keep.get(pred).unwrap().get(i)` is true.
    pub fn should_keep(&self, cvar: VarIdx, idx: ClsIdx) -> bool {
        if *self.lhs_vars[idx]
            .get(&cvar)
            .expect("inconsistent ArgReductor state")
            > 1
        {
            return true;
        }

        if let Some((pred, pvar_map)) = &self.rhs_vars[idx] {
            for (pvar, cvars) in pvar_map.index_iter() {
                if self.keep[*pred].contains(&pvar) && cvars.contains(&cvar) {
                    return true;
                }
            }
        }

        false
    }

    /// Works on a clause.
    ///
    /// Returns `true` iff something changed.
    fn work_on(&mut self, clause: &Clause, idx: ClsIdx, instance: &Instance) -> bool {
        let mut changed = false;

        'all_preds: for (pred, argss) in clause.lhs_preds() {
            let pred = *pred;
            if self.keep[pred].len() == instance[pred].sig.len() {
                continue 'all_preds;
            }

            for args in argss {
                for (pvar, arg) in args.index_iter() {
                    if self.keep[pred].contains(&pvar) {
                        continue;
                    }

                    let keep = if let Some(cvar) = arg.var_idx() {
                        self.should_keep(cvar, idx)
                    } else {
                        true
                    };

                    if keep {
                        let is_new = self.keep[pred].insert(pvar);
                        debug_assert! { is_new }
                        changed = true
                    }
                }
            }
        }

        changed
    }

    /// Runs itself on all clauses of an instance.
    pub fn run(&mut self, instance: &Instance) -> PrdHMap<VarSet> {
        self.init(instance);

        let mut changed = true;

        // println!("\n\n") ;

        while changed {
            changed = false;

            for (idx, clause) in instance.clauses().index_iter() {
                // self.print(instance) ;
                // println!("") ;
                // println!("") ;
                // println!("{}", clause.to_string_info(instance.preds()).unwrap()) ;
                let has_changed = self.work_on(clause, idx, instance);
                changed = changed || has_changed
            }
        }

        let mut res = PrdHMap::new();
        for (pred, vars) in ::std::mem::replace(&mut self.keep, PrdMap::new()).into_index_iter() {
            if !instance[pred].is_defined() {
                let prev = res.insert(pred, vars);
                debug_assert! { prev.is_none() }
            }
        }

        res
    }
}

pub struct ArgReductor2 {
    /// Predicate arguments to keep.
    keep: PrdMap<VarSet>,
    /// Map from clauses to the variables appearing in their lhs.
    lhs_pred_vars: ClsMap<PrdHMap<VarMap<VarSet>>>,
    lhs_term_vars: ClsMap<VarSet>,
    /// Map from clauses to the varibales appearing in their rhs.
    rhs_vars: ClsMap<Option<VarHMap<usize>>>,
}
impl Default for ArgReductor2 {
    fn default() -> Self {
        Self::new()
    }
}
impl ArgReductor2 {
    /// Constructor.
    pub fn new() -> Self {
        ArgReductor2 {
            keep: PrdMap::new(),
            lhs_pred_vars: ClsMap::new(),
            lhs_term_vars: ClsMap::new(),
            rhs_vars: ClsMap::new(),
        }
    }

    /// Prints itself.
    #[allow(dead_code)]
    fn print(&mut self, instance: &Instance) {
        println!("keep {{");
        for (pred, vars) in self.keep.index_iter() {
            if instance[pred].is_defined() {
                continue;
            }
            print!("  {}:", instance[pred]);
            for var in vars {
                print!(" {},", var.default_str())
            }
            println!()
        }
        // println!("}} clauses {{") ;
        // for (idx, _) in instance.clauses().index_iter() {

        // }
        println!("}}")
    }

    /// Initializes itself from an instance.
    fn init(&mut self, instance: &Instance) {
        self.keep.clear();
        self.lhs_pred_vars.clear();
        self.lhs_term_vars.clear();
        self.rhs_vars.clear();

        // Empty set for each predicate.
        for _ in instance.preds() {
            self.keep.push(VarSet::new())
        }

        // Work on all clauses.
        for (idx, clause) in instance.clauses().index_iter() {
            debug_assert_eq! { self.lhs_pred_vars.next_index(), idx }
            debug_assert_eq! { self.lhs_term_vars.next_index(), idx }
            debug_assert_eq! { self.rhs_vars.next_index(), idx }

            // let mut rhs_map: VarHMap<usize> = VarHMap::new();
            macro_rules! map {
                ($map:ident: add $var:expr => $n:expr) => {{
                    use std::ops::AddAssign;
                    $map.entry($var).or_insert(0).add_assign(1)
                }};
            }

            let rhs_map = if let Some((_, args)) = clause.rhs() {
                let mut rhs_map = VarHMap::new();
                for arg in args.iter() {
                    for var in term::vars(arg) {
                        map! { rhs_map: add var => 1 }
                    }
                }
                Some(rhs_map)
            } else {
                None
            };
            self.rhs_vars.push(rhs_map);

            let mut lhs_maps = PrdHMap::new();
            for (&pred, argss) in clause.lhs_preds() {
                let mut lhs_map = VarMap::new();
                if let Some(args) = argss.iter().next() {
                    for _ in args.iter() {
                        lhs_map.push(VarSet::new())
                    }
                }
                for args in argss {
                    for (pvar, arg) in args.index_iter() {
                        lhs_map[pvar].extend(term::vars(arg));
                    }
                }
                lhs_maps.insert(pred, lhs_map);
            }

            self.lhs_pred_vars.push(lhs_maps);

            let mut lhs_vars = VarSet::new();
            for term in clause.lhs_terms() {
                lhs_vars.extend(term::vars(term));
            }
            self.lhs_term_vars.push(lhs_vars);
        }
    }

    /// Checks if a variable appears more than once in a clause.
    ///
    /// Returns `true` if `cvar` appears
    ///
    pub fn should_keep(&self, cvar: VarIdx, idx: ClsIdx) -> bool {
        if let Some(rhs_map) = &self.rhs_vars[idx] {
            if *rhs_map
                .get(&cvar)
                .expect("inconsistent ArgReductor2 state")
                > 1 
            {
                return true;
            }
        }

        for (pred, args) in self.lhs_pred_vars[idx].iter() {
            for (pvar, cvars) in args.index_iter() {
                if self.keep[*pred].contains(&pvar) && cvars.contains(&cvar) {
                    return true;
                }
            }
        }

        if self.lhs_term_vars[idx].contains(&cvar) {
            return true;
        }

        false
    }

    /// Works on a clause.
    ///
    /// Returns `true` iff something changed.
    fn work_on(&mut self, clause: &Clause, idx: ClsIdx, instance: &Instance) -> bool {
        let mut changed = false;

        if let Some((pred, args)) = clause.rhs() {
            if self.keep[pred].len() == instance[pred].sig.len() {
                return false;
            }

            for (pvar, arg) in args.index_iter() {
                if self.keep[pred].contains(&pvar) {
                    continue;
                }

                let keep = if let Some(cvar) = arg.var_idx() {
                    self.should_keep(cvar, idx)
                } else {
                    true
                };

                if keep {
                    let is_new = self.keep[pred].insert(pvar);
                    debug_assert! { is_new }
                    changed = true
                }
            }
        }

        changed
    }

    /// Runs itself on all clauses of an instance.
    pub fn run(&mut self, instance: &Instance) -> PrdHMap<VarSet> {
        self.init(instance);

        let mut changed = true;

        // println!("\n\n") ;

        while changed {
            changed = false;

            for (idx, clause) in instance.clauses().index_iter() {
                // self.print(instance) ;
                // println!("") ;
                // println!("") ;
                // println!("{}", clause.to_string_info(instance.preds()).unwrap()) ;
                let has_changed = self.work_on(clause, idx, instance);
                changed = changed || has_changed
            }
        }

        let mut res = PrdHMap::new();
        for (pred, vars) in ::std::mem::replace(&mut self.keep, PrdMap::new()).into_index_iter() {
            if !instance[pred].is_defined() {
                let prev = res.insert(pred, vars);
                debug_assert! { prev.is_none() }
            }
        }

        res
    }
}
