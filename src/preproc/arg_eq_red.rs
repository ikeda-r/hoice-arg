//!

use std::vec;

use num::{BigInt, Integer};

use crate::{
    common::{
        smt::{FullParser as Parser, SmtTerm},
        *,
    },
    data::Data,
    var_to::vals::*,
    preproc::{PreInstance, RedStrat, PredExtension}, term::fls,
};

pub struct ArgEqRed {}

impl RedStrat for ArgEqRed {
    fn name(&self) -> &'static str {
        "arg_eq_reduce"
    }

    fn new(_: &Instance) -> Self {
        ArgEqRed {}
    }

    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        let mut w = std::io::stdout();
        println!("clauses {{");
        for (cls_idx, cls) in instance.clauses().index_iter() {
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

        let mut reductor = ArgEqReductor::new(instance)?;
        let (constraints, to_keep) = reductor.run()?;

        if conf.preproc.arg_eq_red_check {
            let mut red = false;
            for (&pred, vars) in to_keep.iter() {
                if instance[pred].is_defined() {
                    continue;
                }
                let red_num = instance[pred].sig.len() - vars.len();
                if red_num > 0 {
                    red = true;
                    break;
                }
            }
            if red {
                eprintln!("reduced");
            } else {
                eprintln!("kept");
            }
            bail!("");
        }

        println!("to_keep {{");
        for (&pred, vars) in to_keep.iter() {
            if instance[pred].is_defined() {
                continue;
            }
            print!("  {}:", instance[pred]);
            for var in vars {
                print!(" {},", var.default_str())
            }
            println!();
        }
        println!("}}");
        println!("constraints {{");
        for (&pred, term) in constraints.iter() {
            print!("  {}: ", instance[pred]);
            if instance[pred].is_defined() {
                println!("defined ");
                continue;
            }
            let mut w = std::io::stdout();
            let (term, _) = term;
            let term = term.iter().next().unwrap();
            term.write(&mut w, |w, var| var.default_write(w));
            println!();
        }
        println!("}}");

        println!("clauses_before {{");
        for (cls_idx, cls) in instance.clauses().index_iter() {
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

        println!("preds_before {{");
        for pred in instance.preds() {
            print!("  {}: ", pred.name);
            if pred.is_defined() {
                println!("defined ");
                continue;
            }
            let mut w = std::io::stdout();
            if let Some(term) = pred.strength() {
                term.write(&mut w, |w, var| var.default_write(w));
            }
            println!();
        }
        println!("}}");

        // if !conf.preproc.arg_eq_red2 {
        //     let mut w = std::io::stdout();
        //     println!("clauses_after {{");
        //     for (cls_idx, cls) in instance.clauses().index_iter() {
        //         write!(w, "(assert (forall (")?;
        //         let mut inactive = 0;
        //         for var in &cls.vars {
        //             if var.active {
        //                 write!(w, " (")?;
        //                 var.idx.default_write(&mut w)?;
        //                 write!(w, " {})", var.typ)?;
        //             } else {
        //                 inactive += 1;
        //             }
        //         }
        //         if inactive == cls.vars.len() {
        //             write!(w, " (unused Bool)")?;
        //         } 
        //         write!(w, " ) ")?;
        //         cls.expr_to_smt2(&mut w, &(true, &PrdSet::new(), &PrdSet::new(), instance.preds()))?;
        //         writeln!(w, "))")?;
        //     }
        //     println!("}}");
        //     return Ok(RedInfo::new());
        // }

        let mut res = instance.add_constraint_left(&constraints, &to_keep)?;

        println!("clauses_after {{");
        for (cls_idx, cls) in instance.clauses().index_iter() {
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
        println!("preds_after {{");
        for pred in instance.preds() {
            print!("  {}: ", pred.name);
            if pred.is_defined() {
                println!("defined ");
                continue;
            }
            let mut w = std::io::stdout();
            if let Some(term) = pred.strength() {
                term.write(&mut w, |w, var| var.default_write(w));
            }
            println!();
        }
        println!("}}");

        // let res2 = instance.rm_args(to_keep)?;

        // res += res2;

        // println!("clauses {{");
        // for (cls_idx, cls) in instance.clauses().index_iter() {
        //     write!(w, "(assert (forall (")?;
        //     let mut inactive = 0;
        //     for var in &cls.vars {
        //         if var.active {
        //             write!(w, " (")?;
        //             var.idx.default_write(&mut w)?;
        //             write!(w, " {})", var.typ)?;
        //         } else {
        //             inactive += 1;
        //         }
        //     }
        //     if inactive == cls.vars.len() {
        //         write!(w, " (unused Bool)")?;
        //     } 
        //     write!(w, " ) ")?;
        //     cls.expr_to_smt2(&mut w, &(true, &PrdSet::new(), &PrdSet::new(), instance.preds()))?;
        //     writeln!(w, "))")?;
        // }
        // println!("}}");

        Ok(res)
    }
}

/// Argument reduction context.
pub struct ArgEqReductor {
    /// Predicate arguments to keep.
    keep: PrdMap<VarSet>,
    instance: Arc<Instance>,
    imp_and_pos_clauses: ClsSet,
    solver: Solver<Parser>,
    data: Data,
    raw_constraints: PrdMap<VarValsSet>,
    constraints: Candidates,
    tru_preds: PrdSet,
    fls_preds: PrdSet,
}

impl ArgEqReductor {
    /// Constructor.
    pub fn new(pre_instance: &PreInstance) -> Res<Self> {
        let instance = Arc::new((**pre_instance).clone());

        let mut keep = PrdMap::with_capacity(instance.preds().len());
        // Empty set for each predicate.
        for _ in instance.preds() {
            keep.push(VarSet::new())
        }

        let mut imp_and_pos_clauses = ClsSet::new();
        for (idx, clause) in instance.clauses().index_iter() {
            if clause.rhs().is_some() {
                imp_and_pos_clauses.insert(idx);
            }
        }

        let data = Data::new(instance.clone());

        let solver = conf.solver.spawn("arg_eq_red", Parser, &instance)?;

        let raw_constraints = PrdMap::new();
        let constraints = PrdMap::of_elems(None, instance.preds().len());
        let tru_preds = PrdSet::new();
        let fls_preds = PrdSet::new();

        Ok(ArgEqReductor {
            keep,
            instance,
            imp_and_pos_clauses,
            solver,
            data,
            raw_constraints,
            constraints,
            tru_preds,
            fls_preds,
        })
    }

    /// Prints itself.
    #[allow(dead_code)]
    fn print(
        &mut self,
        constraints: &PrdHMap<crate::preproc::PredExtension>,
        to_keep: &PrdHMap<VarSet>,
        instance: &Instance,
    ) {
        println!("to_keep {{");
        for (&pred, vars) in to_keep {
            if instance[pred].is_defined() {
                continue;
            }
            print!("  {}:", instance[pred]);
            for var in vars {
                print!(" {},", var.default_str())
            }
            println!()
        }
        println!("constraints {{");
        for (&pred, (terms, _)) in constraints {
            if instance[pred].is_defined() {
                continue;
            }
            print!("  {}: ", instance[pred]);
            let mut w = std::io::stdout();
            terms.iter().next().unwrap().write(&mut w, |w, var| var.default_write(w));
            println!()
        }
        println!("}}")
    }

    fn print2(
        &mut self,
    ) {
        println!("to_keep {{");
        for (pred, vars) in self.keep.index_iter() {
            if self.instance[pred].is_defined() {
                continue;
            }
            print!("  {}:", self.instance[pred]);
            for var in vars {
                print!(" {},", var.default_str())
            }
            println!()
        }
        println!("constraints {{");
        for (pred, term) in self.constraints.index_iter() {
            print!("  {}: ", self.instance[pred]);
            if self.instance[pred].is_defined() {
                println!("defined ");
                continue;
            }
            let mut w = std::io::stdout();
            if let Some(term) = term {
                term.write(&mut w, |w, var| var.default_write(w));
            } else {
                print!("None ");
                if self.tru_preds.contains(&pred) {
                    print!("true");
                } else if self.fls_preds.contains(&pred) {
                    print!("false");
                }
            }
            println!()
        }
        println!("}}")
    }

    fn print_data(
        &mut self,
    ) -> Res<()> {
        println!("{}", self.data.string_do(&(), |s| s.to_string())?);
        Ok(())
    }

    fn handle_candidates(&mut self) -> Res<bool> {
        smt::reset(&mut self.solver, &self.instance)?;
        self.fls_preds.clear();
        for (pred, cand) in self.constraints.index_iter() {
            if self.instance[pred].is_defined() {
                continue;
            } else if self.tru_preds.contains(&pred) {
                // skip
            } else if let Some(term) = cand {
                let pred = &self.instance[pred];
                let sig: Vec<_> = pred
                    .sig
                    .index_iter()
                    .map(|(var, typ)| (var, typ.get()))
                    .collect();
                self.solver.define_fun(
                    &pred.name,
                    &sig,
                    typ::bool().get(),
                    &SmtTerm::new(&term),
                )?;
            } else {
                self.fls_preds.insert(pred);
            }
        }

        let mut cexs = ClsHMap::with_capacity(self.instance.clauses().len());
        let mut imp_and_pos_clauses = ClsSet::new();
        std::mem::swap(&mut imp_and_pos_clauses, &mut self.imp_and_pos_clauses);
        for &clause in &imp_and_pos_clauses {
            self.get_cexs_of_clause(clause, &mut cexs)?
        }
        std::mem::swap(&mut imp_and_pos_clauses, &mut self.imp_and_pos_clauses);

        let res = self.instance.cexs_to_data(&mut self.data, cexs)?;

        for cstr in self.data.constraints.clone() {
            if let Some(pos) = cstr.rhs() {
                self.data.add_pos(0.into(), pos.pred, pos.args.clone());
            }
        }
        self.data.propagate()?;

        Ok(res)
    }

    fn get_cexs_of_clause(&mut self, cls_idx: ClsIdx, map: &mut Cexs) -> Res<()> {
        let clause = &self.instance[cls_idx];

        self.solver.push(1)?;
        clause.declare(&mut self.solver)?;
        self.solver.assert_with(
            clause,
            &(
                false,
                &self.tru_preds,
                &self.fls_preds,
                self.instance.preds(),
            ),
        )?;

        let sat = self.solver.check_sat()?;
        if sat {
            let model = self.solver.get_model()?;
            let model = Parser.fix_model(model)?;
            let cex = Cex::of_model(
                clause.vars(),
                model,
                true,
            )?;
            let bias = Bias::Non;
            let cexs = vec![(cex, bias)];
            let prev = map.insert(cls_idx, cexs);
            debug_assert_eq!(prev, None)
        }

        self.solver.pop(1)?;

        Ok(())
    }

    fn generate_constraints(&mut self) -> Res<()> {
        let mut raw_constraints = PrdMap::with_capacity(self.data.pos.len());
        for (pred, samples) in self.data.pos.index_iter() {
            if self.instance[pred].is_defined() {
                raw_constraints.push(None);
                continue;
            } 
            if self.tru_preds.contains(&pred) {
                raw_constraints.push(None);
                continue;
            }

            let mut iter = samples.iter();
            if let Some(base) = iter.next() {
                let mut var_map = Vec::with_capacity(base.len());
                let mut base_vector = Vec::with_capacity(base.len());
                for (var, val) in base.index_iter() {
                    if val.typ().is_int() {
                        var_map.push(var);
                        base_vector.push(base[var].to_int()?.ok_or("base[var] is none")?);
                    }
                }

                let mut vectors = Vec::with_capacity(samples.len() - 1);
                for sample in iter {
                    let mut vector = Vec::with_capacity(var_map.len());
                    for i in 0..var_map.len() {
                        let vval = &sample[var_map[i]];
                        debug_assert!(vval.typ().is_int());
                        let vval = vval.to_int()?.ok_or("vval is none")?;
                        let bval = base_vector[i].clone();
                        vector.push(Rat::from(vval - bval));
                    }
                    vectors.push(vector);
                }
                let rank = gauss_jordan_elimination(&mut vectors);
                raw_constraints.push(Some((var_map, base_vector, vectors, rank)));
            } else {
                raw_constraints.push(None);
            }
        }

        let mut constraints = PrdMap::new();
        let mut keeps = PrdMap::with_capacity(self.instance.preds().len());
        // self.fls_preds.clear();
        for (pred, raw_constraint) in raw_constraints.index_iter() {
            let mut keep = VarSet::with_capacity(self.instance[pred].sig().len());
            if self.instance[pred].is_defined() {
                constraints.push(None);
            } else if self.tru_preds.contains(&pred) {
                constraints.push(None);
                for (var, _) in self.instance[pred].sig().index_iter() {
                    keep.insert(var);
                }
            } else if let Some((var_map, base_vector, vectors, rank)) = raw_constraint {
                let rank = *rank;
                let dim = var_map.len();
                if dim <= rank {
                    self.tru_preds.insert(pred);
                    constraints.push(None);
                    for (var, _) in self.instance[pred].sig().index_iter() {
                        keep.insert(var);
                    }
                } else {
                    let mut pivot_indices = Vec::with_capacity(rank);
                    let mut non_pivot_indices = Vec::with_capacity(dim - rank);

                    {
                        let mut non_zero_ind = 0;
                        for (var, _) in self.instance[pred].sig().index_iter() {
                            keep.insert(var);
                        }
                        for param_ind in 0..rank {
                            while vectors[param_ind][non_zero_ind].is_zero() {
                                keep.remove(&var_map[non_zero_ind]);
                                non_pivot_indices.push(non_zero_ind);
                                non_zero_ind += 1;
                            }
                            pivot_indices.push(non_zero_ind);
                            non_zero_ind += 1;
                        }
                        for i in non_zero_ind..dim {
                            keep.remove(&var_map[i]);
                            non_pivot_indices.push(i);
                        }
                    }
                    

                    let mut and_terms = Vec::with_capacity(dim - rank);
                    for var_ind in non_pivot_indices.into_iter() {
                        let mut const_part = Rat::from(base_vector[var_ind].clone());
                        let mut coef_part = Vec::with_capacity(rank);
                        for i in 0..rank {
                            const_part -= vectors[i][var_ind].clone() * Rat::from(base_vector[pivot_indices[i]].clone());
                            coef_part.push(vectors[i][var_ind].clone());
                        }
                        let mut denom_lcm = const_part.denom().clone();
                        for i in 0..coef_part.len() {
                            denom_lcm = denom_lcm.lcm(coef_part[i].denom());
                        }
                        const_part *= Rat::from(denom_lcm.clone());
                        for i in 0..coef_part.len() {
                            coef_part[i] *= Rat::from(denom_lcm.clone());
                        }

                        let const_part = const_part.to_integer();
                        let coef_part: Vec<_> = coef_part.iter().map(|x| x.to_integer()).collect();

                        let mut add_terms = Vec::with_capacity(1 + coef_part.len());
                        if !const_part.is_zero() {
                            add_terms.push(term::int(const_part));
                        }
                        for i in 0..coef_part.len() {
                            if !coef_part[i].is_zero() {
                                let var_ind = pivot_indices[i];
                                let var = var_map[var_ind];
                                let var_term = term::var(var, self.instance[pred].sig()[var].clone());
                                let mul_term = term::mul(vec![var_term, term::int(coef_part[i].clone())]);
                                add_terms.push(mul_term);
                            }
                        }
                        let add_term = if add_terms.is_empty() { term::int_zero() } else { term::add(add_terms) };
                        let lhs_term = {
                            let var = var_map[var_ind];
                            let var_term = term::var(var, self.instance[pred].sig()[var].clone());
                            term::mul(vec![var_term, term::int(denom_lcm)])
                        };
                        let and_term = term::eq(lhs_term, add_term);
                        and_terms.push(and_term);
                    }

                    let term = term::and(and_terms);
                    constraints.push(Some(term));
                }
            } else {
                constraints.push(None);
                // self.fls_preds.insert(pred);
            }

            keeps.push(keep);
        }

        self.constraints = constraints;
        self.keep = keeps;

        Ok(())
    }

    /// Runs itself on all clauses of an instance.
    pub fn run(mut self) -> Res<(PrdHMap<crate::preproc::PredExtension>, PrdHMap<VarSet>)> {
        loop {
            if !self.handle_candidates()? {
                break;
            }
            self.generate_constraints()?;
            self.print2();
            self.print_data()?;
        }

        let mut constraints = PrdHMap::new();
        let mut op_constraints = PrdMap::new();
        std::mem::swap(&mut op_constraints, &mut self.constraints);
        for (pred, term) in op_constraints.into_index_iter() {
            if let Some(term) = term {
                let mut set = TermSet::with_capacity(1);
                set.insert(term);
                constraints.insert(pred, (set, vec![]));
            }
        }

        // for clause in self.instance.clauses() {
        //     if let Some((prd_idx, args)) = clause.rhs() {
        //         if let Some(term) = &self.constraints[prd_idx] {

        //             smt::reset(&mut self.solver, &self.instance)?;
        //             let pred = &self.instance[prd_idx];
        //             let sig: Vec<_> = pred
        //                 .sig
        //                 .index_iter()
        //                 .map(|(var, typ)| (var, typ.get()))
        //                 .collect();
        //                 self.solver.define_fun(
        //                 &pred.name,
        //                 &sig,
        //                 typ::bool().get(),
        //                 &SmtTerm::new(&term),
        //             )?;

                    // let tru_preds = clause.lhs_preds().keys().cloned().collect();

                    // self.solver.push(1)?;
                    // clause.declare(&mut self.solver)?;
                    // self.solver.assert_with(
                    //     clause,
                    //     &(
                    //         false,
                    //         &tru_preds,
                    //         &PrdSet::new(),
                    //         self.instance.preds(),
                    //     ),
                    // )?;

                    // if self.solver.check_sat()? {
                    //     let lhs = Vec::with_capacity(clause.lhs_len() + 1);
                    //     for (prd_idx, argss) in clause.lhs_preds() {
                    //         for args in argss {

                    //         }
                    //     }
                    //     for term in clause.lhs_terms() {
                            
                    //     }
                    //     self.pre_instance.push_new_clause(clause.vars.clone(), lhs, None, "arg_eq_red")?.ok_or("failed while adding a clause")?;
                    // } else {
                    //     // inductive invariant
                    // }

                    // self.solver.pop(1)?;
        //         }
        //     }
        // }

        let mut to_keep = PrdHMap::new();
        for (pred, vars) in ::std::mem::replace(&mut self.keep, PrdMap::new()).into_index_iter() {
            if !self.instance[pred].is_defined() {
                let prev = to_keep.insert(pred, vars);
                debug_assert! { prev.is_none() }
            }
        }

        // let tru_preds = ::std::mem::replace(&mut self.tru_preds, PrdSet::new());

        self.print(&constraints, &to_keep, &self.instance.clone());

        Ok((constraints, to_keep))
    }
}

/**
 * return rank
 */
fn gauss_jordan_elimination(vectors: &mut Vec<Vec<Rat>>) -> usize {
    let dim = if vectors.len() > 0 { vectors[0].len() } else { 0 };
    let vec_count = vectors.len();
    let mut non_zero_ind = 0;
    for vec_ind in 0..vec_count {
        'non_zero_ind: while non_zero_ind < dim {
            for i in vec_ind..vec_count {
                if !vectors[i][non_zero_ind].is_zero() {
                    vectors.swap(vec_ind, i);
                    break 'non_zero_ind;
                }
            }
            non_zero_ind += 1;
        }
        if non_zero_ind == dim {
            return vec_ind;
        }
        let denom = vectors[vec_ind][non_zero_ind].clone();
        for j in non_zero_ind..dim {
            vectors[vec_ind][j] /= denom.clone();
        }
        for i in 0..vec_count {
            if i == vec_ind {
                continue;
            }
            let mult = vectors[i][non_zero_ind].clone();
            for j in non_zero_ind..dim {
                let x = vectors[vec_ind][j].clone() * mult.clone();
                vectors[i][j] -= x;
            }
        }
    }
    return vec_count;
}
