//! SMT-related zero-cost wrappers.

use std::str::FromStr ;

use rsmt2::{
  print::*,
  parse::{ IdentParser, ModelParser },
} ;

use common::{
  *,
  var_to::vals::{ VarValsMap, VarValsSet }
} ;
use data::Constraint ;
use instance::Clause ;


/// Initial setup for a solver.
///
/// - declares all the datatypes
/// - defines all the functions
/// - asserts all the side-clauses if `preproc` is false
pub fn init<P, I>(
  solver: & mut Solver<P>, instance: I
) -> Res<()>
where I: AsRef<Instance> {
  dtyp::write_all(solver, "") ? ;
  fun::write_all(solver) ? ;
  instance.as_ref().assert_side_clauses(solver)
}

/// Initial setup for a preprocessing solver.
///
/// - declares all the datatypes
/// - defines all the functions
/// - asserts all the side-clauses if `preproc` is false
pub fn preproc_init<P>( solver: & mut Solver<P> ) -> Res<()> {
  dtyp::write_all(solver, "") ? ;
  fun::write_all(solver) ? ;
  Ok(())
}


/// Resets a smt solver.
///
/// Use this and not `solver.reset()`. This declares all the
/// datatypes/functions used in the instance.
pub fn reset<P, I>(
  solver: & mut Solver<P>, instance: I
) -> Res<()>
where I: AsRef<Instance> {
  solver.reset() ? ;
  init(solver, instance)
}

/// Resets a smt preprocessing solver.
///
/// Use this and not `solver.reset()`. This declares all the
/// datatypes/functions used in the instance.
pub fn preproc_reset<P>( solver: & mut Solver<P> ) -> Res<()> {
  solver.reset() ? ;
  preproc_init(solver)
}



/// SMT-prints a term using the default var writer.
pub struct SmtTerm<'a> {
  /// The term.
  pub term: & 'a Term,
}
impl<'a> SmtTerm<'a> {
  /// Constructor.
  pub fn new(term: & 'a Term) -> Self {
    SmtTerm { term }
  }
}
impl<'a> Expr2Smt<()> for SmtTerm<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    self.term.write(
      w, |w, var| var.default_write(w)
    ) ? ;
    Ok(())
  }
}



/// Smt-prints a clause that has no predicate application.
pub struct SmtSideClause<'a> {
  /// The clause.
  pub clause: & 'a Clause,
}
impl<'a> SmtSideClause<'a> {
  /// Constructor.
  pub fn new(clause: & 'a Clause) -> Self {
    SmtSideClause { clause }
  }
}
impl<'a> Expr2Smt<()> for SmtSideClause<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    self.clause.forall_write(
      w, |w, var_info| var_info.idx.default_write(w), |_, _, _| panic!(
        "illegal side clause: found predicate application(s)"
      ), 2
    ) ? ;
    Ok(())
  }
}


/// SMT-prints a collection of terms as a conjunction with default var writer.
pub struct SmtConj<'a, Trms> {
  /// Conjunction.
  terms: Trms,
  /// True if the terms have function applications.
  has_fun_apps: bool,
  /// Variable informations.
  infos: & 'a VarInfos
}
impl<'a, 'b, Trms> SmtConj<'b, Trms>
where Trms: Iterator<Item = & 'a Term> + ExactSizeIterator + Clone {
  /// Constructor.
  pub fn new<IntoIter>(terms: IntoIter, infos: & 'b VarInfos) -> Self
  where IntoIter: IntoIterator<IntoIter = Trms, Item = & 'a Term> {
    let terms = terms.into_iter() ;
    let mut has_fun_apps = false ;
    for term in terms.clone() {
      if term.has_fun_apps() {
        has_fun_apps = true ;
        break
      }
    }
    SmtConj { terms, has_fun_apps, infos }
  }

  /// Checks if this conjunction is unsatisfiable.
  pub fn is_unsat<Parser: Copy>(
    & self, solver: & mut Solver<Parser>, actlit: Option<& Actlit>
  ) -> Res<bool> {
    if self.terms.len() == 0 { return Ok(false) }
    solver.push(1) ? ;
    if ! self.has_fun_apps {
      for var in self.infos {
        if var.active {
          solver.declare_const(& var.idx, var.typ.get()) ?
        }
      }
    }
    solver.assert( self ) ? ;
    let sat = solver.check_sat_act(actlit) ? ;
    solver.pop(1) ? ;
    Ok(! sat)
  }
}

impl<'a, 'b, Trms> Expr2Smt<()> for SmtConj<'b, Trms>
where Trms: Iterator<Item = & 'a Term> + ExactSizeIterator + Clone {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    let suffix = if self.has_fun_apps {
      write!(w, "(exists (") ? ;
      let mut inactive = 0 ;
      for var in self.infos {
        if var.active {
          write!(w, " (") ? ;
          var.idx.default_write(w) ? ;
          write!(w, " {})", var.typ) ?
        } else {
          inactive += 1
        }
      }
      if inactive == self.infos.len() {
        write!(w, " (unused Bool)") ?
      }
      write!(w, " ) ") ? ;
      ")"
    } else {
      ""
    } ;

    if self.terms.len() == 0 {
      write!(w, "true") ?
    } else {
      write!(w, "(and") ? ;
      for term in self.terms.clone() {
        write!(w, " ") ? ;
        term.write(
          w, |w, var| var.default_write(w)
        ) ? ;
      }
      write!(w, ")") ?
    }
    write!(w, "{}", suffix) ? ;
    Ok(())
  }
}



/// SMT-prints an implication `/\ (set \ term) => term`.
pub struct SmtImpl<'a> {
  /// Set of terms.
  pub set: & 'a TermSet,
  /// Term to remove from `set`.
  pub trm: & 'a Term,
}
impl<'a> SmtImpl<'a> {
  /// Constructor.
  ///
  /// Returns `None` if `set.is_empty()`.
  pub fn new(set: & 'a TermSet, trm: & 'a Term) -> Option<Self> {
    if ! set.is_empty() {
      Some( SmtImpl { set, trm } )
    } else {
      None
    }
  }
}
impl<'a> Expr2Smt<()> for SmtImpl<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    debug_assert! { ! self.set.is_empty() }
    write!(w, "(and (not ") ? ;
    self.trm.write(w, |w, var| var.default_write(w)) ? ;
    write!(w, ") ") ? ;
    if self.set.len() <= 1 {
      write!(w, "true") ?
    } else {
      write!(w, "(and ") ? ;
      for term in self.set {
        if term != self.trm {
          write!(w, " ") ? ;
          term.write(w, |w, var| var.default_write(w)) ?
        }
      }
      write!(w, ")") ?
    }
    write!(w, ")") ? ;
    Ok(())
  }
}



/// Wrapper around a predicate/sample pair that SMT-prints it as an identifier.
///
/// In practice, will be printed as `format!("|p_{} {}|", pred, smpl.uid())`.
pub struct SmtSample<'a> {
  /// Predicate index.
  pub pred: PrdIdx,
  /// Reference to a sample.
  pub smpl: & 'a VarVals,
}
impl<'a> SmtSample<'a> {
  /// Constructor.
  pub fn new(pred: PrdIdx, smpl: & 'a VarVals) -> Self {
    SmtSample { pred, smpl }
  }
}
impl<'a> Expr2Smt<()> for SmtSample<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    write!( w, "|p_{} {}|", self.pred, self.smpl.uid() ) ? ;
    Ok(())
  }
}
impl<'a> Sym2Smt<()> for SmtSample<'a> {
  fn sym_to_smt2<Writer>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> where Writer: Write {
    self.expr_to_smt2(w, ())
  }
}


/// Wrapper around constraints that forces smt printing consistent with
/// [`SmtSample`][swrap].
///
/// [swrap]: struct.SmtSample.html (SmtSample struct)
pub struct SmtConstraint<'a> {
  /// Reference to the constraint.
  pub constr: & 'a Constraint,
}
impl<'a> SmtConstraint<'a> {
  /// Constructor.
  pub fn new(constr: & 'a Constraint) -> Self {
    SmtConstraint { constr }
  }
}
impl<'a> Expr2Smt<()> for SmtConstraint<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    write!(w, "(=> ") ? ;
    if let Some(lhs) = self.constr.lhs() {
      write!(w, "(and") ? ;
      for (pred, samples) in lhs {
        for sample in samples {
          write!(w, " ", ) ? ;
          SmtSample::new(
            * pred, sample
          ).expr_to_smt2(w, ()) ?
        }
      }
      write!(w, ") ") ?
    } else {
      write!(w, "false ") ?
    }
    if let Some(rhs) = self.constr.rhs() {
      SmtSample::new(
        rhs.pred, & rhs.args
      ).expr_to_smt2(w, ()) ?
    } else {
      write!(w, "false") ? ;
    }
    write!(w, ")") ? ;
    Ok(())
  }
}


/// Wrapper for activation literals activating samples for some predicate.
///
/// `Sym2Smt` implementation just yields the actlit, used to declare said
/// actlit. `Expr2Smt` is the actual activation expression
///
/// ```bash
/// (=> <actlit> (and <samples>))
/// ```
///
/// Used by the ICE learner.
pub struct SmtActSamples<Samples> {
  /// Activation literal.
  pub actlit: Actlit,
  /// Predicate.
  pub pred: PrdIdx,
  /// Samples.
  pub unc: Samples,
  /// Indicates whether we're assuming the samples positive or negative.
  pub pos: bool,
}
impl<Samples> SmtActSamples<Samples> {
  /// Constructor.
  pub fn new<Parser>(
    solver: & mut Solver<Parser>, pred: PrdIdx, unc: Samples, pos: bool
  ) -> Res<Self> {
    let actlit = solver.get_actlit() ? ;
    Ok( SmtActSamples { actlit, pred, unc, pos } )
  }

  /// Sets the actlit to `pos` and destroys itself.
  pub fn force<Parser>(
    self, solver: & mut Solver<Parser>, pos: bool
  ) -> Res<()> {
    solver.set_actlit(self.actlit, pos) ? ;
    Ok(())
  }
}
impl<'a> Expr2Smt<()> for SmtActSamples<& 'a [ VarVals ]> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    write!(w, "(=> ") ? ;
    self.actlit.write(w) ? ;
    write!(
      w, " ({}", if self.pos { "and" } else { "not (or" }
    ) ? ;
    for unc in self.unc {
      write!(w, " ", ) ? ;
      SmtSample::new(self.pred, unc).expr_to_smt2(w, ()) ?
    }
    write!(w, "))") ? ;
    if ! self.pos {
      write!(w, ")") ?
    }
    Ok(())
  }
}
impl<'a, T> Expr2Smt<()> for SmtActSamples< & 'a VarValsMap<T> > {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    write!(w, "(=> ") ? ;
    self.actlit.write(w) ? ;
    write!(
      w, " ({}", if self.pos { "and" } else { "not (or" }
    ) ? ;
    for (unc, _) in self.unc {
      write!(w, " ", ) ? ;
      SmtSample::new(self.pred, unc).expr_to_smt2(w, ()) ?
    }
    write!(w, "))") ? ;
    if ! self.pos {
      write!(w, ")") ?
    }
    Ok(())
  }
}



/// Wrapper around some terms and some values for these terms.
///
/// Asserts that each term is equal to the corresponding value.
pub struct EqConj<'a> {
  /// Terms.
  pub terms: & 'a [ Term ],
  /// Values.
  pub vals: & 'a VarVals,
}
impl<'a> EqConj<'a> {
  /// Constructor.
  ///
  /// Both lists must have the same length.
  pub fn new(terms: & 'a [ Term ], vals: & 'a VarVals) -> Self {
    debug_assert_eq! { terms.len(), vals.len() }

    EqConj { terms, vals }
  }
}
impl<'a> Expr2Smt<()> for EqConj<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    let mut is_first = true ;
    for (term, val) in self.terms.iter().zip( self.vals.iter() ) {
      if ! val.is_known() {
        continue
      }
      if is_first {
        write!(w, "(and") ? ;
        is_first = false
      }
      write!(w, " (= ") ? ;
      term.write(w, |w, var| write!(w, "{}", var.default_str())) ? ;
      write!(w, " ") ? ;
      val.expr_to_smt2(w, ()) ? ;
      write!(w, ")") ?
    }
    if is_first {
      write!(w, "true") ?
    } else {
      write!(w, ")") ?
    }
    Ok(())
  }
}



/// Wrapper for some arguments and a disjunction of terms.
///
/// Corresponds to the disjunction of `(= args v)` for `v` in `vals`.
pub struct DisjArgs<'a> {
  /// Arguments.
  pub args: & 'a VarTerms,
  /// Values to force the arguments to.
  pub vals: & 'a VarValsSet,
}
impl<'a> DisjArgs<'a> {
  /// Constructor.
  ///
  /// Error if `args` or `vals` is empty.
  #[inline]
  pub fn new(
    args: & 'a VarTerms, vals: & 'a VarValsSet
  ) -> Res<Self> {
    if args.is_empty() {
      bail!("can't create a `DisjArgs` with empty `args`")
    }
    if vals.is_empty() {
      bail!("can't create an empty `DisjArgs`")
    }
    Ok( DisjArgs { args, vals } )
  }
}
impl<'a> Expr2Smt<()> for DisjArgs<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    write!(w, "(or") ? ;
    for vals in self.vals {
      write!(w, " (and") ? ;
      debug_assert_eq! { self.args.len(), vals.len() }
      let mut at_least_one = false ;
      for (arg, val) in self.args.iter().zip( vals.iter() ) {
        if val.is_known() {
          at_least_one = true ;
          write!(w, " (= ") ? ;
          arg.write(w, |w, var| write!(w, "{}", var.default_str())) ? ;
          write!(w, " ") ? ;
          val.expr_to_smt2(w, ()) ? ;
          write!(w, ")") ?
        }
      }
      if ! at_least_one {
        write!(w, " true") ?
      }
      write!(w, ")") ?
    }
    write!(w, ")") ? ;

    Ok(())
  }
}





/// Type of values returned by the full parser.
#[derive(Debug)]
pub enum FPVal {
  /// A normal value.
  Val(Val),
  /// A function to array conversion.
  FunToArray(String),
  /// A function declaration.
  FunDef(String),
}
/// Type of variables returned by the full parser.
#[derive(Debug)]
pub enum FPVar {
  /// A normal variable.
  Var(VarIdx),
  /// A symbol that's not a normal variable.
  Sym(String),
}




/// Input signature for a model that's not fixed yet.
type FPSig = Vec<(FPVar, Typ)> ;



/// Unit type parsing the output of the SMT solver.
///
/// Parses variables of the form `v<int>` and constants. It is designed to
/// parse models of the falsification of a single clause, where the
/// variables of the clause are written as `v<index>` in smt2.
#[derive(Clone, Copy)]
pub struct FullParser ;

impl FullParser {
  /// Translates a raw model to a normal model.
  pub fn fix_model(
    self, mut model: Vec<(FPVar, FPSig, Typ, FPVal)>
  ) -> Res< Vec<(VarIdx, Typ, Val)> > {
    let mut fun_defs: HashMap<String, (Sig, Term)> = HashMap::new() ;
    let mut res = Vec::with_capacity( model.len() ) ;
    let mut postponed = Vec::new() ;

    let mut instance = Instance::new() ;
    let mut context = ::parse::ParserCxt::new() ;
    let dummy_profiler = Profiler::new() ;

    let mut stuck ;

    while ! model.is_empty() {
      let model_len = model.len() ;

      while let Some((var, sig, mut typ, val)) = model.pop() {
        match var {

          FPVar::Var(var) => match val {
            FPVal::Val(val) => {
              res.push((var, typ, val))
            },
            FPVal::FunToArray(fun) => if let Some(
              (sig, def)
            ) = fun_defs.get(& fun) {
              debug_assert_eq! { sig.len(), 1 }
              let idx_type = sig.iter().next().unwrap() ;
              let array = val::array_of_fun(idx_type.clone(), def).chain_err(
                || "while recovering array from function definition"
              ) ? ;
              res.push( (var, typ, array) )
            } else {
              postponed.push(
                (FPVar::Var(var), sig, typ, FPVal::FunToArray(fun))
              )
            },
            FPVal::FunDef(def) => bail!(
              "inconsistent model, \
              normal variable {} associated to function definition {}",
              var.default_str(), def
            ),
          },

          FPVar::Sym(name) => {
            use ::instance::info::VarInfo ;

            let (mut nu_sig, mut var_infos): (
              VarMap<Typ>, VarMap<_>
            ) = (
              VarMap::with_capacity( sig.len() ),
              VarMap::with_capacity( sig.len() ),
            ) ;

            for (var, typ) in & sig {
              let idx = var_infos.next_index() ;
              if let FPVar::Sym(ref var) = * var {
                nu_sig.push( typ.clone() ) ;
                var_infos.push(
                  VarInfo::new(var.clone(), typ.clone(), idx)
                ) ;
              } else {
                bail!("inconsistent function parameters: variable index")
              }
            }

            if let Ok( Some(mut term) ) = match val {
              FPVal::FunDef(ref fun) => {
                let mut var_hmap: BTreeMap<
                  & str, VarIdx
                > = BTreeMap::new() ;

                for (idx, info) in var_infos.index_iter() {
                  let prev = var_hmap.insert(
                    & info.name, idx
                  ) ;
                  debug_assert_eq! { prev, None }
                }

                let mut parser = context.parser(fun, 0, & dummy_profiler) ;

                parser.term_opt(
                  & var_infos, & var_hmap, & instance
                )
              },

              FPVal::Val(ref val) => Ok( val.to_term() ),

              FPVal::FunToArray(fun) => bail!(
                "inconsistent model, function name {} \
                associated to function to array conversion {}",
                name, fun
              ),
            } {
              if let Some(new_typ) = term.typ().merge(& typ) {
                if typ != new_typ {
                  typ = new_typ.clone()
                }
                if term.typ() != new_typ {
                  if let Some(nu_term) = term.force_dtyp(new_typ) {
                    term = nu_term
                  }
                }
              }
              debug_assert_eq! { term.typ(), typ }
              let prev = instance.add_define_fun(
                name.clone(), var_infos,
                ::parse::PTTerms::tterm( TTerm::T(term.clone()) )
              ) ;
              debug_assert! { prev.is_none() }
              let prev = fun_defs.insert(name, (nu_sig, term)) ;
              debug_assert_eq! { prev, None }
            } else {
              postponed.push(
                (FPVar::Sym(name), sig, typ, val)
              )
            }
          },

        }

      }

      stuck = model_len == postponed.len() ;

      if stuck {
        bail!("failed to parse model from solver")
      }

      model.extend( postponed.drain(0..) )

    }

    Ok(res)
  }
}

impl<'a> IdentParser<FPVar, Typ, & 'a str> for FullParser {
  fn parse_ident(self, input: & 'a str) -> SmtRes<FPVar> {
    if input.len() >= 2 && & input[0..2] == "v_" {
      match usize::from_str(& input[2..]) {
        Ok(idx) => Ok( FPVar::Var( idx.into() ) ),
        Err(e) => bail!(
          "could not retrieve var index from `{}`: {}", input, e
        ),
      }
    } else {
      Ok( FPVar::Sym( input.into() ) )
    }
  }
  fn parse_type(self, input: & 'a str) -> SmtRes<Typ> {
    let mut cxt = ::parse::ParserCxt::new() ;
    let dummy_profiler = Profiler::new() ;
    let mut parser = cxt.parser(input, 0, & dummy_profiler) ;
    match parser.sort_opt() {
      Ok( Some(s) ) => Ok(s),
      _ => Err(
        format!("unexpected type `{}`", input).into()
      ),
    }
  }
}

impl<'a> ModelParser<FPVar, Typ, FPVal, & 'a str> for FullParser {
  fn parse_value(
    self, input: & 'a str,
    _id: & FPVar, _params: & [ (FPVar, Typ) ], _out: & Typ
  ) -> SmtRes<FPVal> {
    let mut cxt = ::parse::ParserCxt::new() ;
    let dummy_profiler = Profiler::new() ;
    let mut parser = cxt.parser(input, 0, & dummy_profiler) ;

    let negated = {
      let start = parser.pos() ;
      if parser.tag_opt("(") && {
        parser.ws_cmt() ; parser.tag_opt("-")
      } {
        parser.ws_cmt() ;
        true
      } else {
        parser.backtrack_to(start) ;
        false
      }
    } ;

    if let Some(val) = parser.int() {
      let val = if negated {
        parser.ws_cmt() ;
        if parser.tag_opt(")") {
          - val
        } else {
          bail!("illegal integer value, missing closing `)`")
        }
      } else {
        val
      } ;

      Ok( FPVal::Val( val::int(val) ) )

    } else if let Ok(Some(val)) = parser.real() {
      let val = if negated {
        parser.ws_cmt() ;
        if parser.tag_opt(")") {
          - val
        } else {
          bail!("illegal real value, missing closing `)`")
        }
      } else {
        val
      } ;

      Ok( FPVal::Val( val::real(val) ) )

    } else if let Some(val) = parser.bool() {
      debug_assert! { ! negated }

      Ok( FPVal::Val( val::bool(val) ) )

    } else if let Ok( Some(term) ) = parser.term_opt(
      & vec![].into(), & BTreeMap::new(), & Instance::new()
    ) {
      if let Some(val) = term.val() {
        Ok( FPVal::Val(val) )
      } else {
        bail!("cannot turn term into a value: {}", term)
      }

    } else if parser.tag_opt("(") && {
      parser.ws_cmt() ; parser.tag_opt("_")
    } && {
      parser.ws_cmt() ; parser.tag_opt("as-array")
    } {
      // Try function to array conversion.

      debug_assert! { ! negated }
      parser.ws_cmt() ;

      if let Ok((_, ident)) = parser.ident() {
        parser.ws_cmt() ;
        if parser.tag_opt(")") {
          Ok( FPVal::FunToArray( ident.into() ) )
        } else {
          bail!("ill-formed value, missing closing paren")
        }
      } else {
        bail!("expected symbol in function to array conversion `{}`", input)
      }

    } else {
      debug_assert! { ! negated }
      Ok( FPVal::FunDef(input.into()) )
    }
  }
}





/// Extends a solver so that it's able to check clause triviality.
pub trait ClauseTrivialExt {
  /// Checks whether a clause is trivial.
  fn is_clause_trivial(
    & mut self, & mut ::instance::Clause
  ) -> Res< Option<bool> > ;
}

impl<Parser: Copy> ClauseTrivialExt for Solver<Parser> {
  fn is_clause_trivial(
    & mut self, clause: & mut ::instance::Clause
  ) -> Res< Option<bool> > {
    let mut lhs: Vec<Term> = Vec::with_capacity(17) ;

    for term in clause.lhs_terms() {
      match term.bool() {
        Some(true) => (),
        Some(false) => return Ok( Some(true) ),
        _ => {
          let neg = term::not( term.clone() ) ;
          for term in & lhs {
            if neg == * term {
              return Ok( Some(true) )
            }
          }
          lhs.push( term.clone() )
        },
      }
    }

    let mut actlit = None ;

    let res = {

      let conj = SmtConj::new( lhs.iter(), & clause.vars ) ;

      if clause.rhs().is_none() && clause.lhs_preds().is_empty() {
        if conj.has_fun_apps {
          actlit = Some( self.get_actlit() ? )
        }

        // Either it is trivial, or falsifiable regardless of the predicates.
        if conj.is_unsat( self, actlit.as_ref() ) ? {
          Ok( Some(true) )
        } else {
          Ok(None)
        }

      } else {

        if let Some((pred, args)) = clause.rhs() {
          if clause.lhs_preds().get(& pred).map(
            |set| set.contains(args)
          ).unwrap_or(false) {
            return Ok( Some(true) )
          }
        }

        if lhs.is_empty() {
          Ok( Some(false) )
        } else {

          if conj.has_fun_apps {
            actlit = Some( self.get_actlit() ? )
          }
          conj.is_unsat( self, actlit.as_ref() ).map(Some)
        }

      }
    } ;

    if let Some(actlit) = actlit {
      self.de_actlit(actlit) ?
    }

    clause.lhs_terms_checked() ;

    res
  }
}
