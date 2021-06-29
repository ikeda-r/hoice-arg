//! ICE learner.
//!
//! The ICE learner implements the learning from [the original paper]. The learner is meant to run
//! in parallel alongside the teacher. It receives [`LrnData`] from the teacher from which it
//! constructs candidates for all predicates mentioned.
//!
//! # Data Projection
//!
//! The first step towards producing candidates is to project the learning onto the different
//! predicates. The learner stores the learning data received from the teacher so that it can
//! remember the constraints between unclassified data points. The projection yields a [`CData`]
//! for each predicate.
//!
//! Next, the learner decides which predicate to handle first. This is based on the number of
//! classified/unclassified data available for each predicate and uses [`cmp_data_metrics`]. This
//! step is not systematic, it only triggers a certain percent of the times, controlled by
//! [`IceConf`]'s [`sort_preds`] field. This is yet another mechanism to break the bias introduced
//! by sorting the predicates.
//!
//! # Learning a Single Candidate
//!
//! Once it has chosen a predicate to work on, the learner breaks the corresponding `CData` into a
//! decision tree by repeatedly choosing qualifiers. These choices are based on either the notion
//! of gain introduced in [the original paper], or the pure ICE version of gain that ignores
//! unclassified data when it makes sense. This last gain computation technique is called `simple`
//! gain in the code. Simple gain triggers when legal (there is positive *and* negative data),
//! under some probability specified by [`IceConf`]'s [`simple_gain_ratio`] field.
//!
//! Given the original projected data for some predicate, then after the first split there is
//! usually more than one sub-(split-)data the learner can work on. The learner decides which one
//! it will look at next by using a criteria similar to the one used to select which predicate to
//! run on first ([`cmp_data_metrics`]).
//!
//! If no qualifier can split the current `CData`, the learner runs [synthesis] to create new ones.
//!
//! # Sending Candidates
//!
//! Once it has created a candidate for each predicate, the learner aggregates everything and sends
//! it to the teacher. It then waits for more learning data or an exit message.
//!
//! [the original paper]: https://link.springer.com/chapter/10.1007/978-3-319-89960-2_20
//! (Original higher-order ICE framework)
//! [`LrnData`]: ../../data/LrnData (LrnData struct)
//! [`CData`]: data/struct.CData.html (CData struct)
//! [`IceConf`]: ../../common/config/struct.IceConf.html (IceConf struct)
//! [`sort_preds`]: ../../common/config/struct.IceConf.html#structfield.sort_preds
//! (sort_pred field for IceConf)
//! [`simple_gain_ratio`]: ../../common/config/struct.IceConf.html#structfield.simple_gain_ratio
//! (simple_gain_ratio field for IceConf)
//! [synthesis]: synth/index.html (ICE's synth module)
//! [`cmp_data_metrics`]: ../../common/fn.cmp_data_metrics.html (cmp_data_metrics function)

use crate::{
    common::{
        msg::*,
        smt::{SmtActSamples, SmtConstraint, SmtSample},
        var_to::vals::VarValsMap,
        *,
    },
    data::LrnData,
};

pub mod data;
pub mod quals;
pub mod synth;

use self::data::CData;
use self::quals::NuQuals;
use self::synth::SynthSys;

/// Launcher.
pub struct Launcher;
unsafe impl Sync for Launcher {}
unsafe impl Send for Launcher {}

impl Launcher {
    /// Launches an smt learner.
    pub fn launch(core: &MsgCore, instance: Arc<Instance>, data: LrnData, mine: bool) -> Res<()> {
        let mut learner = IceLearner::new(&core, instance, data, mine)
            .chain_err(|| "while creating ice learner")?;
        let res = learner.run();
        learner.finalize()?;
        res
    }
}

impl Learner for Launcher {
    fn run(&self, core: MsgCore, instance: Arc<Instance>, data: LrnData, mine: bool) {
        match Self::launch(&core, instance, data, mine) {
            Ok(()) => core.exit(),
            Err(e) => core.err(e),
        }
    }
    fn description(&self, mine: bool) -> String {
        format!("ice{}", if mine { "" } else { " pure synth" })
    }
}

/// A branch of a decision tree.
///
/// Boolean is `false` if the term should be negated.
pub type Branch = Vec<(Term, bool)>;

/// Ice learner.
///
/// Created and launched by the teacher. This type is equipped with a [`MsgCore`] to communicate
/// with the teacher.
///
/// The ICE learner receives learning data from the teacher and builds a decision tree for each
/// predicate, which yields candidates for the predicates that respect the learning data.
///
/// [`MsgCore`]: ../../common/msg/struct.MsgCore.html (MsgCore struct)
pub struct IceLearner<'core> {
    /// Arc to the instance.
    pub instance: Arc<Instance>,
    /// Qualifiers for the predicates.
    pub qualifiers: NuQuals,
    /// Synthesizer.
    synth_sys: PrdMap<SynthSys>,
    /// Current data.
    data: LrnData,
    /// Solver used to check if the constraints are respected.
    solver: Solver<()>,
    /// Learner core.
    core: &'core MsgCore,
    /// Branches of the tree, used when constructing a decision tree.
    finished: Vec<Branch>,
    /// Branches to construct later, used when constructing a decision tree.
    unfinished: Vec<(Branch, CData)>,
    /// Classifier for constraint data.
    classifier: VarValsMap<bool>,
    /// Declaration memory: used when declaring samples in the solver to
    /// remember what's already declared. The `u64` is the sample's uid.
    dec_mem: PrdMap<HashSet<u64>>,
    /// Current candidate, cleared at the beginning of each learning phase.
    candidate: PrdMap<Option<Term>>,
    /// Vector used during learning, avoids re-allocation.
    predicates: Vec<(usize, usize, PrdIdx)>,
    /// Rng to decide when to sort predicates.
    sort_rng_1: Rng,
    /// Rng actually doing the predicate sorting.
    sort_rng_2: Rng,
    /// Rng to decide when to use simple gain.
    simple_rng: Rng,
    /// Rng to decide when skip preliminary.
    pre_skip_rng: Rng,
    /// Luby counter for restarts.
    luby: Option<LubyCount>,
    /// Known qualifiers, factored for no reallocation. Used by synthesis.
    known_quals: TermSet,
    /// Gain pivot.
    gain_pivot: f64,
    /// Gain pivot synth.
    gain_pivot_synth: Option<f64>,
    /// Learn step counter.
    count: usize,
}
impl<'core> IceLearner<'core> {
    /// Ice learner constructor.
    pub fn new(
        core: &'core MsgCore,
        instance: Arc<Instance>,
        data: LrnData,
        mine: bool, // synth_solver: Slver
    ) -> Res<Self> {
        let solver = conf.solver.spawn("ice_learner", (), &instance)?;

        profile! { |core._profiler| tick "mining" }
        let qualifiers =
            NuQuals::new(&instance, mine).chain_err(|| "while creating qualifier structure")?;
        profile! { |core._profiler| mark "mining" }

        let dec_mem = vec![HashSet::with_capacity(103); instance.preds().len()].into();
        let candidate = vec![None; instance.preds().len()].into();
        let predicates = Vec::with_capacity(instance.preds().len());

        let mut synth_sys = PrdMap::with_capacity(instance.preds().len());
        for (pred, _) in instance.preds().index_iter() {
            synth_sys.push(SynthSys::new(&instance[pred].sig))
        }

        let mut using_rec_funs = false;

        fun::iter(|_| {
            using_rec_funs = true;
            Ok(())
        })?;

        let (gain_pivot, gain_pivot_synth) = if false && using_rec_funs {
            (0.4f64, Some(0.4f64))
        } else {
            (conf.ice.gain_pivot, conf.ice.gain_pivot_synth)
        };

        use rand::SeedableRng;

        Ok(IceLearner {
            instance,
            qualifiers,
            data,
            solver, // synth_solver,
            synth_sys,
            core,
            finished: Vec::with_capacity(103),
            unfinished: Vec::with_capacity(103),
            classifier: VarValsMap::with_capacity(1003),
            dec_mem,
            candidate,
            predicates,
            sort_rng_1: { Rng::from_seed([42; 16]) },
            sort_rng_2: { Rng::from_seed([79; 16]) },
            simple_rng: { Rng::from_seed([107; 16]) },
            pre_skip_rng: { Rng::from_seed([245; 16]) },
            luby: if mine { None } else { Some(LubyCount::new()) },
            known_quals: TermSet::new(),
            gain_pivot,
            gain_pivot_synth,
            count: 0,
        })
    }

    /// Returns true if all qualifiers should be wiped out.
    fn restart(&mut self) -> bool {
        self.luby.as_mut().map(|l| l.inc()).unwrap_or(false)
    }

    /// Runs the learner.
    pub fn run(&mut self) -> Res<()> {
        profile! { self "quals synthesized" => add 0 }
        profile! {
          self "quals initially" =>
            add self.qualifiers.real_qual_count()
        }

        loop {
            match profile! (
              |self.core._profiler| wrap { self.recv() } "waiting"
            ) {
                Ok(data) => {
                    self.count += 1;
                    if self.count % 50 == 0 {
                        smt::reset(&mut self.solver, &self.instance)?
                    }
                    profile! { self "learn steps" => add 1 }
                    if let Some(candidates) = profile!(
                      |self.core._profiler| wrap {
                        self.solver.push(1) ? ;
                        let res = self.learn(data) ;
                        self.solver.pop(1) ? ;
                        res
                      } "learning"
                    )? {
                        self.send_cands(candidates)
                            .chain_err(|| "while sending candidates")?;
                        if self.restart() {
                            profile! { self "restarts" => add 1 }
                            self.qualifiers.wipe()
                        }
                    } else {
                        return Ok(());
                    }
                }
                Err(e) => bail!(e),
            }
        }
    }

    /// Finalizes the learning process and exits.
    #[cfg(not(feature = "bench"))]
    pub fn finalize(mut self) -> Res<()> {
        let _ = self.solver.kill();
        profile! {
          self "quals once done" => add self.qualifiers.real_qual_count()
        }
        Ok(())
    }
    #[cfg(feature = "bench")]
    pub fn finalize(mut self) -> Res<()> {
        let _ = self.solver.kill();
        Ok(())
    }

    /// Sends some candidates.
    ///
    /// Also resets the solver and clears declaration memory.
    fn send_cands(&mut self, candidates: Candidates) -> Res<()> {
        profile!(
            | self._profiler | wrap {
                self.send_candidates(candidates)
            } "sending"
        )?;
        // // Reset and clear declaration memory.
        // smt::reset(& mut self.solver).chain_err(
        //   || "during solver reset"
        // ) ? ;
        for set in self.dec_mem.iter_mut() {
            set.clear()
        }
        Ok(())
    }

    /// Looks for a classifier.
    ///
    /// Returns `None` if asked to exit.
    pub fn learn(&mut self, mut data: LrnData) -> Res<Option<Candidates>> {
        use rand::Rng;

        ::std::mem::swap(&mut data, &mut self.data);
        self.core.merge_set_prof("data", data.destroy());

        if self.count % conf.ice.gain_pivot_mod == 0 {
            self.gain_pivot += conf.ice.gain_pivot_inc;
            if self.gain_pivot > 0.999 {
                self.gain_pivot = 0.999
            }
            if let Some(gain_pivot_synth) = self.gain_pivot_synth.as_mut() {
                *gain_pivot_synth += conf.ice.gain_pivot_inc;
                if *gain_pivot_synth > 0.999 {
                    *gain_pivot_synth = 0.999
                }
            }
        }

        if conf.ice.qual_print {
            self.qualifiers.log()
        }

        let contradiction = profile!(
            |self.core._profiler| wrap {
                self.setup_solver().chain_err(
                    || "while initializing the solver"
                )
            } "learning", "setup"
        )?;

        if contradiction {
            unsat!("by contradiction in ICE solver")
        }

        self.check_exit()?;

        debug_assert! {
            scoped! {
                let mut okay = true ;
                for term_opt in & self.candidate {
                    okay = okay && term_opt.is_none() ;
                }
                okay
            }
        }

        // Decide whether to use simple gain.
        let simple = conf.ice.simple_gain_ratio >= self.simple_rng.gen();
        // Decide whether to sort the predicates.
        let sorted = conf.ice.sort_preds >= self.sort_rng_1.gen();
        // Skip preliminary decision 20% of the time.
        let skip_prelim = 0.20 >= self.pre_skip_rng.gen();

        msg! { @verb
            self =>
            "starting learning\n  \
            simple:      {},\n  \
            sorted:      {},\n  \
            skip_prelim: {},",
            simple, sorted, skip_prelim
        }

        self.predicate_stats(skip_prelim)?;

        self.check_exit()?;

        if simple {
            profile! { self "simple" => add 1 }
        }

        self.sort_predicates(sorted)?;

        self.check_exit()?;

        while let Some((_unc, _cla, pred)) = self.predicates.pop() {
            msg! {
                debug self =>
                "{}: {} unclassified, {} classified",
                self.instance[pred], _unc, _cla
            }

            let data = profile!(
                |self.core._profiler| wrap {
                    self.data.data_of(pred)
                } "learning", "data"
            );
            self.check_exit()?;

            if let Some(term) = self.pred_learn(pred, data, simple)? {
                self.candidate[pred] = Some(term)
            } else {
                return Ok(None);
            }
            self.check_exit()?;
        }

        let mut candidates: PrdMap<_> = vec![None; self.instance.preds().len()].into();

        ::std::mem::swap(&mut candidates, &mut self.candidate);

        Ok(Some(candidates))
    }

    /// Prepares the predicates for sorting.
    fn predicate_stats(&mut self, skip_prelim: bool) -> Res<()> {
        debug_assert! { self.predicates.is_empty() }

        let mut stuff_changed = true;

        while stuff_changed {
            stuff_changed = false;
            self.predicates.clear();

            for pred in self.instance.pred_indices() {
                if self.instance[pred].is_defined() || self.candidate[pred].is_some() {
                    continue;
                }

                let pos_len = self.data.pos[pred].len();
                let neg_len = self.data.neg[pred].len();
                let unc_len = self.data.map()[pred].len();

                if !skip_prelim {
                    if pos_len == 0 && neg_len > 0 {
                        msg! { debug self => "legal_pred (1)" }
                        // Maybe we can assert everything as negative right away?
                        if self.force_if_legal(pred, false)? {
                            msg! { @verb
                                self =>
                                "{} only has negative ({}) and unclassified ({}) data\n\
                                legal check ok, assuming everything negative",
                                self.instance[pred], neg_len, unc_len
                            }
                            self.candidate[pred] = Some(term::fls());
                            profile!(
                                |self.core._profiler| wrap {
                                    self.data.force_pred(pred, false).chain_err(
                                        || format!(
                                            "while setting all false for {}", self.instance[pred]
                                        )
                                    )
                                } "learning", "data"
                            )?;
                            stuff_changed = true;
                            continue;
                        }
                    }

                    if neg_len == 0 && pos_len > 0 {
                        msg! { debug self => "legal_pred (2)" }
                        // Maybe we can assert everything as positive right away?
                        if self.force_if_legal(pred, true)? {
                            msg! { @verb
                                self =>
                                "{} only has positive ({}) and unclassified ({}) data\n\
                                legal check ok, assuming everything positive",
                                self.instance[pred], pos_len, unc_len
                            }
                            self.candidate[pred] = Some(term::tru());
                            profile!(
                                |self.core._profiler| wrap {
                                    self.data.force_pred(pred, true).chain_err(
                                        || format!(
                                            "while setting all true for {}", self.instance[pred]
                                        )
                                    )
                                } "learning", "data"
                            )?;
                            stuff_changed = true;
                            continue;
                        }
                    }
                }

                self.predicates.push((unc_len, pos_len + neg_len, pred))
            }
        }

        Ok(())
    }

    /// Sorts predicates.
    ///
    /// Randomly if `!sorted`, based on the amount of (un)classified data otherwise.
    fn sort_predicates(&mut self, sorted: bool) -> Res<()> {
        profile! { self tick "learning", "predicate sorting" }
        if sorted {
            // The iteration starts from the end of `predicates`. The first
            // predicates we want to synthesize should be last.
            self.predicates
                .sort_unstable_by(|&(unc_1, sum_1, _p_1), &(unc_2, sum_2, _p_2)| {
                    cmp_data_metrics(sum_1, unc_1, sum_2, unc_2)
                });
        } else {
            // Not sorting, forcing random order.
            let sort_rng = &mut self.sort_rng_2;
            self.predicates.sort_unstable_by(|_, _| {
                use rand::Rng;
                use std::cmp::Ordering::*;

                let rand: f64 = sort_rng.gen();
                if rand <= 0.33 {
                    Less
                } else if rand <= 0.66 {
                    Equal
                } else {
                    Greater
                }
            })
        }
        profile! { self mark "learning", "predicate sorting" }

        Ok(())
    }

    /// Chooses a branch to go into next.
    ///
    /// Updates the data in the branches.
    pub fn choose_branch(&mut self, pred: PrdIdx) -> Option<(Branch, CData)> {
        profile! { self tick "learning", "choose branch" }

        let mut best = None;

        for n in 0..self.unfinished.len() {
            let data = &mut self.unfinished[n].1;
            self.data.classify(pred, data);
            let (classified, unknown) = (data.pos().len() + data.neg().len(), data.unc().len());
            best = if let Some((idx, cla, unk)) = best {
                use std::cmp::Ordering::*;
                match cmp_data_metrics(classified, unknown, cla, unk) {
                    Greater => Some((n, classified, unknown)),
                    _ => Some((idx, cla, unk)),
                }
            } else {
                Some((n, classified, unknown))
            }
        }

        profile! { self mark "learning", "choose branch" }

        if let Some((index, _, _)) = best {
            Some(self.unfinished.swap_remove(index))
        } else {
            None
        }
    }

    /// Looks for a classifier for a given predicate.
    pub fn pred_learn(&mut self, pred: PrdIdx, data: CData, simple: bool) -> Res<Option<Term>> {
        debug_assert!(self.finished.is_empty());
        debug_assert!(self.unfinished.is_empty());
        self.classifier.clear();

        msg! { @verb
            self =>
            "working on predicate {} (pos: {}, neg: {}, unc: {})",
            self.instance[pred], data.pos().len(), data.neg().len(), data.unc().len()
        }

        use rand::Rng;
        let mut rng = rand::thread_rng();
        let b: bool = rng.gen();
        if conf.ice.datagen {
            if (data.pos().len() > 0 && b) || data.neg().len() == 0 {
                let mut or_args = Vec::with_capacity(100);
                for sample in data.pos() {
                    let args = sample.get();
                    // let n = args.len() - 1;
                    let mut i = 0;
                    let mut and_args = Vec::with_capacity(100);
                    for val in args.iter() {
                        if let Some(term1) = val.to_term() {
                            let v;
                            if term1.typ().is_int() {
                                v = term::int_var(i)
                            } else {
                                if term1.typ().is_bool() {
                                    v = term::bool_var(i)
                                } else {
                                    v = term::real_var(i)
                                }
                            }
                            let term = term::eq(v, term1);
                            and_args.push(term);
                        } else {
                        };
                        i = i + 1;
                    }
                    let term2 = term::and(and_args);
                    //println!("pred for {}: {}", pred, term2);
                    or_args.push(term2);
                }
                return Ok(Some(term::or(or_args)));
            } else {
                let mut and_args = Vec::with_capacity(100);
                for sample in data.neg() {
                    let args = sample.get();
                    // let n = args.len() - 1;
                    let mut i = 0;
                    let mut or_args2 = Vec::with_capacity(100);
                    for val in args.iter() {
                        if let Some(term1) = val.to_term() {
                            let v;
                            if term1.typ().is_int() {
                                v = term::int_var(i)
                            } else {
                                if term1.typ().is_bool() {
                                    v = term::bool_var(i)
                                } else {
                                    v = term::real_var(i)
                                }
                            }
                            let term = term::not(term::eq(v, term1));
                            or_args2.push(term);
                        } else {
                        };
                        i = i + 1;
                    }
                    let term2 = term::or(or_args2);
                    //println!("pred for {}: {}", pred, term2);
                    and_args.push(term2);
                }
                return Ok(Some(term::and(and_args)));
            }
        };

        self.unfinished.push((vec![], data));

        'learning: while let Some((mut branch, data)) = self.choose_branch(pred) {
            self.check_exit()?;

            let branch_is_empty = branch.is_empty();

            // Checking whether we can close this branch.
            let data = if let Some(data) = self.try_force_all(pred, data, true)? {
                data
            } else if branch_is_empty {
                debug_assert!(self.finished.is_empty());
                debug_assert!(self.unfinished.is_empty());
                return Ok(Some(term::tru()));
            } else {
                branch.shrink_to_fit();
                self.finished.push(branch);
                continue 'learning;
            };

            let data = if let Some(data) = self.try_force_all(pred, data, false)? {
                data
            } else if branch_is_empty {
                debug_assert!(self.finished.is_empty());
                debug_assert!(self.unfinished.is_empty());
                return Ok(Some(term::fls()));
            } else {
                continue 'learning;
            };

            self.check_exit()?;

            // Could not close the branch, look for a qualifier.
            let res = profile!(
                self wrap {
                    self.get_qualifier(pred, data, simple)
                } "learning", "qual"
            );

            let (qual, q_data, nq_data) = if let Some(res) = res? {
                res
            } else {
                return Ok(None);
            };

            // Remember the branch where qualifier is false.
            let mut nq_branch = branch.clone();
            nq_branch.push((qual.clone(), false));
            self.unfinished.push((nq_branch, nq_data));

            // Remember the branch where qualifier is true.
            branch.push((qual, true));
            self.unfinished.push((branch, q_data))
        }

        profile! { self tick "learning", "pred finalize" }
        debug_assert!(self.unfinished.is_empty());
        let mut or_args = Vec::with_capacity(self.finished.len());
        for branch in self.finished.drain(0..) {
            let mut and_args = Vec::with_capacity(branch.len());
            for (term, pos) in branch {
                let term = if pos { term } else { term::not(term) };
                and_args.push(term)
            }
            or_args.push(term::and(and_args))
        }
        profile! { self mark "learning", "pred finalize" }
        Ok(Some(term::or(or_args)))
    }

    /// Prepares the solver to check that constraints are respected.
    ///
    /// Returns `true` if a contradiction was found.
    ///
    /// - **does not** reset the solver or clean declaration memory (must be done before sending
    ///   previous candidates)
    /// - **defines** pos (neg) data as `true` (`false`)
    /// - **declares** samples that neither pos nor neg
    /// - asserts constraints
    pub fn setup_solver(&mut self) -> Res<bool> {
        // Positive data.
        self.solver.comment("Positive data:")?;
        for (pred, set) in self.data.pos.index_iter() {
            for sample in set.iter() {
                let is_new = self.dec_mem[pred].insert(sample.uid());
                debug_assert!(is_new);
                self.solver.define_const(
                    &SmtSample::new(pred, sample),
                    typ::bool().get(),
                    &"true",
                )?
            }
        }
        // Negative data.
        self.solver.comment("Negative data:")?;
        for (pred, set) in self.data.neg.index_iter() {
            for sample in set.iter() {
                let is_new = self.dec_mem[pred].insert(sample.uid());
                if !is_new {
                    // Contradiction found.
                    return Ok(true);
                }
                self.solver.define_const(
                    &SmtSample::new(pred, sample),
                    typ::bool().get(),
                    &"false",
                )?
            }
        }

        self.solver
            .comment("Sample declarations for constraints:")?;
        // Declare all samples used in constraints.
        for (pred, map) in self.data.map().index_iter() {
            // if let Some(term) = self.instance.term_of(pred) {
            //   if term.is_true() {
            //     self.solver.comment(
            //       & format!(
            //         "Predicate {} is forced to be `true`:", self.instance[pred]
            //       )
            //     ) ? ;
            //     for (sample, _) in map.read().map_err(corrupted_err)?.iter() {
            //       let uid = sample.uid() ;
            //       if ! self.dec_mem[pred].contains(& uid) {
            //         let _ = self.dec_mem[pred].insert(uid) ;
            //         self.solver.define_fun(
            //           & SmtSample(pred, sample), & args, & Typ::Bool, & "true", & ()
            //         ) ?
            //       }
            //     }
            //   } else {
            //     bail!(
            //       "predicate {} is forced to {}, unsupported for now",
            //       self.instance[pred], term
            //     )
            //   }
            // } else {
            for (sample, _) in map.iter() {
                let uid = sample.uid();
                if !self.dec_mem[pred].contains(&uid) {
                    let _ = self.dec_mem[pred].insert(uid);
                    self.solver
                        .declare_const(&SmtSample::new(pred, sample), &typ::RTyp::Bool)?
                }
            }
            // }
        }

        self.solver.comment("Constraints:")?;
        // Assert all constraints.
        for constraint in self.data.constraints.iter() {
            if !constraint.is_tautology() {
                self.solver.assert(&SmtConstraint::new(constraint))?
            }
        }

        Ok(false)
    }
}

/// Functions dealing with forcing some data to positive/negative.
impl<'core> IceLearner<'core> {
    /// Tries to force some data to positive/negative for some predicate.
    ///
    /// Input `pos` specifies whether the data should be forced positive or negative.
    ///
    /// Returns `None` if everything was forced successfully.
    ///
    /// ```rust
    /// use std::sync::mpsc::channel;
    /// use hoice::{ learning::ice::IceLearner, common::*, data::Data, var_to::vals::RVarVals };
    /// let ((s_1, _), (_, r_2)) = (channel(), channel());
    /// let core = msg::MsgCore::new_learner(0.into(), s_1, r_2);
    /// let instance = Arc::new( ::hoice::parse::mc_91() );
    /// let pred: PrdIdx = 0.into();
    /// let mut data = Data::new( instance.clone() );
    ///
    /// // Adding sample `(mc_91 0 0)` as positive.
    /// data.add_data(0.into(), vec![], Some((
    ///     pred, RVarVals::of_pred_model(instance[pred].sig(), vec![
    ///         (0.into(), (), val::int(0)), (1.into(), (), val::int(0))
    ///     ], false).unwrap()
    /// ))).expect("while adding first positive sample");
    /// // Adding `(mc_91 1 0) => (mc_91 0 1)`.
    /// data.add_data(
    ///     0.into(), vec![
    ///         (pred, RVarVals::of_pred_model(instance[pred].sig(), vec![
    ///             (0.into(), (), val::int(1)), (1.into(), (), val::int(0)),
    ///         ], false).unwrap())
    ///     ], Some((
    ///         pred, RVarVals::of_pred_model(instance[pred].sig(), vec![
    ///             (0.into(), (), val::int(0)), (1.into(), (), val::int(1))
    ///         ], false).unwrap()
    ///     ))
    /// ).expect("while adding first implication");
    /// let lrn_data = data.to_lrn_data();
    /// let mut learner = IceLearner::new(
    ///     &core, instance.clone(), lrn_data.clone(), true
    /// ).expect("while creating learner");
    /// learner.setup_solver().unwrap();
    /// assert! {
    ///     learner.try_force_all(pred, lrn_data.data_of(pred), true).expect(
    ///         "during first try force all"
    ///     ).is_none() // Success.
    /// }
    ///
    /// // Adding `(mc_91 1 0) and (mc_91 2 0) => false`.
    /// data.add_data(
    ///     0.into(), vec![
    ///         (pred, RVarVals::of_pred_model(instance[pred].sig(), vec![
    ///             (0.into(), (), val::int(1)), (1.into(), (), val::int(0)),
    ///         ], false).unwrap()),
    ///         (pred, RVarVals::of_pred_model(instance[pred].sig(), vec![
    ///             (0.into(), (), val::int(2)), (1.into(), (), val::int(0)),
    ///         ], false).unwrap()),
    ///     ], None
    /// ).expect("while adding second implication");
    /// let lrn_data = data.to_lrn_data();
    /// let mut learner = IceLearner::new(
    ///     &core, instance, lrn_data.clone(), true
    /// ).expect("while creating learner");
    /// learner.setup_solver().unwrap();
    /// assert! {
    ///     learner.try_force_all(pred, lrn_data.data_of(pred), true).expect(
    ///         "during first try force all"
    ///     ).is_some() // Failed.
    /// }
    /// ```
    pub fn try_force_all(&mut self, pred: PrdIdx, data: CData, pos: bool) -> Res<Option<CData>> {
        let forcing = if pos {
            // No more negative data?
            data.neg().is_empty()
        } else {
            // No more positive data?
            data.pos().is_empty()
        };

        let polarity = || if pos { "positive" } else { "negative" };

        if forcing
            && self
                .force_legal(pred, data.unc(), pos)
                .chain_err(|| format!("while checking possibility of assuming {}", polarity()))?
        {
            if_verb! {
                let mut s = format!(
                    "  no more {} data, force_legal check ok\n  \
                    forcing {} unclassified(s) {}...",
                    if !pos { "positive" } else { "negative" },
                    data.unc().len(),
                    if pos { "positive" } else { "negative" }
                ) ;

                if_debug! {
                    s = format!("{}\n  data:", s) ;
                    s = format!("{}\n    pos {{", s) ;
                    for sample in data.pos() {
                        s = format!("{}\n      {}", s, sample)
                    }
                    s = format!("{}\n    }} neg {{", s) ;
                    for sample in data.neg() {
                        s = format!("{}\n      {}", s, sample)
                    }
                    s = format!("{}\n    }} unc {{", s) ;
                    for sample in data.unc() {
                        s = format!("{}\n      {}", s, sample)
                    }
                    s = format!("{}\n    }}", s) ;
                }
                msg! { self => s }
            }

            let (_, _, unc) = data.destroy();

            profile!(
                |self.core._profiler| wrap {
                    if pos {
                        for unc in unc {
                            self.data.add_pos(pred, unc) ;
                        }
                    } else {
                        for unc in unc {
                            self.data.add_neg(pred, unc) ;
                        }
                    }
                    self.data.propagate()
                } "learning", "data"
            )?;

            Ok(None)
        } else {
            Ok(Some(data))
        }
    }

    /// Checks whether assuming some data as positive (if `pos` is true, negative otherwise) is
    /// legal.
    ///
    /// Used by [`try_force_all`].
    ///
    /// **NB**: if assuming the data positive / negative is legal, the data will be forced to be
    /// positive / negative in the solver automatically. Otherwise, the solver is put back in the
    /// same state it was before.
    ///
    /// [`try_force_all`]: #method.try_force_all (try_force_all function)
    fn force_legal(&mut self, pred: PrdIdx, unc: &[VarVals], pos: bool) -> Res<bool> {
        if unc.is_empty() {
            return Ok(true);
        }
        profile! { self tick "learning", "smt", "legal" }

        // Wrap actlit and increment counter.
        let samples = SmtActSamples::new(&mut self.solver, pred, unc, pos)?;
        self.solver.assert(&samples)?;

        let legal = if self.solver.check_sat_act(Some(&samples.actlit))? {
            profile! { self mark "learning", "smt", "legal" }
            true
        } else {
            profile! { self mark "learning", "smt", "legal" }
            false
        };

        samples.force(&mut self.solver, legal)?;

        Ok(legal)
    }

    /// Checks whether assuming **all** the unclassified data from a predicate as `pos` is legal.
    ///
    /// **NB**: if assuming the data positive / negative is legal, the data will be forced to be
    /// positive / negative in the solver automatically. Otherwise, the solver is put back in the
    /// same state it was before the call.
    ///
    /// # Examples
    ///
    /// Forcing data to positive.
    ///
    /// ```rust
    /// use std::sync::mpsc::channel;
    /// use hoice::{ learning::ice::IceLearner, common::*, data::Data, var_to::vals::RVarVals };
    /// let ((s_1, _), (_, r_2)) = (channel(), channel());
    /// let core = msg::MsgCore::new_learner(0.into(), s_1, r_2);
    /// let instance = Arc::new( ::hoice::parse::mc_91() );
    /// let pred: PrdIdx = 0.into();
    /// let mut data = Data::new( instance.clone() );
    ///
    /// // Adding sample `(mc_91 0 0)` as positive.
    /// data.add_data(0.into(), vec![], Some((
    ///     pred, RVarVals::of_pred_model(instance[pred].sig(), vec![
    ///         (0.into(), (), val::int(0)), (1.into(), (), val::int(0))
    ///     ], false).unwrap()
    /// ))).expect("while adding first positive sample");
    /// // Adding `(mc_91 1 0) => (mc_91 0 1)`.
    /// data.add_data(
    ///     0.into(), vec![
    ///         (pred, RVarVals::of_pred_model(instance[pred].sig(), vec![
    ///             (0.into(), (), val::int(1)), (1.into(), (), val::int(0)),
    ///         ], false).unwrap())
    ///     ], Some((
    ///         pred, RVarVals::of_pred_model(instance[pred].sig(), vec![
    ///             (0.into(), (), val::int(0)), (1.into(), (), val::int(1))
    ///         ], false).unwrap()
    ///     ))
    /// ).expect("while adding first implication");
    /// let lrn_data = data.to_lrn_data();
    /// let mut learner = IceLearner::new(
    ///     &core, instance.clone(), lrn_data.clone(), true
    /// ).expect("while creating learner");
    /// learner.setup_solver().unwrap();
    /// assert! {
    ///     learner.force_if_legal(pred, true).expect(
    ///         "during first try force all"
    ///     ) // Success.
    /// }
    ///
    /// // Adding `(mc_91 1 0) and (mc_91 2 0) => false`.
    /// data.add_data(
    ///     0.into(), vec![
    ///         (pred, RVarVals::of_pred_model(instance[pred].sig(), vec![
    ///             (0.into(), (), val::int(1)), (1.into(), (), val::int(0)),
    ///         ], false).unwrap()),
    ///         (pred, RVarVals::of_pred_model(instance[pred].sig(), vec![
    ///             (0.into(), (), val::int(2)), (1.into(), (), val::int(0)),
    ///         ], false).unwrap()),
    ///     ], None
    /// ).expect("while adding second implication");
    /// let lrn_data = data.to_lrn_data();
    /// let mut learner = IceLearner::new(
    ///     &core, instance, lrn_data.clone(), true
    /// ).expect("while creating learner");
    /// learner.setup_solver().unwrap();
    /// assert! {
    ///     !learner.force_if_legal(pred, true).expect(
    ///         "during second try force all"
    ///     ) // Failed.
    /// }
    /// ```
    ///
    /// Forcing data to negative.
    ///
    ///
    /// ```rust
    /// use std::sync::mpsc::channel;
    /// use hoice::{ learning::ice::IceLearner, common::*, data::Data, var_to::vals::RVarVals };
    /// let ((s_1, _), (_, r_2)) = (channel(), channel());
    /// let core = msg::MsgCore::new_learner(0.into(), s_1, r_2);
    /// let instance = Arc::new( ::hoice::parse::mc_91() );
    /// let pred: PrdIdx = 0.into();
    /// let mut data = Data::new( instance.clone() );
    ///
    /// // Adding sample `(mc_91 0 0)` as negative.
    /// data.add_data(0.into(), vec![(
    ///     pred, RVarVals::of_pred_model(instance[pred].sig(), vec![
    ///         (0.into(), (), val::int(0)), (1.into(), (), val::int(0))
    ///     ], false).unwrap()
    /// )], None).expect("while adding first positive sample");
    /// // Adding `(mc_91 1 0) and (mc_91 2 0) => false`.
    /// data.add_data(
    ///     0.into(), vec![
    ///         (pred, RVarVals::of_pred_model(instance[pred].sig(), vec![
    ///             (0.into(), (), val::int(1)), (1.into(), (), val::int(0)),
    ///         ], false).unwrap()),
    ///         (pred, RVarVals::of_pred_model(instance[pred].sig(), vec![
    ///             (0.into(), (), val::int(2)), (1.into(), (), val::int(0)),
    ///         ], false).unwrap()),
    ///     ], None
    /// ).expect("while adding first implication");
    /// let lrn_data = data.to_lrn_data();
    /// let mut learner = IceLearner::new(
    ///     &core, instance.clone(), lrn_data.clone(), true
    /// ).expect("while creating learner");
    /// learner.setup_solver().unwrap();
    /// assert! {
    ///     learner.force_if_legal(pred, false).expect(
    ///         "during first try force all"
    ///     ) // Success.
    /// }
    ///
    /// // Adding `(mc_91 1 0) => (mc_91 0 1)`.
    /// data.add_data(
    ///     0.into(), vec![
    ///         (pred, RVarVals::of_pred_model(instance[pred].sig(), vec![
    ///             (0.into(), (), val::int(1)), (1.into(), (), val::int(0)),
    ///         ], false).unwrap())
    ///     ], Some((
    ///         pred, RVarVals::of_pred_model(instance[pred].sig(), vec![
    ///             (0.into(), (), val::int(0)), (1.into(), (), val::int(1))
    ///         ], false).unwrap()
    ///     ))
    /// ).expect("while adding second implication");
    /// let lrn_data = data.to_lrn_data();
    /// let mut learner = IceLearner::new(
    ///     &core, instance, lrn_data.clone(), true
    /// ).expect("while creating learner");
    /// learner.setup_solver().unwrap();
    /// assert! {
    ///     learner.force_if_legal(pred, false).expect(
    ///         "during second try force all"
    ///     ) // Failed.
    /// }
    /// ```
    pub fn force_if_legal(&mut self, pred: PrdIdx, pos: bool) -> Res<bool> {
        profile! { self tick "learning", "smt", "all legal" }
        let unc = &self.data.map()[pred];
        if unc.is_empty() {
            profile! { self mark "learning", "smt", "all legal" }
            return Ok(true);
        }

        // Wrap actlit.
        let samples = SmtActSamples::new(&mut self.solver, pred, unc, pos)?;
        self.solver.assert(&samples)?;

        let legal = if self.solver.check_sat_act(Some(&samples.actlit))? {
            profile! { self mark "learning", "smt", "all legal" }
            true
        } else {
            profile! { self mark "learning", "smt", "all legal" }
            false
        };

        samples.force(&mut self.solver, legal)?;

        Ok(legal)
    }
}

/// Functions dealing with qualifier selection.
impl<'core> IceLearner<'core> {
    /// Looks for a qualifier. Requires a mutable `self` in case it needs to
    /// synthesize a qualifier.
    ///
    /// Be careful when modifying this function as it as a (tail-)recursive call.
    /// The recursive call is logically guaranteed not cause further calls and
    /// terminate right away. Please be careful to preserve this.
    ///
    /// The `simple` flag forces to use simple, unclassified-agnostic gain.
    pub fn get_qualifier(
        &mut self,
        pred: PrdIdx,
        mut data: CData,
        simple: bool,
    ) -> Res<Option<(Term, CData, CData)>> {
        let simple = data.unc().is_empty()
            || (!data.pos().is_empty()
                && !data.neg().is_empty()
                && (simple || data.unc().len() > 3 * (data.pos().len() + data.neg().len())));

        if_debug! {
            let mut s = "data:".to_string() ;
            s = format!("{}\n  pos {{", s) ;
            for sample in data.pos() {
                s = format!("{}\n    {}", s, sample)
            }
            s = format!("{}\n  }} neg {{", s) ;
            for sample in data.neg() {
                s = format!("{}\n    {}", s, sample)
            }
            s = format!("{}\n  }} unc {{", s) ;
            for sample in data.unc() {
                s = format!("{}\n    {}", s, sample)
            }
            s = format!("{}\n  }}", s) ;
            msg! { self => s }
        }

        let mut best_qual = self.get_best_qual(simple, pred, &mut data)?;

        if let Some((qual, gain)) = best_qual {
            best_qual = if gain >= self.gain_pivot && gain > 0.0 {
                msg! { self =>
                    "  using qualifier {}, gain: {} >= {} (simple: {})",
                    qual, gain, self.gain_pivot, simple
                }
                // This qualifier is satisfactory.
                let (q_data, nq_data) = profile!(
                    self wrap { data.split(&qual) } "learning", "qual", "data split"
                );
                return Ok(Some((qual, q_data, nq_data)));
            } else {
                msg! {
                  self =>
                  "  qualifier {} is not good enough, gain: {} < {} (simple: {})",
                  qual, gain, self.gain_pivot, simple
                }
                // Not good enough, maybe synthesis can do better.
                Some((qual, gain))
            }
        }

        if_verb! {
            let mut msg = format!(
                "  could not split remaining data for {}:\n", self.instance[pred]
            ) ;
            msg.push_str("  pos (") ;
            for pos in data.pos() {
                msg.push_str( & format!("\n    {}", pos) )
            }
            msg.push_str("\n  ) neg (") ;
            for neg in data.neg() {
                msg.push_str( & format!("\n    {}", neg) )
            }
            msg.push_str("\n  ) unc (") ;
            for unc in data.unc() {
                msg.push_str( & format!("\n    {}", unc) )
            }
            msg.push_str("\n  )") ;
            msg!{ self => msg } ;
        }

        if data.is_empty() {
            bail!("[bug] cannot synthesize qualifier based on no data")
        }

        self.check_exit()?;

        // Synthesize qualifier separating the data.
        let mut best_synth_qual = None;
        msg! { self => "synthesizing" }

        let res = profile!(
            self wrap {
                self.synthesize(pred, &data, &mut best_synth_qual, simple)
            } "learning", "qual", "synthesis"
        );

        if res?.is_none() {
            return Ok(None);
        }

        let qual = self.choose_qual(best_qual, best_synth_qual)?;

        let (q_data, nq_data) = profile!(
            self wrap { data.split(&qual) } "learning", "qual", "data split"
        );

        Ok(Some((qual, q_data, nq_data)))
    }

    /// Gets the best qualifier available for some data.
    pub fn get_best_qual(
        &mut self,
        simple_gain: bool,
        pred: PrdIdx,
        data: &mut CData,
    ) -> Res<Option<(Term, f64)>> {
        // Run simple if in simple mode.
        if simple_gain {
            profile! {
                self wrap {
                    self.get_best_qual_simple_gain(pred, data)
                } "learning", "qual", "simple gain"
            }
        } else {
            profile! {
                self wrap {
                    self.get_best_qual_normal_gain(pred, data)
                } "learning", "qual", "gain"
            }
        }
    }

    /// Gets the best qualifier based on the simple gain value.
    fn get_best_qual_simple_gain(
        &mut self,
        pred: PrdIdx,
        data: &mut CData,
    ) -> Res<Option<(Term, f64)>> {
        let bias = data.pop_single_sample();
        let core = &self.core;

        self.qualifiers.maximize(pred, bias, |qual| {
            if conf.ice.qual_step {
                let _ = core.msg(format!("evaluating {} (simple gain)", qual));
            }
            let res = data.simple_gain(qual, false)?;
            if conf.ice.qual_step {
                let _ = core.msg(format!(
                    "{}: {}",
                    qual,
                    res.map(|g| format!("{}", g))
                        .unwrap_or_else(|| "none".into())
                ));
                pause_msg(core, "to continue (--qual_step on)");
                ()
            }
            core.check_exit()?;
            Ok(res)
        })
    }

    /// Gets the best qualifier based on the normal (non-simple) gain value.
    fn get_best_qual_normal_gain(
        &mut self,
        pred: PrdIdx,
        data: &mut CData,
    ) -> Res<Option<(Term, f64)>> {
        let core = &self.core;
        let qualifiers = &mut self.qualifiers;
        let all_data = &self.data;

        let bias = data.pop_single_sample();

        qualifiers.maximize(pred, bias, |qual| {
            if conf.ice.qual_step {
                let _ = core.msg(format!("evaluating {} (gain)", qual));
            }
            let res = data.gain(pred, all_data, qual, &core._profiler, false)?;
            if conf.ice.qual_step {
                let _ = core.msg(format!(
                    "; {}: {}",
                    qual,
                    res.map(|g| format!("{}", g))
                        .unwrap_or_else(|| "none".into())
                ));
                pause_msg(core, "to continue (--qual_step on)");
                ()
            }
            core.check_exit()?;
            Ok(res)
        })
    }

    /// Chooses between a qualifier and a synthesized qualifier.
    fn choose_qual(&self, qual: Option<(Term, f64)>, squal: Option<(Term, f64)>) -> Res<Term> {
        let res = match (qual, squal) {
            (Some((qual, gain)), Some((squal, synth_gain))) => {
                if synth_gain > gain {
                    msg! {
                      self =>
                      "using synth qualifier {}, gain {} >= {} (for {})",
                      squal, synth_gain, gain, qual
                    }
                    squal
                } else {
                    msg! {
                      self =>
                      "synth qualifier {} is not good enough, gain: {}\n\
                      using qualifier {} instead, gain: {}",
                      squal, synth_gain, qual, gain
                    }
                    qual
                }
            }
            (None, Some((squal, _synth_gain))) => {
                msg! {
                  self =>
                  "using synth qualifier {}, gain {}", squal, _synth_gain
                }
                squal
            }
            // I think this should be unreachable.
            (Some((qual, _gain)), None) => {
                msg! {
                  self =>
                  "using qualifier {}, gain {}", qual, _gain
                }
                qual
            }
            (None, None) => {
                // let mut msg = format!(
                //   "\ncould not split remaining data for {} after synthesis:\n",
                //   self.instance[pred]
                // ) ;
                // msg.push_str("pos (") ;
                // for pos in data.pos() {
                //   msg.push_str( & format!("\n    {}", pos) )
                // }
                // msg.push_str("\n) neg (") ;
                // for neg in data.neg() {
                //   msg.push_str( & format!("\n    {}", neg) )
                // }
                // msg.push_str("\n) unc (") ;
                // for unc in data.unc() {
                //   msg.push_str( & format!("\n    {}", unc) )
                // }
                // msg.push_str("\n)") ;
                // bail!(msg)
                unknown!("by lack of (synth) qualifier")
            }
        };
        Ok(res)
    }

    /// Qualifier synthesis.
    pub fn synthesize(
        &mut self,
        pred: PrdIdx,
        data: &CData,
        best: &mut Option<(Term, f64)>,
        simple: bool,
    ) -> Res<Option<()>> {
        scoped! {
          let self_data = & self.data ;
          let quals = & mut self.qualifiers ;

          let self_core = & self.core ;
          let known_quals = & mut self.known_quals ;
          // let gain_pivot = self.gain_pivot ;
          let gain_pivot_synth = self.gain_pivot_synth ;
          known_quals.clear() ;

          // println!("synthesizing") ;

          let mut treatment = |term: Term| {
            self_core.check_exit() ? ;
            let is_new = ! quals.quals_of_contains(
              pred, & term
            ) && known_quals.insert(
              term.clone()
            ) ;

            if ! is_new {
              // Term already known, skip.
              Ok(false)
            } else {
              if conf.ice.qual_step || conf.ice.qual_synth_step {
                let _ = self_core.msg(
                  format!("synth evaluating {}", term)
                ) ;
              }
              let gain = if simple {
                data.simple_gain(& term, false) ?
              } else {
                data.gain(
                  pred, self_data, & term, & self_core._profiler, false
                ) ?
              } ;

              if conf.ice.qual_step || conf.ice.qual_synth_step {
                let _ = self_core.msg(
                  format!(
                    "{}: {} (synthesis)", term, gain.map(
                      |gain| format!("{}", gain)
                    ).unwrap_or_else( || "none".into() )
                  )
                ) ;
                pause_msg(self_core, "to continue (--qual_step on)") ;
                ()
              }

              if let Some(gain) = gain {
                // println!("  - {}", gain) ;
                if conf.ice.add_synth && gain >= 1.0 {
                  msg! { self_core => "  adding synth qual {}", term }
                  quals.insert(term.clone(), pred) ? ;
                  ()
                }
                if let Some( (ref mut old_term, ref mut old_gain) ) = * best {
                  let diff = gain - * old_gain ;
                  if diff > ::std::f64::EPSILON {
                    * old_gain = gain ;
                    * old_term = term
                  } else if (* old_gain - gain).abs() < ::std::f64::EPSILON
                  && term::vars(old_term).len() < term::vars(& term).len() {
                    * old_term = term
                  }
                } else {
                  * best = Some((term, gain))
                }

                let stop = gain >= 0.9999
                || if let Some(pivot) = gain_pivot_synth {
                  gain >= pivot
                } else {
                  false
                } ;

                if stop {
                  msg! {
                    self_core =>
                    "  stopping on synth qual {}, gain {}",
                    best.as_ref().unwrap().0, gain
                  }
                }
                Ok(stop)
              } else {
                Ok(false)
              }
            }
          } ;

          self.synth_sys[pred].restart() ;

          'synth: loop {

            for sample in data.iter(! simple) {
              self_core.check_exit() ? ;
              let done = self.synth_sys[pred].sample_synth(
                sample, & mut treatment, & self_core._profiler
              ) ? ;
              if done { break }
            }

            self.synth_sys[pred].increment() ;
            if self.synth_sys[pred].is_done() {
              break 'synth
            }

          }
        }

        Ok(Some(()))
    }
}

impl<'core> ::std::ops::Deref for IceLearner<'core> {
    type Target = MsgCore;
    fn deref(&self) -> &MsgCore {
        &self.core
    }
}
