# Thesis ↔ Isabelle mapping

Matches the revised thesis (October 2026). Numbering follows that version.

Status column: ✔ checked by Isabelle2024 (full session build, no `sorry`, 16 Oct 2026).

## The top-level argument

| Thesis | Isabelle | Theory | Status |
|---|---|---|---|
| Part 1: for any Collector meeting the Collector's specification and any Mutator meeting the Mutator's, Collector ∥ Mutator is correct (the parallel rule with the obligations of §4.5.5 and coupling consistent(s, σ)) | `Collector_par_Mutator_abstract` | GC_Parallel | ✔ |
| The Collector meets its specification: {pre-Collector, rely-Collector} Unmark; Mark; Sweep {guar-Collector, post-Collector} | `Collector_sat` | GC_Collector | ✔ |
| The Mutator meets its specification: {new-risk = {}, guar-Collector} Mutator {guar-Mutator, true} | `Mutator_sat` | GC_Mutator | ✔ |
| So Collector ∥ Mutator is correct: the abstract theorem applied to the two programs | `Collector_par_Mutator` | GC_System | ✔ |

## Definitions

| Thesis | Isabelle | Theory |
|---|---|---|
| Heap, shared state Σ (§4.2.1–4.2.2) | `('a,'i) heap`, record `state` | GC_Defs |
| Definition 1 (garbage) | `garbage` | GC_Defs |
| Definition 2 (kids) | `kids` | GC_Defs |
| Definition 3 (child-rel, child-rel*) | `child_rel`, `(child_rel h)^*` | GC_Defs |
| Definition 4 (paths) / Lemma 21 (App. B.2) | library `rtrancl`; `reach_last_edge`, `reach_closed` | GC_Defs |
| Definition 5 (reach) | `reach` | GC_Defs |
| inv-Σ (weakened, §4.4.2) | `inv_state` | GC_Defs |
| Definition 6 (Bad, BadA) | `Bad`, `BadA` | GC_Collector_Spec |
| invB (§4.7) | `invB` | GC_Invariant |
| rely-Collector (§4.5.4), with (4.1) as `a ∉ garbage ∧ hp′(a,i) ∉ garbage` | `rely_Collector`; with Assumption 1 and inv-Σ: `env_step` | GC_Collector_Spec |
| Assumption 1 (§4.4.1) | `atomic` (part of `env_step`; proved for the Mutator's steps in `section_455_obligation`) | GC_Collector_Spec, GC_Parallel |
| guar-Unmark / Mark / Mark-kids (App. C) | `guar_Unmark`, `guar_Mark`, `guar_MarkKids`, `guar_MarkEnd` | GC_Collector_Steps |
| guar-Sweep, guar-Add-to-free (App. C, §4.8.3) | `guar_Sweep`, `guar_AddToFree` | GC_Collector_Steps |
| invA (§4.8.4) | `invA` | GC_Collector_Steps |
| inv-safe (§4.8.4) | `inv_safe` | GC_Safety |
| step-Collector (§4.7.2) | `step_Collector` | GC_Collector_Steps |
| guar-Collector (§4.4, with the conjunct (reach(roots,hp) × Index) ◁ hp′ = (reach(roots,hp) × Index) ◁ hp; rely of the Mutator, §4.6) | `guar_Collector` | GC_Collector_Spec |
| so-far_M-k, so-far_P, so-far_M, so-far_U, so-far_S | `so_farMk`, `so_farP`, `so_farM`, `so_farU`, `so_farS` | GC_Mark, GC_Unmark, GC_Sweep |
| post-Mark-kids, post-Propagate, post-Mark, post-Unmark, post-Sweep, post-Collector | `post_MarkKids`, `post_Propagate`, `post_Mark`, `post_Unmark`, `post_Sweep`, `post_Collector` | GC_Mark, GC_Unmark, GC_Sweep, GC_Collector_Post |
| Possible values (§2.3) | history variable `Fv` (a list of the values `free` took), history function `hC`, possible values `pv k0 k`, `hist_ok` | GC_Code |
| Rely/guarantee quadruple {p, r} c {g, q} (§2.2), over computations with program and environment steps | `rg_sat`, computations `rg_reach` | RG_Semantics |
| Parallel composition A ∥ B | `par`, `par_pre`, `par_guar`, `par_post` | RG_Semantics |
| Programs: atomic statements, sequential composition, if, while (the language of Appendix C) | `com`: `Basic`, `Seq`, `Cond`, `IfThen`, `While`, `Skip` | RG_VDM |
| The VDM quadruple {p, r} c {g, q}; p "holds despite interference"; post1 \| post2 | `vdm`, `stable`, `tolerates`, `seq_post` | RG_VDM |
| The Collector's specification (§4.4): rely rely-Collector, guar guar-Collector (with Lemma 3), pre s = {}, post post-Collector | `rely_C`, `guar_C` (GC_Collector_Spec); `C_pre`, `C_post` (GC_Collector); `coll_sat` is {p, rely-Collector} c {g, q} (GC_Code) | GC_Collector_Spec, GC_Collector, GC_Code |
| The Collector's private variables (consid, checked, mc, s, x, i, cleared) | record `cvars` | GC_Code |
| The Collector's code (Appendix C): Unmark (Alg. 15), Mark (Alg. 7), Propagate (Alg. 17), Mark-kids (Alg. 18), Sweep (Alg. 19), Add-to-free (Alg. 20) | `Unmark`, `Mark`, `Propagate`, `MarkKids`, `Sweep`, `AddToFree`; `Collector = Unmark; Mark; Sweep` | GC_Code |
| Each operation's specification (App. C) | `MK_pre`/`MK_guar`/`MK_post`, `P_…`, `M_…`, `U_…`, `A_…`, `S_guar`/`S_J`/`S_post` | GC_Mark_Sat, GC_Unmark_Sat, GC_Sweep_Sat |
| Each loop's test, inv and so-far (§4.8) | `MK_test`/`MK_inv`/`MK_sofar`, `P_…`, `M_test`/`M_inv`/`M_sofar`, `U_…`, `A_…`, `S_…` | GC_Code (tests), GC_Mark_Sat, GC_Unmark_Sat, GC_Sweep_Sat |
| The Mutator's specification (§4.6): rely guar-Collector, guar guar-Mutator | `rely_M`, `guar_M` (GC_Mutator_Spec); `mut_sat` is {p, guar-Collector} c {g, q} (GC_Mutator) | GC_Mutator_Spec, GC_Mutator |
| guar-Mutator (§4.6): the step guarantees of Redirect, Malloc and Zap, with new-risk | `guar_Mutator` (`g_Redirect_hp`, `g_Redirect_mk`, `g_Malloc_hp`, `g_Malloc_fr`, `g_Zap`) | GC_Mutator_Spec |
| consistent(s,σ) ≜ Bad(s,σ) ⊆ new-risk(σ) | `consistent` | GC_Parallel |
| The Mutator's private variables (the operation chosen, a, i, b, new-risk) | record `mvars` | GC_Mutator |
| The Mutator's code (Algorithm 12, §4.6): Redirect, Malloc, Zap | `Mutator`, `Mut_op`, `Mut_choose`, `Redirect`, `Malloc`, `Zap` | GC_Mutator |
| The pre conditions of Redirect, Malloc and Zap (§4.6) | `pre_op` | GC_Mutator |

## Results

| Thesis | Isabelle | Theory | Status |
|---|---|---|---|
| Rely is reflexive and transitive (requirement of §2.2) | `rely_Collector_refl`, `rely_Collector_trans` | GC_Collector_Spec | ✔ |
| step-Collector ⇒ guar-Unmark ∨ guar-Mark ∨ guar-Sweep (§4.7.2) | `step_Collector_phases` | GC_Collector_Steps | ✔ |
| Lemma 1 | `lemma1_env_card` | GC_Invariant | ✔ |
| Lemma 2 | `lemma2_env_invB` (via `invB_witness_hp_change`) | GC_Invariant | ✔ |
| Lemma 3 | `lemma3_prog_Bad` | GC_Invariant | ✔ |
| Lemma 4 | `lemma4_prog_invB` | GC_Invariant | ✔ |
| Mark-kids meets its specification (§4.8.1) | `MarkKids_sat` (loop: `MK_loop_sat`, body: `MK_body_sat`) | GC_Mark_Sat | ✔ |
| Lemma 5 | `lemma5_so_farMk_trans`, `lemma5_so_farMk_wf`; despite interference: `MK_sofar_tolerates` | GC_Mark, GC_Mark_Sat | ✔ |
| Theorem 1 | `theorem1_post_MarkKids` (used in `MK_loop_sat`) | GC_Mark, GC_Mark_Sat | ✔ |
| Propagate meets its specification (§4.8.1) | `Propagate_sat` (loop: `P_loop_sat`, body: `P_body_sat`) | GC_Mark_Sat | ✔ |
| Lemma 6 | `lemma6_so_farP_trans`, `lemma6_so_farP_wf`; despite interference: `P_sofar_tolerates` | GC_Mark, GC_Mark_Sat | ✔ |
| Lemma 7 | `lemma7_post_Propagate1` | GC_Mark | ✔ |
| Lemma 8 | `lemma8_kids_marked` | GC_Mark | ✔ |
| Theorem 2 | `theorem2_core`, `theorem2_post_Propagate` (used in `P_loop_sat`) | GC_Mark, GC_Mark_Sat | ✔ |
| Mark meets its specification (§4.8.1) | `Mark_sat` (the loop runs at least once: `rule_repeat`; body: `M_body_sat`) | GC_Mark_Sat, RG_VDM | ✔ |
| Lemma 9 | `lemma9_reach_marked_mono` | GC_Mark | ✔ |
| Lemma 10 | `lemma10_so_farM_trans`, `lemma10_so_farM_wf`; despite interference: `M_sofar_tolerates` | GC_Mark, GC_Mark_Sat | ✔ |
| Lemma 11 / 12 | `lemma11_post_Mark1`, `lemma12_post_Mark2` | GC_Mark | ✔ |
| Theorem 3 | `theorem3_post_Mark` (used in `Mark_sat`) | GC_Mark, GC_Mark_Sat | ✔ |
| Corollary 1 | `corollary1_garbage_bound` | GC_Mark | ✔ |
| Unmark meets its specification (§4.8.2) | `Unmark_sat` (loop: `U_loop_sat`, body: `U_body_sat`) | GC_Unmark_Sat | ✔ |
| Lemma 13 | `lemma13_so_farU_trans`, `lemma13_so_farU_wf`; despite interference: `U_sofar_tolerates` | GC_Unmark, GC_Unmark_Sat | ✔ |
| Theorem 4 | `theorem4_post_Unmark` (used in `U_loop_sat`) | GC_Unmark, GC_Unmark_Sat | ✔ |
| Add-to-free meets its specification (§4.8.3) | `AddToFree_sat` (loop: `A_loop_sat`, body: `A_body_sat`) | GC_Sweep_Sat | ✔ |
| Sweep meets its specification (§4.8.3) | `Sweep_sat` (loop: `S_loop_sat`, body: `S_body_sat`, line 4: `S_if_sat`) | GC_Sweep_Sat | ✔ |
| Lemma 14 | `lemma14_so_farS_trans`, `lemma14_so_farS_wf`; despite interference: `S_sofar_tolerates` | GC_Sweep, GC_Sweep_Sat | ✔ |
| Theorem 5 | `theorem5_post_Sweep` (used in `S_loop_sat`) | GC_Sweep, GC_Sweep_Sat | ✔ |
| Lemma 15 / 16 | `lemma15_env_inv_safe`, `lemma16_prog_inv_safe`; in Sweep: `S_J_stable`, `S_guar_J`; in Mark: `envs_inv_safe` | GC_Safety, GC_Sweep_Sat, GC_Mark_Sat | ✔ |
| invA holds on entry to Add-to-free (§4.8.4, after Lemma 16) | `invA_init` | GC_Safety | ✔ |
| Lemma 17 / 18 | `lemma17_env_invA`, `lemma18_prog_invA`; in Add-to-free: `A_J_stable`, `A_null_sat` | GC_Safety, GC_Sweep_Sat | ✔ |
| Theorem 6 (Safety) | `theorem6_safety`; for the Collector's code: `Collector_safe`; for Collector ∥ Mutator: `system_safety` | GC_Safety, GC_Collector, GC_System | ✔ |
| Lemma 19 | first conjunct: `lemma19_edges_unchanged`; second conjunct: `lemma19_reach_unchanged` | GC_Safety | ✔ |
| Sublemma 1 | `sublemma1_agree_reach`; applied to guar-Collector (proof of Corollary 2): `guar_Collector_reach` | GC_Safety | ✔ |
| Corollary 2 | `corollary2_step_guar`, `corollary2_guar_trans`; for the Collector's code: `C_step_guar` | GC_Safety, GC_Collector | ✔ |
| Every step of the Collector's code is a step-Collector step | `C_step` in `Unmark_C`, `Mark_C`, `Sweep_C` | GC_Collector | ✔ |
| Lemma 20 | `lemma20_reach_marked_bound` | GC_Collector_Post | ✔ |
| Sublemma 2 | `sublemma2_closure` (single-step form: `sublemma2_step`); what Unmark guarantees: `no_new_ptr` in `U_post` | GC_Collector_Post, GC_Unmark, GC_Unmark_Sat | ✔ |
| Theorem 7 | `theorem7_post_Collector`; for the Collector's code: `Collector_sat` (post condition `C_post`); for Collector ∥ Mutator: `system_post_Collector` | GC_Collector_Post, GC_Collector, GC_System | ✔ |
| Theorem 8 / Lemma 22 (App. B.3, informal) | invB is part of the invariants of Mark and its loops (`M_pre`, `M_inv`, `P_inv`), kept by Lemma 2 (`envs_invB`) and Lemma 4 (`guar_Mark_invB`); outside Mark s = {} and invB holds trivially (`invB_empty`) | GC_Invariant, GC_Code, GC_Mark_Sat | ✔ |
| The VDM rules (App. B.1): consequence, sequential composition, while; atomic statements and conditionals | `rule_conseq`, `rule_weaken`, `rule_seq`, `rule_while`, `rule_repeat`, `rule_basic`, `rule_cond`, `rule_if`, `rule_seq_basic`, `rule_trace`, `rule_trace_h`, `rule_inv` | RG_VDM | ✔ |
| A VDM quadruple is a rely/guarantee quadruple, so the parallel rule applies | `vdm_rg_sat` | RG_VDM | ✔ |
| The parallel rule, proved sound (generalised §2.2 rule: private variables in rely/guarantee conditions, coupling predicate as in the abstract-set pattern) | `rg_parallel` (soundness argument: `par_project`) | RG_Semantics | ✔ |
| The plain parallel rule of §2.2 | `rg_parallel_plain` | RG_Semantics | ✔ |
| Redirect, Malloc and Zap meet their specifications (§4.6) | `Redirect_sat`, `Malloc_sat`, `Zap_sat`; one operation: `Mut_op_sat` | GC_Mutator | ✔ |
| The pre conditions of the operations hold despite interference (§4.6) | `pre_op_stable`, `Mut_inv_stable`, `R_mid_stable`, `Ml_mid_stable` | GC_Mutator | ✔ |
| §4.5.5 displayed obligation: consistent(s,σ) ∧ guar-Mutator ⇒ rely-Collector ∧ consistent(s,σ′), for every s | `section_455_obligation` | GC_Parallel | ✔ |
| §4.5.5 supporting obligations (consistency holds initially; every Collector step preserves it) | `gc_parallel.initially`, `collector_keeps_consistent` (via Lemma 3); for the code: `system_init_iff` | GC_Parallel, GC_System | ✔ |
| guar-Collector implies the Mutator's rely; guar-Mutator implies rely-Collector | `gc_parallel.side_C`, `gc_parallel.side_M` | GC_Parallel | ✔ |
| The parallel rule applied to any two processes meeting the two specifications | `Collector_par_Mutator_abstract` (locale form: `gc_parallel.parallel`); in every interleaving: `gc_parallel.collector_safe`, `gc_parallel.mutator_step`, `gc_parallel.invariants` | GC_Parallel | ✔ |
| The Collector and the Mutator as processes | `collector_process`, `mutator_process`, `system_instance` | GC_System | ✔ |
| In every interleaving: every Mutator step satisfies guar-Mutator and rely-Collector; consistent(s,σ) and inv-Σ hold | `system_mutator_steps`, `system_consistent` | GC_System | ✔ |

## How the mechanisation is organised

The theories are in folders in `theories/`, one for each part of the argument, and are
listed in `ROOT` in reading order. `GC_Results` (at the top of `theories/`) restates the
main results, with the thesis sentence each corresponds to.

**0_Framework: rely/guarantee in general (§2.2, Appendix B.1).**

- **Rely/guarantee semantics (RG_Semantics).** A rely/guarantee quadruple is given a
  meaning over Aczel traces: program steps and environment steps, with every
  environment step satisfying the rely condition. The parallel rule is proved sound
  from that meaning. It is our own formalisation, not Isabelle's HOL-Hoare_Parallel
  library, whose plain rule has no private variables or coupling predicate.
- **VDM-style reasoning (RG_VDM).** A small language of programs (the language of
  Appendix C), a VDM quadruple over its computations, and the rules the thesis uses,
  each proved sound. `vdm_rg_sat` turns a VDM quadruple about a program into a
  quadruple of RG_Semantics about the program run as a process.

**Part 1, 1_Specifications: the specifications, and why any Collector and Mutator meeting them are correct in parallel (§4.2–4.6).** No code.

- **The state (GC_Defs).** The definitions of §4.2.
- **The Collector's specification (GC_Collector_Spec).** Definition 6 (Bad), rely-Collector,
  Assumption 1 and guar-Collector, and the Collector's rely and guarantee conditions built
  from them (`rely_C`, `guar_C`).
- **The Mutator's specification (GC_Mutator_Spec).** The Mutator relies on guar-Collector
  and guarantees guar-Mutator, built from the guarantee of each atomic step of Redirect,
  Malloc and Zap (`rely_M`, `guar_M`).
- **Collector ∥ Mutator (GC_Parallel).** The obligations of §4.5.5 and the parallel rule
  applied to any process meeting the Collector's specification and any process meeting
  the Mutator's (`Collector_par_Mutator_abstract`). In every interleaving, each
  process's steps satisfy the other's rely condition, every Collector step frees only
  garbage, and consistent(s, σ) holds.

**Part 2: why the actual code meets those specifications (§4.7–4.8, §4.6).**

- **The Collector (2a_Collector).** One folder for each part of the thesis:
  - `0_Code`: the guarantee of each phase of the code, invA and step-Collector
    (GC_Collector_Steps), and the code of Appendix C (GC_Code);
  - `4.7_Invariant`: invB and Lemmas 1–4 (GC_Invariant);
  - then for each subsection of §4.8 the thesis's lemmas and theorems followed by the
    proof that that part of the code meets its specification: GC_Mark and GC_Mark_Sat
    (`4.8.1_Mark`), GC_Unmark and GC_Unmark_Sat (`4.8.2_Unmark`), GC_Sweep, GC_Safety and
    GC_Sweep_Sat (`4.8.3-4.8.4_Sweep_Safety`; Add-to-free and Sweep need the invariants of
    §4.8.4), GC_Collector_Post and GC_Collector (`4.8.5_Collector`, `Collector_sat`).
- **The Mutator (2b_Mutator, GC_Mutator).** The code of Algorithm 12 and the proof that
  each operation and the Mutator meet the specification (`Mutator_sat`).

**Part 3, 3_System: the two together.**

- **Collector ∥ Mutator for the code (GC_System).** The two programs run as processes
  meet the two specifications, so `Collector_par_Mutator_abstract` applies to them
  (`Collector_par_Mutator`), and its consequences hold in every interleaving of the
  code; once the Collector has finished its cycle, post-Collector holds.
- **The main results (GC_Results).** `result1_any_Collector_par_any_Mutator` to
  `result7_consistent`: Part 1, `Collector_sat`, `Mutator_sat`, Collector ∥ Mutator for the
  code, safety, post-Collector and consistent(s, σ) in every run.

## Changes of statement and notes

1. **step-Collector.** The thesis defines step-Collector(σ,σ′) as "consecutive states
   of a single program step of the Collector". Here it is the relation that records
   what the thesis proofs use about such a step: it is a step of Unmark, Mark or
   Sweep, and a Sweep step that changes `free` or `hp` is a step of Add-to-free(x)
   taken while invA(x,σ) holds (as the thesis argues from pre-Add-to-free, inv-safe
   and Lemmas 17–18). GC_Collector proves that every atomic step of the code satisfies
   it (`C_step` in `Unmark_C`, `Mark_C`, `Sweep_C`).
2. **rely-Collector is transitive.** `rely_Collector_trans` proves the rely condition
   transitive, using the state invariant (`free ⊆ marked`) in the first state.
3. **Assumption 1 is required.** The mechanisation makes `atomic` part of every
   environment step of the Collector (`env_step`) and proves it for the Mutator's
   steps (`section_455_obligation`).
4. **`roots` constant.** Stated explicitly in `rely_Collector` and all guarantees.
5. **Lemma 2, Case 2.** The three-way case analysis of Figure 4.20 is replaced by one
   lemma (`reach_upd`): everything reachable from the roots in the old heap is reachable
   from `roots ∪ {c}` in the heap with the changed edge deleted, and `c` is marked.
6. **Theorem 2.** The backwards walk is replaced by a closure argument (`reach_closed`):
   the marked set is closed under the child relation of the heap with the bad edge
   deleted, so the witness's source is marked and yields a second bad edge.
7. **Possible values.** The Collector has a history variable `Fv`, the list of the
   values `free` has taken. After every step, by either process, the history function
   `hC` appends the current value of `free`. `pv k0 k` is the set of values recorded
   from configuration k0 to k (the thesis's free~ over that stretch), and
   `hist_ok k0 k` says the history has only been appended to. This is how the
   possible-values notation of Theorems 5 and 7 is given meaning.
8. **Mark-kids** `hp(x,i)` is guarded (`{b. hp σ (x,i) = Some b}`), matching the
   set-comprehension form of the thesis.
9. **The Collector's guarantee in Isabelle** (`guar_C`) is guar-Collector together with
   inv-Σ after the step and Bad(s′,σ′) ⊆ Bad(s,σ) (Lemma 3). The Mutator relies only
   on guar-Collector; the other two conjuncts are what the composition needs (item 2
   at the end of §4.5.5). The Collector's pre condition (`C_pre`) also states inv-Σ.
10. **The Mutator's pre condition** (`Mut_pre`) is new-risk = {}, together with inv-Σ
    and free ∩ reach(roots, hp) = {}, which hold between the Mutator's operations
    (§4.4.2). The operations are proved with post condition `Mut_inv` (the same
    predicate), what the next operation needs. What holds between the two atomic steps
    of Redirect and of Malloc is `R_mid` and `Ml_mid`.
11. **guar-Mutator is reflexive.** `guar_Mutator` has the disjunct σ′ = σ ∧ new-risk′ =
    new-risk, for the Mutator's steps that change no shared variable (choosing an
    operation). Rely and guarantee conditions are reflexive (§2.2);
    `section_455_obligation` covers this case.
12. **Add-to-free's post condition.** x ∈ free′ and kids(x, hp′) = {} are not satisfied
    despite interference, since the Mutator may allocate x as soon as it is free. The
    post condition in Isabelle (`A_post`) is that x is marked and was in free at some
    point during Add-to-free (x ∈ f for some f in free~), which is what Sweep's post
    condition needs. §4.8.3 makes this point for Sweep.
13. **Termination.** The rules of RG_VDM are for partial correctness: `rule_while` needs
    so-far transitive but not well-founded. That so-far is well-founded, so each loop
    terminates, is proved separately for each loop (`lemma5_so_farMk_wf`,
    `lemma6_so_farP_wf`, `lemma10_so_farM_wf`, `lemma13_so_farU_wf`,
    `lemma14_so_farS_wf`). For Mark the relation is restricted to iterations that start
    where testM holds, as in the thesis's argument.
14. **The parallel rule.** `rg_parallel` allows rely and guarantee conditions to refer
    to a component's own private variables (rely-Collector refers to s), and requires
    the side conditions only in states satisfying a coupling predicate J that both
    guarantees preserve. Here J is consistent(s, σ). This is the quantification over an
    abstract set of Yatapanage (2026, arXiv:2609.27392). With J true and conditions over the
    shared state only it is the rule of §2.2 (`rg_parallel_plain`). A post condition is
    "terminated ⇒ post" (`post_of`), and environment steps may follow the last program
    step, so every post condition is shown to hold despite interference.
