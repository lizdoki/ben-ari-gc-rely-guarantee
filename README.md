# Rely/guarantee verification of the Ben-Ari garbage collector in Isabelle/HOL

> [!NOTE]
> **Authorship.** The ideas formalised here are my own and come from my thesis. 
> Turning them into Isabelle/HOL was done with heavy use of AI assistance.

This repository mechanises in Isabelle/HOL the rely/guarantee proof of safety of Ben-Ari's on-the-fly garbage collector from Chapter 4 of my thesis, [*Concurrency Verification Using a Rely/Guarantee Approach*](thesis.pdf?raw=true) (L. Yevdokimov, ANU Honours thesis,
revised version of October 2026; theorem numbering follows that version). The Collector is proved correct under its own rely condition, for every heap and any environment satisfying that rely condition. The Mutator is proved to satisfy the rely condition, and the two are composed with the parallel rule. 

To the best of my knowledge, this is the first complete rely/guarantee proof of safety for this algorithm, and the first mechanised one. Earlier mechanised proofs either use non-compositional methods, or do not establish the Collector's correctness under a rely condition; see §5.4 of the thesis.


## Key results

All of these are in `theories/GC_Results.thy`.

**The Collector is correct under its rely condition.** The results below hold for every heap
and for *any* environment whose steps satisfy rely-Collector (with Assumption 1 and inv-Σ),
not only for the Mutator of §4.6.

| Result | Thesis | Isabelle |
|---|---|---|
| Every step of the Collector only adds garbage to free (safety) | Theorem 6, Corollary 2 | `result2a_Collector_safety` |
| An iteration of Propagate in which marked does not change ends with every reachable node marked | Theorem 2 | `result2b_Propagate_round` |
| When Mark finishes, every reachable node is marked | Theorem 3 | `result2c_Mark_marks_reachable` |
| The Collector meets its specification: {pre-Collector, rely-Collector} Unmark; Mark; Sweep {guar-Collector, post-Collector} | §4.7–4.8, Theorem 7 | `result2_Collector_meets_spec` |

**The Mutator meets its specification**, {new-risk = {}, guar-Collector} Mutator
{guar-Mutator, true} (§4.6): `result3_Mutator_meets_spec`.

**The two together are correct** (§4.5.5):

| Result | Isabelle |
|---|---|
| Any Collector and any Mutator meeting the two specifications are correct in parallel | `result1_any_Collector_par_any_Mutator` |
| Collector ∥ Mutator is correct, for the code | `result4_Collector_par_Mutator` |
| In every run, no node in use is ever freed | `result5_safety` |
| In every run in which the Collector finishes its cycle, every node that was garbage at the start was in free at some point during the cycle (post-Collector) | `result6_post_Collector` |
| In every run, consistent(s, σ) and inv-Σ hold in every state | `result7_consistent` |

## How the theories are organised

The folders in `theories/` follow the three parts of the argument. Each folder has a short
README saying what is in it and the order to read it.

```
theories/
├── GC_Results.thy                  start here: the main results, restated
├── 0_Framework/                    rely/guarantee in general (§2.2, App. B.1)
├── 1_Specifications/               Part 1: the specifications (§4.2–4.6)
├── 2a_Collector/                   Part 2: the Collector's code meets its specification (§4.7–4.8)
│   ├── 0_Code/
│   ├── 4.7_Invariant/
│   ├── 4.8.1_Mark/
│   ├── 4.8.2_Unmark/
│   ├── 4.8.3-4.8.4_Sweep_Safety/
│   └── 4.8.5_Collector/
├── 2b_Mutator/                     Part 2: the Mutator's code meets its specification (§4.6)
└── 3_System/                       Part 3: the two together, for the code (§4.5.5)
```

**0_Framework: rely/guarantee in general.** Nothing here is about garbage collection.
`RG_Semantics` gives rely/guarantee quadruples a meaning and proves the parallel rule sound;
`RG_VDM` gives the VDM-style rules the thesis uses, each proved sound.

**Part 1: the specifications, and why any Collector and Mutator meeting them are correct
in parallel (§4.2–4.6).** No code.

- `GC_Collector_Spec` states the Collector's specification: it relies on rely-Collector and
  guarantees guar-Collector.
- `GC_Mutator_Spec` states the Mutator's specification: it relies on guar-Collector and
  guarantees guar-Mutator.
- `GC_Parallel` proves the obligations of §4.5.5 and then `Collector_par_Mutator_abstract`:
  for **any** process C1 that meets the Collector's specification and **any** process C2
  that meets the Mutator's, C1 ∥ C2 is correct, by the parallel rule of §2.2 with
  consistent(s, σ) as the coupling predicate. Its two main assumptions are exactly
  "the Collector meets its specification" and "the Mutator meets its specification".

**Part 2: why the actual code meets those specifications (§4.7–4.8 and §4.6).**

- `2a_Collector`: the Collector's code (Appendix C) meets `GC_Collector_Spec`:
  `Collector_sat` (GC_Collector), proved in VDM style, following §4.7–4.8. There is one
  folder for each part of the thesis. In each §4.8 folder, the first theory has the thesis's
  lemmas and theorems, which are about steps and relations and mention no code (for example
  GC_Mark), and the `_Sat` theory proves that that part of the code meets its
  specification, using them (for example GC_Mark_Sat).
- `2b_Mutator`: the Mutator's code (Algorithm 12 with Redirect, Malloc and Zap of §4.6)
  meets `GC_Mutator_Spec`: `Mutator_sat` (GC_Mutator).

**Part 3: the two together, for the code (§4.5.5).**

- `GC_System` applies Part 1 to the two programs: `Collector_par_Mutator`, and its
  consequences in every run (safety, post-Collector, consistent(s, σ) throughout).
- `GC_Results` restates the main results.

## Reading the Isabelle alongside Chapter 4

| Thesis | Folder | Theory | Main names |
|---|---|---|---|
| §2.2 rely/guarantee quadruples, the parallel rule | 0_Framework | RG_Semantics | `rg_sat`, `rg_parallel` |
| App. B.1 the VDM rules | 0_Framework | RG_VDM | `vdm`, `rule_seq`, `rule_while`, `rule_conseq` |
| §4.2 the state and its definitions | 1_Specifications | GC_Defs | `garbage`, `kids`, `reach`, `inv_state` |
| §4.4–4.5 the Collector's specification: Definition 6, rely-Collector, Assumption 1, guar-Collector | 1_Specifications | GC_Collector_Spec | `Bad`, `rely_Collector`, `atomic`, `guar_Collector`, `rely_C`, `guar_C` |
| §4.5.5, §4.6 the Mutator's specification: guar-Collector, guar-Mutator | 1_Specifications | GC_Mutator_Spec | `rely_M`, `guar_Mutator`, `guar_M` |
| §4.5.5 Collector ∥ Mutator, for any processes meeting the specifications | 1_Specifications | GC_Parallel | `section_455_obligation`, `Collector_par_Mutator_abstract` |
| App. C the guarantee of each phase; §4.7.2 step-Collector; §4.8.4 invA | 2a_Collector/0_Code | GC_Collector_Steps | `guar_Mark`, `guar_Sweep`, `step_Collector`, `invA`, … |
| App. C the Collector's code | 2a_Collector/0_Code | GC_Code | `Unmark`, `Mark`, `Propagate`, `MarkKids`, `Sweep`, `AddToFree`, `Collector` |
| §4.7 invB, Lemmas 1–4 | 2a_Collector/4.7_Invariant | GC_Invariant | `invB`, `lemma1_env_card` … `lemma4_prog_invB` |
| §4.8.1 Lemmas 5–12, Theorems 1–3, Corollary 1 | 2a_Collector/4.8.1_Mark | GC_Mark | `lemma5_so_farMk_trans`, `lemma5_so_farMk_wf`, `theorem1_post_MarkKids`, … |
| §4.8.1 Mark-kids, Propagate and Mark meet their specifications | 2a_Collector/4.8.1_Mark | GC_Mark_Sat | `MarkKids_sat`, `Propagate_sat`, `Mark_sat` |
| §4.8.2 Lemma 13, Theorem 4 | 2a_Collector/4.8.2_Unmark | GC_Unmark | `lemma13_so_farU_trans`, `theorem4_post_Unmark` |
| §4.8.2 Unmark meets its specification | 2a_Collector/4.8.2_Unmark | GC_Unmark_Sat | `Unmark_sat` |
| §4.8.3 Lemma 14, Theorem 5 | 2a_Collector/4.8.3-4.8.4_Sweep_Safety | GC_Sweep | `lemma14_so_farS_trans`, `theorem5_post_Sweep` |
| §4.8.4 Lemmas 15–19, Sublemma 1, Theorem 6, Corollary 2 | 2a_Collector/4.8.3-4.8.4_Sweep_Safety | GC_Safety | `lemma15_env_inv_safe`, `theorem6_safety`, `sublemma1_agree_reach`, `corollary2_step_guar`, … |
| §4.8.3–4.8.4 Add-to-free and Sweep meet their specifications | 2a_Collector/4.8.3-4.8.4_Sweep_Safety | GC_Sweep_Sat | `AddToFree_sat`, `Sweep_sat` |
| §4.8.5 Sublemma 2, Lemma 20, Theorem 7 | 2a_Collector/4.8.5_Collector | GC_Collector_Post | `sublemma2_closure`, `lemma20_reach_marked_bound`, `theorem7_post_Collector` |
| §4.8.5 the Collector meets its specification | 2a_Collector/4.8.5_Collector | GC_Collector | `Collector_sat` |
| §4.6 the Mutator meets its specification | 2b_Mutator | GC_Mutator | `Redirect_sat`, `Malloc_sat`, `Zap_sat`, `Mutator_sat` |
| §4.5.5 Collector ∥ Mutator for the code | 3_System | GC_System | `Collector_par_Mutator`, `system_safety`, `system_post_Collector` |
| the main results, restated | (top of `theories/`) | GC_Results | `result1_any_Collector_par_any_Mutator` … `result7_consistent`, with `result2a_Collector_safety`, `result2b_Propagate_round`, `result2c_Mark_marks_reachable` |

For each subsection of §4.8 there are two theories: first the thesis's lemmas and theorems
for that subsection, in the thesis's order, then the proof that that part of the code meets
its specification, using them. For each operation X of Appendix C the second theory defines
X's specification (`X_pre`, `X_guar`, `X_post`), its loop's test, inv and so-far (`X_test`,
`X_inv`, `X_sofar`), shows that inv and so-far hold despite interference, goes through the
statements of the loop body one by one, and proves `X_sat`. Add-to-free and Sweep are proved
after §4.8.4 because their proofs use the safety invariants inv-safe and invA (Lemmas 15–18).

Each definition and theorem, or each group of them, has a text block saying how it relates to
the thesis: "Thesis:" (it is that part of the thesis), "Beyond the thesis:" (the thesis
states or argues it informally or not at all) or "Mechanisation only:" (a helper for the
Isabelle proof). `MAPPING.md` lists every thesis result with its Isabelle name.

## Files

- `ROOT` — session `GC_Mechanisation` (based on HOL); lists the folders and the theories in
  reading order.
- `theories/` — the theories, in the folders above.
- `thesis.pdf` — the revised thesis (October 2026).
- `LICENSE` — BSD 3-Clause.
- `CITATION.cff` — how to cite this work (GitHub shows it as "Cite this repository").

## Building

From this folder:

    /Applications/Isabelle2024.app/bin/isabelle build -d . -v GC_Mechanisation

or, to step through the theories interactively:

    /Applications/Isabelle2024.app/bin/isabelle jedit -d . theories/GC_Results.thy

The `-d .` tells Isabelle about `ROOT`, which lists the folders the theories import
each other from. If Isabelle/jEdit is started without it (for example from the Dock),
every theory reports `Bad theory import "Draft.…"` which is annoying. To make the
session known whichever way Isabelle is started, run this once:

    /Applications/Isabelle2024.app/bin/isabelle components -u "$PWD"

## Status

The whole session builds with Isabelle2024 with no `sorry`. The rules of RG_VDM are for
partial correctness. That each loop terminates is the well-foundedness half of Lemmas 5, 6,
10, 13 and 14 (`lemma5_so_farMk_wf` and so on), proved separately.

## Sources

This mechanisation builds on the following work, as the thesis does. The Collector's rely
condition, the proofs and the way they are put together are those of the thesis.

- **The algorithm.** M. Ben-Ari. Algorithms for on-the-fly garbage collection. *ACM
  Transactions on Programming Languages and Systems*, 6(3):333–344, 1984.
- **The model of the shared state** (roots, hp, free, marked), the definitions of §4.2
  (kids, the child relation, reach). C. B. Jones and N. Yatapanage. Investigating the limits of
  rely/guarantee relations based on a concurrent garbage collector example. *Formal
  Aspects of Computing*, 31:353–374, 2019.
- **Rely/guarantee reasoning.** C. B. Jones. Tentative steps toward a development method
  for interfering programs. *ACM Transactions on Programming Languages and Systems*,
  5(4):596–619, 1983. I. Hayes and C. B. Jones. A guide to rely/guarantee thinking. In
  *Engineering Trustworthy Software Systems*, LNCS 11174, pages 1–38. Springer, 2018.
- **VDM notation and proof rules.** C. B. Jones. *Systematic Software Development using
  VDM*, 2nd edition. Prentice Hall International, 1990.
- **Possible values** (free~, used in Theorems 5 and 7). C. B. Jones and I. Hayes.
  Possible values: exploring a concept for concurrency. *Journal of Logical and Algebraic
  Methods in Programming*, 85(5):972–984, 2016.
- **Quantifying over an abstract set** (the coupling predicate of the parallel rule).
  N. Yatapanage. The complexity of interference: when rely/guarantee does not work.
  arXiv:2609.27392, 2026.

## How to cite

If you use this mechanisation, or the ideas in it, please cite the thesis:

> Liz Yevdokimov. *Concurrency Verification Using a Rely/Guarantee Approach.* Bachelor of
> Philosophy (Honours) thesis, The Australian National University, 2025 (revised
> October 2026).

The "Cite this repository" button on GitHub gives this citation in BibTeX and other formats.

## Licence

BSD 3-Clause; see `LICENSE`.
