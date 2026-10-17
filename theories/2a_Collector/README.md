# 2a_Collector: Part 2 for the Collector (§4.7–4.8)

The Collector's code (Appendix C) meets its specification
(`../1_Specifications/GC_Collector_Spec.thy`). The main theorem is `Collector_sat`, in
`4.8.5_Collector/GC_Collector.thy`.

There is one folder for each part of the thesis. In each §4.8 folder the first theory has
the thesis's lemmas and theorems for that subsection, in the thesis's order (they are about
steps and relations, and mention no code), and the `_Sat` theory proves that that part of
the code meets its specification, using them.

| Folder | Thesis | Theories |
|---|---|---|
| `0_Code` | Appendix C | `GC_Collector_Steps`: what one step of each phase may do, invA, step-Collector; `GC_Code`: the code |
| `4.7_Invariant` | §4.7 | `GC_Invariant`: invB, Lemmas 1–4 |
| `4.8.1_Mark` | §4.8.1 | `GC_Mark`: Lemmas 5–12, Theorems 1–3, Corollary 1; `GC_Mark_Sat`: Mark-kids, Propagate and Mark meet their specifications |
| `4.8.2_Unmark` | §4.8.2 | `GC_Unmark`: Lemma 13, Theorem 4; `GC_Unmark_Sat`: Unmark meets its specification |
| `4.8.3-4.8.4_Sweep_Safety` | §4.8.3–4.8.4 | `GC_Sweep`: Lemma 14, Theorem 5; `GC_Safety`: Lemmas 15–19, Sublemma 1, Theorem 6, Corollary 2; `GC_Sweep_Sat`: Add-to-free and Sweep meet their specifications (after `GC_Safety`, whose invariants they use) |
| `4.8.5_Collector` | §4.8.5 | `GC_Collector_Post`: Sublemma 2, Lemma 20, Theorem 7; `GC_Collector`: the whole Collector meets its specification (`Collector_sat`) |
