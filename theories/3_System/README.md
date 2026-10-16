# 3_System: Part 3 (§4.5.5)

`GC_System.thy`: Parts 1 and 2 together. The Collector and the Mutator, run as processes,
meet the two specifications, so the theorem of Part 1 applies to them
(`Collector_par_Mutator`). Its consequences hold in every run: safety (`system_safety`),
post-Collector (`system_post_Collector`), and consistent(s, σ) and inv-Σ
(`system_consistent`).

The main results are restated in `../GC_Results.thy`.
