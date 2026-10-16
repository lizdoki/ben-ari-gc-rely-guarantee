# 1_Specifications: Part 1 (§4.2–4.6)

The two specifications, and why any Collector and any Mutator that meet them are correct
in parallel. No code.

1. `GC_Defs.thy`: the shared state and the definitions of §4.2 (`reach`, `garbage`,
   `inv_state`).
2. `GC_Collector_Spec.thy`: the Collector's rely and guarantee conditions: Definition 6
   (`Bad`), rely-Collector, Assumption 1 and guar-Collector (`rely_C`, `guar_C`).
3. `GC_Mutator_Spec.thy`: the Mutator's rely and guarantee conditions: it relies on
   guar-Collector and guarantees guar-Mutator (`rely_M`, `guar_M`).
4. `GC_Parallel.thy`: the obligations of §4.5.5, and the main theorem of Part 1,
   `Collector_par_Mutator_abstract`: any Collector meeting its specification and any
   Mutator meeting its specification are correct in parallel.

Part 2 proves that the actual code meets these specifications: the Collector's in
`../2a_Collector`, the Mutator's in `../2b_Mutator`.
