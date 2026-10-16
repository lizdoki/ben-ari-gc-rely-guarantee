session GC_Mechanisation = HOL +
  description "Mechanisation of the Ben-Ari garbage collector verification
    (L. Yevdokimov, Concurrency Verification Using a Rely/Guarantee Approach)."
  options [document = false]
  directories
    "theories/0_Framework"
    "theories/1_Specifications"
    "theories/2a_Collector/0_Code"
    "theories/2a_Collector/4.7_Invariant"
    "theories/2a_Collector/4.8.1_Mark"
    "theories/2a_Collector/4.8.2_Unmark"
    "theories/2a_Collector/4.8.3-4.8.4_Sweep_Safety"
    "theories/2a_Collector/4.8.5_Collector"
    "theories/2b_Mutator"
    "theories/3_System"
    "theories"
  theories
    (* 0_Framework: rely/guarantee in general (Section 2.2, Appendix B.1) *)
    RG_Semantics
    RG_VDM
    (* PART 1, 1_Specifications: the specifications, and why any Collector and
       Mutator meeting them are correct in parallel (Sections 4.2-4.6) *)
    GC_Defs
    GC_Collector_Spec
    GC_Mutator_Spec
    GC_Parallel
    (* PART 2, 2a_Collector: the Collector's code meets its specification
       (Sections 4.7 and 4.8): for each subsection, the thesis's lemmas
       (about steps and relations, no code), then the proof that the code
       meets its specification (_Sat) *)
    GC_Collector_Steps
    GC_Code
    GC_Invariant
    GC_Mark
    GC_Mark_Sat
    GC_Unmark
    GC_Unmark_Sat
    GC_Sweep
    GC_Safety
    GC_Sweep_Sat
    GC_Collector_Post
    GC_Collector
    (* PART 2, 2b_Mutator: the Mutator's code meets its specification
       (Section 4.6) *)
    GC_Mutator
    (* PART 3, 3_System: Parts 1 and 2 together, for the code (Section 4.5.5),
       and the main results restated (GC_Results) *)
    GC_System
    GC_Results
