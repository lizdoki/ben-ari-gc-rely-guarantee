(*  GC_Results: the main results, restated.

    The big picture of what is proved, without the details.  Each result
    below restates, with its full Isabelle statement, a theorem proved
    elsewhere, and says which sentence of the thesis it is and where to find
    its proof.  Nothing new is proved here: each proof just cites the theorem.

    The theories are in folders, one for each part (see README.md):
      0_Framework        rely/guarantee in general: the parallel rule
                         (RG_Semantics) and the VDM rules (RG_VDM);
      1_Specifications   Part 1: the specifications, and why any Collector
                         and any Mutator meeting them are correct in
                         parallel (Sections 4.2-4.6);
      2a_Collector       Part 2: the Collector's code meets its
                         specification (Sections 4.7 and 4.8); results 2a-2c
                         below restate what this gives under rely-Collector;
      2b_Mutator         Part 2: the Mutator's code meets its specification
                         (Section 4.6);
      3_System           Part 3: the two together, for the code.

    The specifications themselves: rely_C and guar_C for the Collector
    (rely-Collector and guar-Collector, in GC_Collector_Spec), and rely_M
    and guar_M for the Mutator (guar-Collector and guar-Mutator, in
    GC_Mutator_Spec).

    HOW TO READ THE LABELS.  Each result below has a text block saying how it
    relates to the thesis:
      "Thesis:"             it is that part of the thesis;
      "Beyond the thesis:"  the thesis states or argues it informally or not
                            at all; the label says which part of the thesis
                            it makes precise or supports;
      "Mechanisation only:" a helper needed only for the Isabelle proof.
    Section, lemma and theorem numbers are those of the thesis.             *)

theory GC_Results
  imports GC_System
begin

section \<open>Part 1: any Collector and any Mutator meeting the specifications\<close>

text \<open>Thesis: "the Collector meets its specification, the Mutator meets its
  specification, and so Collector \<parallel> Mutator is correct" (Section 4.5.5),
  for any Collector C1 and any Mutator C2.  The first two assumptions are the
  two specifications: C1 relies on rely-Collector and guarantees
  guar-Collector; C2 relies on guar-Collector and guarantees guar-Mutator.
  The third says the Collector starts with s = {}; the last two that history
  variables are separate from s and new-risk.  The conclusion is the
  quadruple of the parallel rule (Section 2.2), with consistent(s, \<sigma>) as the
  coupling predicate: from a state where both pre conditions and
  consistent(s, \<sigma>) hold, every step satisfies guar-Collector or guar-Mutator,
  and both post conditions and consistent(s, \<sigma>) hold throughout.  The
  composed system has no environment (no_env).
  Proved in GC_Parallel (Collector_par_Mutator_abstract), from the
  obligations of Section 4.5.5 (section_455_obligation, side_C, side_M,
  initially) and the parallel rule (rg_parallel, RG_Semantics).\<close>

theorem result1_any_Collector_par_any_Mutator:
  assumes "rg_sat C1 h1 P1 (rely_C s_of) (guar_C s_of) Q1"
    and "rg_sat C2 h2 P2 rely_M (guar_M nr_of) Q2"
    and "\<And>c. P1 c \<Longrightarrow> s_of (fst c) = {}"
    and "\<And>l \<sigma>. s_of (h1 l \<sigma>) = s_of l"
    and "\<And>m \<sigma>. nr_of (h2 m \<sigma>) = nr_of m"
  shows "rg_sat (par C1 C2) (hpar h1 h2) (par_pre P1 P2 (coupling s_of nr_of)) no_env
                (par_guar (guar_C s_of) (guar_M nr_of)) (par_post Q1 Q2 (coupling s_of nr_of))"
  using assms by (rule Collector_par_Mutator_abstract)

section \<open>Part 2: the code meets the specifications\<close>

text \<open>Thesis: the Collector meets its specification (Sections 4.7 and 4.8):
    {pre-Collector, rely-Collector} Unmark; Mark; Sweep {guar-Collector, post-Collector}
  for the code of Appendix C (Collector, GC_Code).  The pre condition C_pre is
  s = {} (with inv-\<Sigma>); the post condition C_post is post-Collector,
  garbage \<subseteq> \<Union>free~, where free~ is the set of values free has taken during
  the cycle (Theorem 7).  Proved in GC_Collector (Collector_sat), from Unmark,
  Mark and Sweep meeting their specifications (GC_Unmark_Sat, GC_Mark_Sat,
  GC_Sweep_Sat) and the lemmas and theorems of Sections 4.7 and 4.8.\<close>

theorem result2_Collector_meets_spec:
  "coll_sat C_pre (Collector :: ('a::finite,'i::finite) ccom) (guar_C cvars.s) C_post"
  by (rule Collector_sat)

section \<open>Part 2 in detail: the Collector is correct under rely-Collector\<close>

text \<open>Thesis: what the Collector guarantees under its rely condition (Sections
  4.7 and 4.8).  The three results below are read off the quadruples proved for
  the Collector's code, and hold for every heap and for any environment whose
  steps satisfy rely-Collector (with Assumption 1 and inv-\<Sigma>, env_step), not
  only for the Mutator of Section 4.6.
  creach hC (rely_C cvars.s) c k0 c' k says that some computation of the program
  c from the configuration k0, in which every environment step satisfies
  rely-Collector, reaches the configuration k with c' left to run (c' = Skip
  when c has finished).\<close>

text \<open>Thesis: Theorem 6 (safety) and Corollary 2, under rely-Collector: every step
  of the Collector only adds garbage to free.  Proved from Collector_sat, whose
  guarantee guar_C contains guar-Collector.\<close>

theorem result2a_Collector_safety:
  assumes pre: "C_pre k0"
    and run: "creach hC (rely_C cvars.s) (Collector :: ('a::finite,'i::finite) ccom) k0 c k"
    and step: "cstep c k c' k'"
  shows "free (snd k') - free (snd k) \<subseteq> garbage (snd k)"
proof -
  have "k' = k \<or> guar_C cvars.s k k'"
    by (rule vdmD_guar[OF Collector_sat pre run step])
  then show ?thesis unfolding guar_C_def guar_Collector_def by auto
qed

text \<open>Thesis: Theorem 2, under rely-Collector: when an iteration of Propagate
  finishes and marked has not changed during it, every reachable node is
  marked.  Proved from Propagate_sat (GC_Mark_Sat).\<close>

theorem result2b_Propagate_round:
  assumes pre: "P_pre k0"
    and run: "creach hC (rely_C cvars.s) (Propagate :: ('a::finite,'i::finite) ccom) k0 Skip k"
    and same: "marked (snd k) = marked (snd k0)"
  shows "reach (roots (snd k)) (hp (snd k)) \<subseteq> marked (snd k)"
proof -
  obtain l0 \<sigma>0 where k0: "k0 = (l0, \<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l, \<sigma>)" by (cases k)
  have "P_post k0 k" by (rule vdmD_post[OF Propagate_sat pre run])
  with k0 k same show ?thesis by (simp add: P_post_def post_Propagate_def)
qed

text \<open>Thesis: Theorem 3, under rely-Collector: when Mark finishes, every
  reachable node is marked.  Proved from Mark_sat (GC_Mark_Sat).\<close>

theorem result2c_Mark_marks_reachable:
  assumes pre: "M_pre k0"
    and run: "creach hC (rely_C cvars.s) (Mark :: ('a::finite,'i::finite) ccom) k0 Skip k"
  shows "reach (roots (snd k)) (hp (snd k)) \<subseteq> marked (snd k)"
proof -
  obtain l0 \<sigma>0 where k0: "k0 = (l0, \<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l, \<sigma>)" by (cases k)
  have "M_post k0 k" by (rule vdmD_post[OF Mark_sat pre run])
  with k0 k show ?thesis by (simp add: M_post_def post_Mark_def)
qed

text \<open>Thesis: the Mutator meets its specification (Section 4.6):
    {new-risk = {}, guar-Collector} Mutator {guar-Mutator, true}
  for the code of Algorithm 12 with Redirect, Malloc and Zap (Mutator,
  GC_Mutator).  The pre condition Mut_pre also states inv-\<Sigma> and that no free
  node is reachable.  Proved in GC_Mutator (Mutator_sat).\<close>

theorem result3_Mutator_meets_spec:
  "mut_sat Mut_pre (Mutator :: ('a::finite,'i::finite) mcom) (guar_M nr) (\<lambda>k0 k. True)"
  by (rule Mutator_sat)

section \<open>Part 3: Collector \<parallel> Mutator for the code\<close>

text \<open>Thesis: Collector \<parallel> Mutator is correct, for the code: result 1 applied to
  the Collector and the Mutator of results 2 and 3, run as processes.  Proved
  in GC_System (Collector_par_Mutator).\<close>

theorem result4_Collector_par_Mutator:
  "rg_sat (par prog_of prog_of) (hpar (hist_of hC) (hist_of no_hist))
          (par_pre (pre_of (Collector :: ('a::finite,'i::finite) ccom) C_pre)
                   (pre_of (Mutator :: ('a,'i) mcom) Mut_pre) (coupling C_s M_nr))
          no_env
          (par_guar (guar_C C_s) (guar_M M_nr))
          (par_post (\<lambda>c0 c. post_of C_post c0 c \<and> inv_state (snd c)) (\<lambda>c0 c. inv_state (snd c))
                    (coupling C_s M_nr))"
  by (rule Collector_par_Mutator)

text \<open>What result 4 means for every run of the two programs.  In each result
  below the run starts with the Collector at the start of its cycle with
  s = {} (private variables l0), the Mutator between operations with
  new-risk = {} (private variables m0), inv-\<Sigma>, and no free node reachable.
  system_reach c0 (cl, cm) \<sigma> says that some interleaving of the Collector and
  the Mutator goes from c0 to the state \<sigma>, where cl and cm are what is left
  of each program together with its private variables.\<close>

text \<open>Thesis: Theorem 6 (safety) in every run: every step of the Collector
  only adds garbage to free, so no node in use is ever freed.  Proved in
  GC_System (system_safety), from Theorem 6 and Corollary 2 (GC_Safety).\<close>

theorem result5_safety:
  fixes \<sigma>0 :: "('a::finite,'i::finite) state"
  assumes start: "cvars.s l0 = {}" "nr m0 = {}" "inv_state \<sigma>0"
                 "free \<sigma>0 \<inter> reach (roots \<sigma>0) (hp \<sigma>0) = {}"
    and run: "system_reach (((Collector, l0), (Mutator, m0)), \<sigma>0) (cl, cm) \<sigma>"
    and step: "prog_of (cl, \<sigma>) (cl', \<sigma>')"
  shows "free \<sigma>' - free \<sigma> \<subseteq> garbage \<sigma>"
proof -
  have I0: "par_pre (pre_of Collector C_pre) (pre_of Mutator Mut_pre) (coupling C_s M_nr)
              (((Collector, l0), (Mutator, m0)), \<sigma>0)"
    using start by (simp add: system_init_iff)
  show ?thesis by (rule system_safety(1)[OF I0 run step])
qed

text \<open>Thesis: Theorem 7 (post-Collector) in every run: once the Collector has
  finished its cycle (its program is Skip), every node that was garbage at
  the start of the cycle was in free at some point during it.  pv (l0, \<sigma>0)
  (l, \<sigma>) is the set of values free has taken from the start to \<sigma> (free~).
  Proved in GC_System (system_post_Collector), from Collector_sat.\<close>

theorem result6_post_Collector:
  fixes \<sigma>0 :: "('a::finite,'i::finite) state"
  assumes start: "cvars.s l0 = {}" "nr m0 = {}" "inv_state \<sigma>0"
                 "free \<sigma>0 \<inter> reach (roots \<sigma>0) (hp \<sigma>0) = {}"
    and run: "system_reach (((Collector, l0), (Mutator, m0)), \<sigma>0) ((Skip, l), cm) \<sigma>"
  shows "garbage \<sigma>0 \<subseteq> \<Union>(pv (l0, \<sigma>0) (l, \<sigma>))"
proof -
  have I0: "par_pre (pre_of Collector C_pre) (pre_of Mutator Mut_pre) (coupling C_s M_nr)
              (((Collector, l0), (Mutator, m0)), \<sigma>0)"
    using start by (simp add: system_init_iff)
  from system_post_Collector[OF I0 run] show ?thesis by simp
qed

text \<open>Thesis: consistent(s, \<sigma>), Bad(s, \<sigma>) \<subseteq> new-risk, and inv-\<Sigma> hold in
  every state of every run (Section 4.5.5).  Proved in GC_System
  (system_consistent).\<close>

theorem result7_consistent:
  fixes \<sigma>0 :: "('a::finite,'i::finite) state"
  assumes start: "cvars.s l0 = {}" "nr m0 = {}" "inv_state \<sigma>0"
                 "free \<sigma>0 \<inter> reach (roots \<sigma>0) (hp \<sigma>0) = {}"
    and run: "system_reach (((Collector, l0), (Mutator, m0)), \<sigma>0) (cl, cm) \<sigma>"
  shows "consistent (cvars.s (snd cl)) \<sigma> (nr (snd cm)) \<and> inv_state \<sigma>"
proof -
  have I0: "par_pre (pre_of Collector C_pre) (pre_of Mutator Mut_pre) (coupling C_s M_nr)
              (((Collector, l0), (Mutator, m0)), \<sigma>0)"
    using start by (simp add: system_init_iff)
  from system_consistent[OF I0 run] show ?thesis by (simp add: C_s_def M_nr_def)
qed

text \<open>Thesis: termination.  Each loop of the Collector terminates because its
  so-far relation is well-founded (the second half of Lemmas 5, 6, 10, 13
  and 14: lemma5_so_farMk_wf, lemma6_so_farP_wf, lemma10_so_farM_wf,
  lemma13_so_farU_wf, lemma14_so_farS_wf).  The rules of RG_VDM are for
  partial correctness, so results 2 and 4 do not themselves state
  termination.\<close>

end
