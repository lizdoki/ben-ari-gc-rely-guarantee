(*  GC_System: Collector \<parallel> Mutator for the code (Section 4.5.5; Part 3 of the
    mechanisation, putting Parts 1 and 2 together).

    GC_Parallel proved, from the two specifications alone, that any Collector
    meeting the Collector's specification, in parallel with any Mutator
    meeting the Mutator's, is correct (Collector_par_Mutator_abstract).
    GC_Collector proved that the Collector's code meets its specification
    (Collector_sat), and GC_Mutator that the Mutator's code meets its
    (Mutator_sat).  This theory puts the two together: run as processes
    (collector_process, mutator_process), the two programs are an instance of
    the theorem of Part 1 (Collector_par_Mutator), and its consequences hold
    in every interleaving of the code.

    HOW TO READ THE LABELS.  Each definition and theorem below has a text
    block saying how it relates to the thesis:
      "Thesis:"             it is that part of the thesis;
      "Beyond the thesis:"  the thesis states or argues it informally or not
                            at all; the label says which part of the thesis
                            it makes precise or supports;
      "Mechanisation only:" a helper needed only for the Isabelle proof.
    Section, lemma and theorem numbers are those of the thesis.

      thesis                                           Isabelle
      ---------------------------------------------    --------------------
      the Collector and the Mutator as processes       collector_process,
                                                         mutator_process
      Collector \<parallel> Mutator meets its specification      Collector_par_Mutator
      every Collector step: guar-Collector             system_safety
        (Corollary 2), frees only garbage (Theorem 6)
      every Mutator step satisfies rely-Collector      system_mutator_steps
      consistent(s, \<sigma>) throughout                      system_consistent
      post-Collector once the Collector has finished   system_post_Collector
        (Theorem 7)                                                         *)

theory GC_System
  imports GC_Parallel GC_Collector GC_Mutator
begin

section \<open>Collector \<parallel> Mutator for the code\<close>

subsection \<open>The two programs as processes\<close>

text \<open>Mechanisation only: a program runs as a process whose private state is
  the program still to run together with its private variables (RG_VDM).
  C_s reads the Collector's protected set s, M_nr the Mutator's new-risk.\<close>

definition C_s :: "('a,'i) ccom \<times> ('a,'i) cvars \<Rightarrow> ('a \<times> 'i) set" where
  "C_s cl = cvars.s (snd cl)"

definition M_nr :: "('a,'i) mcom \<times> ('a,'i) mvars \<Rightarrow> ('a \<times> 'i) set" where
  "M_nr cm = nr (snd cm)"

lemma C_s_pair [simp]: "C_s (c,l) = cvars.s l"
  by (simp add: C_s_def)

lemma M_nr_pair [simp]: "M_nr (c,m) = nr m"
  by (simp add: M_nr_def)

text \<open>Thesis: the Collector of Appendix C, run as a process, meets the
  Collector's specification: its rely condition is rely-Collector and every
  step satisfies guar-Collector (with inv-\<Sigma> after it and Lemma 3).  This is
  Collector_sat; in addition inv-\<Sigma> holds in every state, so a step that
  changes nothing also satisfies the guarantee.\<close>

lemma collector_process:
  "rg_sat prog_of (hist_of hC) (pre_of (Collector :: ('a::finite,'i::finite) ccom) C_pre)
          (rely_C C_s) (guar_C C_s) (\<lambda>c0 c. post_of C_post c0 c \<and> inv_state (snd c))"
proof -
  have V: "rg_sat prog_of (hist_of hC) (pre_of (Collector :: ('a,'i) ccom) C_pre)
              (rely_of (rely_C cvars.s)) (guar_of (guar_C cvars.s)) (post_of C_post)"
    by (rule vdm_rg_sat[OF Collector_sat])
  have V': "rg_sat prog_of (hist_of hC) (pre_of (Collector :: ('a,'i) ccom) C_pre)
              (rely_C C_s) (guar_of (guar_C cvars.s)) (post_of C_post)"
  proof (rule rg_conseq[OF V])
    fix cl :: "('a,'i) ccom \<times> ('a,'i) cvars" and \<sigma> \<sigma>' :: "('a,'i) state"
    assume "rely_C C_s cl \<sigma> \<sigma>'"
    then show "rely_of (rely_C cvars.s) cl \<sigma> \<sigma>'" by (cases cl) (simp add: rely_C_def)
  qed simp_all
  show ?thesis
  proof (rule rg_sat_guar_inv[OF V', where I = "\<lambda>c. inv_state (snd c)"])
    fix c :: "(('a,'i) ccom \<times> ('a,'i) cvars, ('a,'i) state) rg_conf"
    assume "pre_of Collector C_pre c"
    then show "inv_state (snd c)" by (cases c) (auto simp: C_pre_def)
  next
    fix cl :: "('a,'i) ccom \<times> ('a,'i) cvars" and \<sigma> \<sigma>' :: "('a,'i) state"
    assume "inv_state (snd (cl,\<sigma>))" and "rely_C C_s cl \<sigma> \<sigma>'"
    then show "inv_state (snd (hist_of hC cl \<sigma>', \<sigma>'))" by (simp add: rely_C_def env_step_def)
  next
    fix cl cl' :: "('a,'i) ccom \<times> ('a,'i) cvars" and \<sigma> \<sigma>' :: "('a,'i) state"
    assume I: "inv_state (snd (cl,\<sigma>))" and G: "guar_of (guar_C cvars.s) (cl,\<sigma>) (cl',\<sigma>')"
    obtain c l where cl: "cl = (c,l)" by (cases cl)
    obtain c' l' where cl': "cl' = (c',l')" by (cases cl')
    from G cl cl' have "(l',\<sigma>') = (l,\<sigma>) \<or> guar_C cvars.s (l,\<sigma>) (l',\<sigma>')" by simp
    then show "inv_state (snd (hist_of hC cl' \<sigma>', \<sigma>'))"
      using I unfolding guar_C_def by auto
  next
    fix c c' :: "(('a,'i) ccom \<times> ('a,'i) cvars, ('a,'i) state) rg_conf"
    assume I: "inv_state (snd c)" and G: "guar_of (guar_C cvars.s) c c'"
    obtain cl \<sigma> where c: "c = (cl,\<sigma>)" by (cases c)
    obtain cl' \<sigma>' where c': "c' = (cl',\<sigma>')" by (cases c')
    obtain p l where cl: "cl = (p,l)" by (cases cl)
    obtain p' l' where cl': "cl' = (p',l')" by (cases cl')
    from G c c' cl cl' have D: "(l',\<sigma>') = (l,\<sigma>) \<or> guar_C cvars.s (l,\<sigma>) (l',\<sigma>')" by simp
    from I c have inv: "inv_state \<sigma>" by simp
    from D show "guar_C C_s c c'"
    proof
      assume "(l',\<sigma>') = (l,\<sigma>)"
      then have "l' = l" "\<sigma>' = \<sigma>" by simp_all
      then show ?thesis using inv c c' cl cl' guar_Collector_refl unfolding guar_C_def by simp
    next
      assume "guar_C cvars.s (l,\<sigma>) (l',\<sigma>')"
      then show ?thesis using c c' cl cl' unfolding guar_C_def by simp
    qed
  qed
qed

text \<open>Thesis: the Mutator of Algorithm 12, run as a process, meets the
  Mutator's specification: rely guar-Collector, guar guar-Mutator
  (Mutator_sat); inv-\<Sigma> holds in every state.\<close>

lemma mutator_process:
  "rg_sat prog_of (hist_of no_hist) (pre_of (Mutator :: ('a::finite,'i::finite) mcom) Mut_pre)
          rely_M (guar_M M_nr) (\<lambda>c0 c. inv_state (snd c))"
proof -
  have V: "rg_sat prog_of (hist_of no_hist) (pre_of (Mutator :: ('a,'i) mcom) Mut_pre)
              (rely_of rely_M) (guar_of (guar_M nr)) (post_of (\<lambda>k0 k. True))"
    by (rule vdm_rg_sat[OF Mutator_sat])
  have V': "rg_sat prog_of (hist_of no_hist) (pre_of (Mutator :: ('a,'i) mcom) Mut_pre)
              rely_M (guar_of (guar_M nr)) (post_of (\<lambda>k0 k. True))"
  proof (rule rg_conseq[OF V])
    fix cm :: "('a,'i) mcom \<times> ('a,'i) mvars" and \<sigma> \<sigma>' :: "('a,'i) state"
    assume "rely_M cm \<sigma> \<sigma>'"
    then show "rely_of rely_M cm \<sigma> \<sigma>'" by (cases cm) (simp add: rely_M_def)
  qed simp_all
  have W: "rg_sat prog_of (hist_of no_hist) (pre_of (Mutator :: ('a,'i) mcom) Mut_pre)
              rely_M (guar_M M_nr) (\<lambda>c0 c. post_of (\<lambda>k0 k. True) c0 c \<and> inv_state (snd c))"
  proof (rule rg_sat_guar_inv[OF V', where I = "\<lambda>c. inv_state (snd c)"])
    fix c :: "(('a,'i) mcom \<times> ('a,'i) mvars, ('a,'i) state) rg_conf"
    assume "pre_of Mutator Mut_pre c"
    then show "inv_state (snd c)" by (cases c) (auto simp: Mut_pre_def)
  next
    fix cm :: "('a,'i) mcom \<times> ('a,'i) mvars" and \<sigma> \<sigma>' :: "('a,'i) state"
    assume "inv_state (snd (cm,\<sigma>))" and "rely_M cm \<sigma> \<sigma>'"
    then show "inv_state (snd (hist_of no_hist cm \<sigma>', \<sigma>'))" by (simp add: rely_M_def)
  next
    fix cm cm' :: "('a,'i) mcom \<times> ('a,'i) mvars" and \<sigma> \<sigma>' :: "('a,'i) state"
    assume I: "inv_state (snd (cm,\<sigma>))" and G: "guar_of (guar_M nr) (cm,\<sigma>) (cm',\<sigma>')"
    obtain c m where cm: "cm = (c,m)" by (cases cm)
    obtain c' m' where cm': "cm' = (c',m')" by (cases cm')
    from G cm cm' have "(m',\<sigma>') = (m,\<sigma>) \<or> guar_M nr (m,\<sigma>) (m',\<sigma>')" by simp
    then show "inv_state (snd (hist_of no_hist cm' \<sigma>', \<sigma>'))"
      using I unfolding guar_M_def guar_Mutator_def by auto
  next
    fix c c' :: "(('a,'i) mcom \<times> ('a,'i) mvars, ('a,'i) state) rg_conf"
    assume I: "inv_state (snd c)" and G: "guar_of (guar_M nr) c c'"
    obtain cm \<sigma> where c: "c = (cm,\<sigma>)" by (cases c)
    obtain cm' \<sigma>' where c': "c' = (cm',\<sigma>')" by (cases c')
    obtain p m where cm: "cm = (p,m)" by (cases cm)
    obtain p' m' where cm': "cm' = (p',m')" by (cases cm')
    from G c c' cm cm' have D: "(m',\<sigma>') = (m,\<sigma>) \<or> guar_M nr (m,\<sigma>) (m',\<sigma>')" by simp
    from I c have inv: "inv_state \<sigma>" by simp
    from D show "guar_M M_nr c c'"
    proof
      assume "(m',\<sigma>') = (m,\<sigma>)"
      then have "m' = m" "\<sigma>' = \<sigma>" by simp_all
      then show ?thesis using inv c c' cm cm' unfolding guar_M_def guar_Mutator_def by simp
    next
      assume "guar_M nr (m,\<sigma>) (m',\<sigma>')"
      then show ?thesis using c c' cm cm' unfolding guar_M_def by simp
    qed
  qed
  show ?thesis by (rule rg_conseq[OF W]) simp_all
qed

subsection \<open>The parallel composition\<close>

text \<open>Thesis: the other assumptions of Collector_par_Mutator_abstract hold: the
  Collector starts with s = {} (its pre condition), and the history variable
  (the possible values of free) is separate from s and new-risk.\<close>

lemma collector_starts_empty:
  "pre_of (Collector :: ('a::finite,'i::finite) ccom) C_pre c \<Longrightarrow> C_s (fst c) = {}"
  by (cases c) (auto simp: C_pre_def)

lemma collector_hist_s: "C_s (hist_of hC cl \<sigma>) = C_s cl"
  by (cases cl) simp

lemma mutator_hist_nr: "M_nr (hist_of no_hist cm \<sigma>) = M_nr cm"
  by (cases cm) (simp add: no_hist_def)

text \<open>Thesis: Collector \<parallel> Mutator meets its specification.  The Collector of
  Appendix C meets the Collector's specification (Collector_sat, as
  collector_process) and the Mutator of Algorithm 12 meets the Mutator's
  (Mutator_sat, as mutator_process), so Collector_par_Mutator_abstract
  applies:
    {pre-Collector \<and> pre-Mutator \<and> consistent, false}
        Collector \<parallel> Mutator
    {guar-Collector \<or> guar-Mutator, post-Collector \<and> consistent}.\<close>

theorem Collector_par_Mutator:
  "rg_sat (par prog_of prog_of) (hpar (hist_of hC) (hist_of no_hist))
          (par_pre (pre_of (Collector :: ('a::finite,'i::finite) ccom) C_pre)
                   (pre_of (Mutator :: ('a,'i) mcom) Mut_pre) (coupling C_s M_nr))
          no_env
          (par_guar (guar_C C_s) (guar_M M_nr))
          (par_post (\<lambda>c0 c. post_of C_post c0 c \<and> inv_state (snd c)) (\<lambda>c0 c. inv_state (snd c))
                    (coupling C_s M_nr))"
proof (rule Collector_par_Mutator_abstract[OF collector_process mutator_process])
  fix c :: "(('a,'i) ccom \<times> ('a,'i) cvars, ('a,'i) state) rg_conf"
  assume "pre_of Collector C_pre c"
  then show "C_s (fst c) = {}" by (rule collector_starts_empty)
next
  fix cl :: "('a,'i) ccom \<times> ('a,'i) cvars" and \<sigma> :: "('a,'i) state"
  show "C_s (hist_of hC cl \<sigma>) = C_s cl" by (rule collector_hist_s)
next
  fix cm :: "('a,'i) mcom \<times> ('a,'i) mvars" and \<sigma> :: "('a,'i) state"
  show "M_nr (hist_of no_hist cm \<sigma>) = M_nr cm" by (rule mutator_hist_nr)
qed

text \<open>Mechanisation only: the same facts as an instance of the locale
  gc_parallel (GC_Parallel), so that its other results (collector_safe,
  mutator_step, invariants) apply to the code.\<close>

lemma system_instance:
  "gc_parallel prog_of (hist_of hC) C_s (pre_of (Collector :: ('a::finite,'i::finite) ccom) C_pre)
               (\<lambda>c0 c. post_of C_post c0 c \<and> inv_state (snd c))
               prog_of (hist_of no_hist) M_nr (pre_of (Mutator :: ('a,'i) mcom) Mut_pre)
               (\<lambda>c0 c. inv_state (snd c))"
proof (rule gc_parallel.intro[OF collector_process mutator_process])
  fix c :: "(('a,'i) ccom \<times> ('a,'i) cvars, ('a,'i) state) rg_conf"
  assume "pre_of Collector C_pre c"
  then show "C_s (fst c) = {}" by (rule collector_starts_empty)
next
  fix cl :: "('a,'i) ccom \<times> ('a,'i) cvars" and \<sigma> :: "('a,'i) state"
  show "C_s (hist_of hC cl \<sigma>) = C_s cl" by (rule collector_hist_s)
next
  fix cm :: "('a,'i) mcom \<times> ('a,'i) mvars" and \<sigma> :: "('a,'i) state"
  show "M_nr (hist_of no_hist cm \<sigma>) = M_nr cm" by (rule mutator_hist_nr)
qed

text \<open>Thesis: the starting states: the Collector at the start of its cycle
  with s = {}, the Mutator between operations with new-risk = {}, inv-\<Sigma>,
  and no free node reachable.  Consistency holds there (item 1 at the end of
  Section 4.5.5).\<close>

lemma system_init_iff:
  "par_pre (pre_of Collector C_pre) (pre_of Mutator Mut_pre) (coupling C_s M_nr) (((c,l),(p,m)),\<sigma>) \<longleftrightarrow>
     c = Collector \<and> cvars.s l = {} \<and> p = Mutator \<and> nr m = {} \<and> inv_state \<sigma> \<and>
     free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}"
  unfolding par_pre_def C_pre_def Mut_pre_def coupling_def consistent_def Bad_def
  by auto

text \<open>Mechanisation only: the configurations of Collector \<parallel> Mutator reached
  from c0 by some interleaving.\<close>

abbreviation system_reach where
  "system_reach c0 cm \<sigma> \<equiv> rg_reach (par prog_of prog_of) no_env (hpar (hist_of hC) (hist_of no_hist)) c0 cm \<sigma>"

text \<open>Thesis: Corollary 2 and Theorem 6 in every interleaving: every step of
  the Collector satisfies guar-Collector, and in particular only adds
  garbage to free (safety).\<close>

theorem system_safety:
  assumes I0: "par_pre (pre_of (Collector :: ('a::finite,'i::finite) ccom) C_pre)
                       (pre_of (Mutator :: ('a,'i) mcom) Mut_pre) (coupling C_s M_nr) c0"
    and R: "system_reach c0 (cl,cm) \<sigma>" and S: "prog_of (cl,\<sigma>) (cl',\<sigma>')"
  shows "free \<sigma>' - free \<sigma> \<subseteq> garbage \<sigma>" and "guar_Collector \<sigma> \<sigma>'"
proof -
  show "free \<sigma>' - free \<sigma> \<subseteq> garbage \<sigma>"
    by (rule gc_parallel.collector_safe(1)[OF system_instance I0 R S])
  show "guar_Collector \<sigma> \<sigma>'"
    by (rule gc_parallel.collector_safe(2)[OF system_instance I0 R S])
qed

text \<open>Thesis: the relationship Section 4.5.5 requires, in every interleaving:
  every step of the Mutator satisfies guar-Mutator, and hence rely-Collector
  for the Collector's current s.\<close>

theorem system_mutator_steps:
  assumes I0: "par_pre (pre_of (Collector :: ('a::finite,'i::finite) ccom) C_pre)
                       (pre_of (Mutator :: ('a,'i) mcom) Mut_pre) (coupling C_s M_nr) c0"
    and R: "system_reach c0 (cl,cm) \<sigma>" and S: "prog_of (cm,\<sigma>) (cm',\<sigma>')"
  shows "guar_Mutator (M_nr cm) \<sigma> (M_nr cm') \<sigma>'" and "rely_Collector (C_s cl) \<sigma> \<sigma>'"
proof -
  show "guar_Mutator (M_nr cm) \<sigma> (M_nr cm') \<sigma>'"
    by (rule gc_parallel.mutator_step(1)[OF system_instance I0 R S])
  show "rely_Collector (C_s cl) \<sigma> \<sigma>'"
    by (rule gc_parallel.mutator_step(2)[OF system_instance I0 R S])
qed

text \<open>Thesis: in every state of every interleaving, consistent(s, \<sigma>) holds
  (Section 4.5.5) and so does inv-\<Sigma>; and once the Collector has finished
  its cycle, post-Collector holds (Theorem 7): every node that was garbage
  at the start was in free at some point during the cycle.\<close>

theorem system_consistent:
  assumes I0: "par_pre (pre_of (Collector :: ('a::finite,'i::finite) ccom) C_pre)
                       (pre_of (Mutator :: ('a,'i) mcom) Mut_pre) (coupling C_s M_nr) c0"
    and R: "system_reach c0 (cl,cm) \<sigma>"
  shows "consistent (C_s cl) \<sigma> (M_nr cm) \<and> inv_state \<sigma>"
proof -
  have "coupling C_s M_nr cl cm \<sigma> \<and>
        (post_of C_post (fst (fst c0), snd c0) (cl,\<sigma>) \<and> inv_state (snd (cl,\<sigma>))) \<and>
        inv_state (snd (cm,\<sigma>))"
    by (rule gc_parallel.invariants[OF system_instance I0 R])
  then show ?thesis unfolding coupling_def by simp
qed

theorem system_post_Collector:
  assumes I0: "par_pre (pre_of (Collector :: ('a::finite,'i::finite) ccom) C_pre)
                       (pre_of (Mutator :: ('a,'i) mcom) Mut_pre) (coupling C_s M_nr) c0"
    and R: "system_reach c0 ((Skip,l),cm) \<sigma>"
  shows "garbage (snd c0) \<subseteq> \<Union>(pv (snd (fst (fst c0)), snd c0) (l,\<sigma>))"
proof -
  from gc_parallel.invariants[OF system_instance I0 R]
  have P: "post_of C_post (fst (fst c0), snd c0) ((Skip,l),\<sigma>)" by blast
  obtain p0 l0 where pl: "fst (fst c0) = (p0,l0)" by (cases "fst (fst c0)")
  from P pl have "C_post (l0, snd c0) (l,\<sigma>)" by simp
  then show ?thesis using pl unfolding C_post_def post_Collector_def by simp
qed

end
