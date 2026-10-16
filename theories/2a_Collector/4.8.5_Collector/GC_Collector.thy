(*  GC_Collector: the Collector's code meets its specification (Section
    4.8.5).

    Collector = Unmark; Mark; Sweep.  The three phases meet their
    specifications (Unmark_sat, Mark_sat, Sweep_sat); every step of each is a
    step of step-Collector, so it satisfies guar-Collector (Corollary 2 and
    Lemma 3); and Theorem 7 gives post-Collector.  This is "the Collector
    meets its specification" (Collector_sat), which GC_System puts together
    with Collector_par_Mutator_abstract (GC_Parallel).

    HOW TO READ THE LABELS.  Each definition and theorem below, or each group
    of them, has a text block saying how it relates to the thesis:
      "Thesis:"             it is that part of the thesis;
      "Beyond the thesis:"  the thesis states or argues it informally or not
                            at all; the label says which part of the thesis
                            it makes precise or supports;
      "Mechanisation only:" a helper needed only for the Isabelle proof.
    Section, lemma and theorem numbers are those of the thesis.

      thesis                                        Isabelle
      ------------------------------------------    ------------------------
      the Collector's pre and post conditions       C_pre, C_post
      every step is a step of step-Collector        C_step, Unmark_C, Mark_C,
                                                      Sweep_C
      the Collector meets its specification         Collector_sat
      Theorem 6 for the Collector's code            Collector_safe        *)

theory GC_Collector
  imports GC_Collector_Post GC_Sweep_Sat
begin

section \<open>The Collector meets its specification (Section 4.8.5)\<close>

text \<open>Thesis: the Collector's specification (Section 4.4, Appendix C):
    pre  s = {}
    rely rely-Collector
    guar guar-Collector
    post garbage \<subseteq> \<Union>free~                                   (post-Collector)
  for Collector \<triangleq> Unmark; Mark; Sweep.  In Isabelle the pre condition also
  states inv-\<Sigma>, and the guarantee is guar_C: guar-Collector, with inv-\<Sigma>
  after the step and Bad(s', \<sigma>') \<subseteq> Bad(s, \<sigma>) (Lemma 3), which the
  composition with the Mutator uses (Section 4.5.5).\<close>

definition C_pre :: "('a,'i) cconf \<Rightarrow> bool" where
  "C_pre = (\<lambda>(l,\<sigma>). s l = {} \<and> inv_state \<sigma>)"

definition C_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "C_post = (\<lambda>k0 k. post_Collector (snd k0) (pv k0 k))"

text \<open>Thesis: every program step of the Collector is a step of one of its
  three phases (step-Collector, Section 4.7.2), and stays within \<Sigma>.\<close>

definition C_step :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "C_step = (\<lambda>(l,\<sigma>) (l',\<sigma>'). step_Collector (s l) \<sigma> (s l') \<sigma>' \<and> inv_state \<sigma>')"

text \<open>Thesis: Corollary 2 (every step satisfies guar-Collector) and Lemma 3 (a
  step does not increase Bad): a step of step-Collector satisfies guar_C.\<close>

lemma C_step_guar:
  assumes "C_step (l,\<sigma>) (l',\<sigma>')"
  shows "guar_C s (l,\<sigma>) (l',\<sigma>')"
proof -
  from assms have S: "step_Collector (s l) \<sigma> (s l') \<sigma>'" and inv': "inv_state \<sigma>'"
    unfolding C_step_def by simp_all
  have "guar_Collector \<sigma> \<sigma>'" by (rule corollary2_step_guar[OF S])
  moreover have "Bad (s l') \<sigma>' \<subseteq> Bad (s l) \<sigma>" by (rule lemma3_prog_Bad[OF S])
  ultimately show ?thesis using inv' unfolding guar_C_def by simp
qed

text \<open>Mechanisation only: the history variable only records, throughout any
  operation whose steps leave it alone.\<close>

lemma hist_ok_add:
  assumes V: "coll_sat P (c :: ('a,'i) ccom) G Q"
    and GF: "\<And>k k'. G k k' \<Longrightarrow> Fv (fst k') = Fv (fst k)"
  shows "coll_sat P c G (\<lambda>k0 k. Q k0 k \<and> hist_ok k0 k)"
proof (rule rule_trace_h[OF V])
  fix k :: "('a,'i) cconf" show "hist_ok k k" by (rule hist_ok_refl)
next
  fix k0 k k' :: "('a,'i) cconf" assume "hist_ok k0 k" and "envC k k'"
  from hist_ok_env[OF this] show "hist_ok k0 k'" by blast
next
  fix k0 k k' :: "('a,'i) cconf" assume H: "hist_ok k0 k" and G: "G k k'"
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
  from GF[OF G] k k' have F: "Fv l' = Fv l" by simp
  from hist_ok_step[OF H[unfolded k] F] k' show "hist_ok k0 (hupd hC k')" by simp
qed

text \<open>Thesis: the three phases, each meeting its specification, with what each
  gives the next: Unmark ends with inv-\<Sigma> and s = {}, so invB holds for
  Mark (Section 4.7); Mark ends with reach(roots, hp) \<subseteq> marked, which is
  pre-Sweep (Section 4.8.4).  Every step of each phase is a step of
  step-Collector that stays in \<Sigma>.\<close>

lemma Unmark_C:
  "coll_sat U_pre (Unmark :: ('a,'i) ccom) C_step (\<lambda>k0 k. (U_post k0 k \<and> U_inv k) \<and> hist_ok k0 k)"
proof -
  have V: "coll_sat U_pre (Unmark :: ('a,'i) ccom) (\<lambda>k k'. U_guar k k' \<and> U_inv k)
             (\<lambda>k0 k. (U_post k0 k \<and> U_inv k) \<and> hist_ok k0 k)"
    by (rule hist_ok_add[OF Unmark_sat]) (auto simp: U_guar_def split_beta)
  show ?thesis
  proof (rule rule_weaken[OF V])
    fix k k' :: "('a,'i) cconf" assume G: "U_guar k k' \<and> U_inv k"
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from G k k' have G': "U_guar (l,\<sigma>) (l',\<sigma>')" and I: "U_pre (l,\<sigma>)" by (simp_all add: U_inv_def)
    from I have s0: "s l = {}" unfolding U_pre_def by simp
    have "guar_Unmark (s l) \<sigma> (s l') \<sigma>'" by (rule U_guar_Unmark[OF G' s0])
    then have "step_Collector (s l) \<sigma> (s l') \<sigma>'" unfolding step_Collector_def by simp
    moreover have "inv_state \<sigma>'" using U_guar_pre[OF G' I] unfolding U_pre_def by simp
    ultimately show "C_step k k'" using k k' unfolding C_step_def by simp
  qed simp_all
qed

lemma Mark_C:
  "coll_sat M_pre (Mark :: ('a::finite,'i::finite) ccom) C_step
            (\<lambda>k0 k. (M_post k0 k \<and> inv_state (snd k)) \<and> hist_ok k0 k)"
proof -
  have IS: "stable hC (rely_C s) (\<lambda>k::('a,'i) cconf. inv_state (snd k))"
  proof (rule stableC)
    fix l :: "('a,'i) cvars" and \<sigma> \<sigma>' :: "('a,'i) state"
    assume I: "inv_state (snd (l,\<sigma>))" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    from envs_inv_state[OF E] I show "inv_state (snd (hC l \<sigma>', \<sigma>'))" by simp
  qed
  have V1: "coll_sat M_pre (Mark :: ('a,'i) ccom) (\<lambda>k k'. M_guar k k' \<and> inv_state (snd k))
              (\<lambda>k0 k. M_post k0 k \<and> inv_state (snd k))"
  proof (rule rule_inv[OF Mark_sat _ IS])
    fix k :: "('a,'i) cconf" assume "M_pre k"
    then show "inv_state (snd k)" by (cases k) (simp add: M_pre_def)
  next
    fix k k' :: "('a,'i) cconf" assume I: "inv_state (snd k)" and G: "M_guar k k'"
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from G k k' have GM: "guar_Mark (s l) \<sigma> (s l') \<sigma>'" unfolding M_guar_def by simp
    from guar_Mark_inv_state[OF GM] I k k' show "inv_state (snd k')" by simp
  qed
  have V: "coll_sat M_pre (Mark :: ('a,'i) ccom) (\<lambda>k k'. M_guar k k' \<and> inv_state (snd k))
             (\<lambda>k0 k. (M_post k0 k \<and> inv_state (snd k)) \<and> hist_ok k0 k)"
    by (rule hist_ok_add[OF V1]) (auto simp: M_guar_def split_beta)
  show ?thesis
  proof (rule rule_weaken[OF V])
    fix k k' :: "('a,'i) cconf" assume G: "M_guar k k' \<and> inv_state (snd k)"
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from G k k' have GM: "guar_Mark (s l) \<sigma> (s l') \<sigma>'" and inv: "inv_state \<sigma>"
      unfolding M_guar_def by simp_all
    have "step_Collector (s l) \<sigma> (s l') \<sigma>'" using GM unfolding step_Collector_def by simp
    moreover have "inv_state \<sigma>'" by (rule guar_Mark_inv_state[OF GM inv])
    ultimately show "C_step k k'" using k k' unfolding C_step_def by simp
  qed simp_all
qed

lemma Sweep_C:
  "coll_sat S_J (Sweep :: ('a::finite,'i::finite) ccom) C_step (\<lambda>k0 k. S_post k0 k \<and> S_J k)"
proof (rule rule_weaken[OF Sweep_sat])
  fix k k' :: "('a,'i) cconf" assume G: "S_guar k k' \<and> S_J k"
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
  from G k k' have "S_guar (l,\<sigma>) (l',\<sigma>')" and "S_J (l,\<sigma>)" by simp_all
  from S_guar_step[OF this] k k' show "C_step k k'" unfolding C_step_def by simp
qed simp_all

text \<open>Thesis: Theorem 7 (Collector's post condition): with \<sigma>U, \<sigma>M, \<sigma>S the
  states at the start of Unmark, Mark and Sweep,
    post-Unmark(\<sigma>U, \<sigma>M) \<and> post-Mark(\<sigma>M, \<sigma>S) \<and> post-Sweep(\<sigma>S, \<sigma>U')
                                         \<Rightarrow> post-Collector(\<sigma>U, \<sigma>U'),
  where "the possible values between \<sigma>S and \<sigma>U' are contained within the
  possible values between \<sigma>U and \<sigma>U'" (hist_ok).  Lemma 20 also uses, from
  Unmark, that no pointer leads from the old free or reachable region into
  the old garbage (Sublemma 1).\<close>

theorem Collector_sat:
  "coll_sat C_pre (Collector :: ('a::finite,'i::finite) ccom) (guar_C s) C_post"
proof -
  have MS: "coll_sat M_pre (Seq Mark Sweep :: ('a,'i) ccom) C_step
              (seq_post (\<lambda>k0 k. (M_post k0 k \<and> inv_state (snd k)) \<and> hist_ok k0 k)
                        (\<lambda>k0 k. S_post k0 k \<and> S_J k))"
  proof (rule rule_seq[OF Mark_C Sweep_C])
    fix k0 k :: "('a,'i) cconf"
    assume "M_pre k0" and Q: "(M_post k0 k \<and> inv_state (snd k)) \<and> hist_ok k0 k"
    then show "S_J k"
      by (cases k0, cases k) (simp add: M_post_def post_Mark_def S_J_def inv_safe_def)
  qed
  have UMS: "coll_sat U_pre (Collector :: ('a,'i) ccom) C_step
               (seq_post (\<lambda>k0 k. (U_post k0 k \<and> U_inv k) \<and> hist_ok k0 k)
                 (seq_post (\<lambda>k0 k. (M_post k0 k \<and> inv_state (snd k)) \<and> hist_ok k0 k)
                           (\<lambda>k0 k. S_post k0 k \<and> S_J k)))"
    unfolding Collector_def
  proof (rule rule_seq[OF Unmark_C MS])
    fix k0 k :: "('a,'i) cconf"
    assume "U_pre k0" and Q: "(U_post k0 k \<and> U_inv k) \<and> hist_ok k0 k"
    then show "M_pre k"
      by (cases k) (simp add: U_inv_def U_pre_def M_pre_def invB_empty)
  qed
  have Q: "C_post k0 k"
    if "seq_post (\<lambda>k0 k. (U_post k0 k \<and> U_inv k) \<and> hist_ok k0 k)
          (seq_post (\<lambda>k0 k. (M_post k0 k \<and> inv_state (snd k)) \<and> hist_ok k0 k)
                    (\<lambda>k0 k. S_post k0 k \<and> S_J k)) k0 k"
    for k0 k :: "('a,'i) cconf"
  proof -
    from that obtain k1 k2 where U: "U_post k0 k1" and H1: "hist_ok k0 k1"
      and M: "M_post k1 k2" and H2: "hist_ok k1 k2" and S: "S_post k2 k"
      unfolding seq_post_def by blast
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
    obtain l2 \<sigma>2 where k2: "k2 = (l2,\<sigma>2)" by (cases k2)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from U k0 k1 have PU: "post_Unmark \<sigma>0 \<sigma>1" and NP: "no_new_ptr \<sigma>0 \<sigma>1"
      unfolding U_post_def by simp_all
    from M k1 k2 have PM: "post_Mark \<sigma>1 (s l2) \<sigma>2" unfolding M_post_def by simp
    from S k2 k have PS: "post_Sweep \<sigma>2 (pv k2 k) \<sigma>" and H3: "hist_ok k2 k"
      unfolding S_post_def by simp_all
    from hist_ok_trans[OF H1 H2] have H12: "hist_ok k0 k2" by blast
    from hist_ok_trans[OF H12 H3] have F: "pv k2 k \<subseteq> pv k0 k" by blast
    have "post_Collector \<sigma>0 (pv k0 k)" by (rule theorem7_post_Collector[OF PU NP PM PS F])
    with k0 show ?thesis unfolding C_post_def by simp
  qed
  show ?thesis
  proof (rule rule_weaken[OF UMS])
    fix k :: "('a,'i) cconf" assume "C_pre k"
    then show "U_pre k" by (cases k) (simp add: C_pre_def U_pre_def)
  next
    fix k k' :: "('a,'i) cconf" assume "C_step k k'"
    then show "guar_C s k k'" by (cases k, cases k') (simp add: C_step_guar)
  next
    fix k0 k :: "('a,'i) cconf" assume "C_pre k0"
      and "seq_post (\<lambda>k0 k. (U_post k0 k \<and> U_inv k) \<and> hist_ok k0 k)
             (seq_post (\<lambda>k0 k. (M_post k0 k \<and> inv_state (snd k)) \<and> hist_ok k0 k)
                       (\<lambda>k0 k. S_post k0 k \<and> S_J k)) k0 k"
    then show "C_post k0 k" by (blast intro: Q)
  qed
qed

text \<open>Thesis: Theorem 6 (safety), read off the specification: every step of
  the Collector, in any computation from a state where its pre condition
  holds, whatever the environment does within rely-Collector, adds only
  garbage to free.\<close>

corollary Collector_safe:
  assumes "C_pre k0" and "creach hC (rely_C s) (Collector :: ('a::finite,'i::finite) ccom) k0 c k"
    and "cstep c k c' k'"
  shows "free (snd k') - free (snd k) \<subseteq> garbage (snd k)"
proof -
  have "k' = k \<or> guar_C s k k'" by (rule vdmD_guar[OF Collector_sat assms])
  then show ?thesis
  proof
    assume "k' = k" then show ?thesis by simp
  next
    assume "guar_C s k k'"
    then have "guar_Collector (snd k) (snd k')" unfolding guar_C_def by simp
    then show ?thesis unfolding guar_Collector_def by blast
  qed
qed

text \<open>Mechanisation only: the names of the Collector's private variables are
  short (as in the thesis); outside this theory they are written with the
  record name, e.g. cvars.s.\<close>

hide_const (open) cvars.consid cvars.checked cvars.mc cvars.s cvars.x cvars.i cvars.cleared cvars.Fv
  cvars.consid_update cvars.checked_update cvars.mc_update cvars.s_update cvars.x_update
  cvars.i_update cvars.cleared_update cvars.Fv_update

end
