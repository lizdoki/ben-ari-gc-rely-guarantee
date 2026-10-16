(*  GC_Mark_Sat: Mark-kids, Propagate and Mark meet their specifications
    (Section 4.8.1).

    For each operation: its specification (Appendix C); the test, inv and
    so-far of its loop; that inv and so-far hold despite interference; the
    statements of the loop body one by one; and the operation meeting its
    specification, by the rules of RG_VDM with the lemmas and theorems of
    GC_Mark.  That Mark's post condition holds despite interference uses
    Lemma 15 (Section 4.8.4, GC_Safety).

    Some names.  For an operation X of Appendix C, X_pre, X_guar and X_post
    are its specification and X_sat states that X meets it:
      coll_sat p X g q  is  {p, rely-Collector} X {g, q}.
    For a loop, X_test, X_inv and X_sofar are test, inv and so-far.  An
    atomic statement st has its own post condition st_post.  Every guarantee
    also says which private variables the operation leaves alone (its frame,
    which VDM gives by the ext and owns clauses).

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
      Mark-kids meets its specification             MarkKids_sat
      Propagate meets its specification             Propagate_sat
      Mark meets its specification                  Mark_sat              *)

theory GC_Mark_Sat
  imports GC_Mark GC_Code GC_Safety
begin

section \<open>Interference and the safety invariant (Lemma 15)\<close>

text \<open>Thesis: Lemma 15 (an environment step preserves inv-safe), together with
  the observation of Section 4.8.3 that while inv-safe holds interference
  marks nothing new ("no environment steps change marked during this
  phase").\<close>

lemma envs_inv_safe:
  assumes E: "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>" and IS: "inv_safe \<sigma>"
  shows "inv_safe \<sigma>' \<and> marked \<sigma>' = marked \<sigma>"
proof (cases "\<sigma>' = \<sigma>")
  case True
  with IS show ?thesis by simp
next
  case False
  with E have ES: "env_step S \<sigma> \<sigma>'" by simp
  then have inv: "inv_state \<sigma>" and R: "rely_Collector S \<sigma> \<sigma>'" unfolding env_step_def by blast+
  have "inv_safe \<sigma>'" by (rule lemma15_env_inv_safe[OF inv R IS])
  moreover have "marked \<sigma>' = marked \<sigma>"
    using envs_new_marks[OF E] envs_marked[OF E] IS unfolding inv_safe_def by blast
  ultimately show ?thesis by blast
qed

text \<open>Mechanisation only: the same, for an environment step alone.\<close>

lemmas env_inv_safe = envs_inv_safe[OF disjI1]

text \<open>Mechanisation only: what holds after any number of environment steps:
  the shared state changes only as rely-Collector allows, and inv-\<Sigma> and
  inv-safe are kept (Lemma 15).\<close>

lemma envC_star_state:
  assumes RS: "envC\<^sup>*\<^sup>* k0 k"
  shows "marked (snd k0) \<subseteq> marked (snd k)" "garbage (snd k0) \<subseteq> garbage (snd k)"
    "roots (snd k) = roots (snd k0)" "free (snd k) \<subseteq> free (snd k0)"
    "inv_state (snd k0) \<Longrightarrow> inv_state (snd k)"
    "inv_safe (snd k0) \<Longrightarrow> inv_safe (snd k) \<and> marked (snd k) = marked (snd k0)"
proof -
  have E: "env_step (s (fst k1)) (snd k1) (snd k2) \<or> snd k2 = snd k1" if "envC k1 k2" for k1 k2
    using that by (cases k1, cases k2) (simp add: rely_C_def)
  show "marked (snd k0) \<subseteq> marked (snd k)"
    by (rule rtranclp_trace[OF RS, where T = "\<lambda>k0 k. marked (snd k0) \<subseteq> marked (snd k)"])
       (auto dest!: E envs_marked)
  show "garbage (snd k0) \<subseteq> garbage (snd k)"
    by (rule rtranclp_trace[OF RS, where T = "\<lambda>k0 k. garbage (snd k0) \<subseteq> garbage (snd k)"])
       (auto dest!: E envs_garbage)
  show "roots (snd k) = roots (snd k0)"
    by (rule rtranclp_trace[OF RS, where T = "\<lambda>k0 k. roots (snd k) = roots (snd k0)"])
       (auto dest!: E envs_roots)
  show "free (snd k) \<subseteq> free (snd k0)"
    by (rule rtranclp_trace[OF RS, where T = "\<lambda>k0 k. free (snd k) \<subseteq> free (snd k0)"])
       (auto dest!: E envs_free)
  show "inv_state (snd k)" if "inv_state (snd k0)"
    by (rule rtranclp_trace[OF RS, where T = "\<lambda>k0 k. inv_state (snd k)"])
       (auto simp: that dest!: E envs_inv_state)
  show "inv_safe (snd k) \<and> marked (snd k) = marked (snd k0)" if "inv_safe (snd k0)"
    by (rule rtranclp_trace[OF RS, where T = "\<lambda>k0 k. inv_safe (snd k) \<and> marked (snd k) = marked (snd k0)"])
       (auto simp: that dest!: E envs_inv_safe)
qed

section \<open>Mark-kids (Section 4.8.1)\<close>

text \<open>Thesis: the specification of Mark-kids(x) (Section 4.8.1, Appendix C):
    pre  x \<in> marked
    rely rely-Collector
    guar marked \<subseteq> marked' \<and> s \<subseteq> s' \<and> (marked' - marked) \<subseteq> kids(x, hp) \<and>
         (\<forall>(x, i) \<in> (s' - s) \<cdot> (x, i) \<notin> dom hp \<or> hp(x, i) \<in> marked')
    post s' = s \<union> {(x, i) | i \<in> Index} \<and> kids(x, hp') \<subseteq> marked' \<union> BadA(s', \<sigma>')
  The guarantee is guar_MarkKids (GC_Collector_Steps), which also records that hp,
  roots and free do not change (ext rd hp); and of the private variables
  only s, checked and i change (owns wr s, checked).  The post condition is
  post_MarkKids (GC_Mark).\<close>

definition MK_pre :: "('a,'i) cconf \<Rightarrow> bool" where
  "MK_pre = (\<lambda>(l,\<sigma>). x l \<in> marked \<sigma>)"

definition MK_guar :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "MK_guar = (\<lambda>(l,\<sigma>) (l',\<sigma>'). guar_MarkKids (x l) (s l) \<sigma> (s l') \<sigma>' \<and>
      consid l' = consid l \<and> mc l' = mc l \<and> x l' = x l \<and> cleared l' = cleared l \<and> Fv l' = Fv l)"

definition MK_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "MK_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). post_MarkKids (x l0) (s l0) (s l) \<sigma>)"

text \<open>Thesis: the post condition of Mark-kids is satisfied despite interference:
  once every edge of x is in s', each child of x is marked or the target of
  a Bad edge (the argument of Theorem 1, which does not depend on the
  state).\<close>

lemma post_MarkKids_any:
  assumes "post_MarkKids y S S' \<sigma>"
  shows "post_MarkKids y S S' \<sigma>'"
proof -
  from assms have "S' = S \<union> {(y,j) | j. True}" unfolding post_MarkKids_def by blast
  then have "so_farMk y {} S UNIV S'" unfolding so_farMk_def by auto
  from theorem1_post_MarkKids[OF this] show ?thesis .
qed

subsection \<open>The Mark-kids loop\<close>

text \<open>Thesis: test, inv and so-far for the loop of Mark-kids (Section 4.8.1,
  "Mark-kids Loop"):
    testM-k  \<triangleq> checked \<noteq> Index                          (MK_test)
    invM-k   \<triangleq> checked \<subseteq> Index                          (MK_inv)
    so-farM-k \<triangleq> checked \<subset> checked' \<and>
                s' = s \<union> {(x, i) | i \<in> checked' - checked}   (MK_sofar)
  Index is the type 'i, so invM-k always holds.  so-farM-k is so_farMk of
  GC_Mark, for the x of this call.\<close>

definition MK_inv :: "('a,'i) cconf \<Rightarrow> bool" where
  "MK_inv = (\<lambda>(l,\<sigma>). checked l \<subseteq> UNIV)"

definition MK_sofar :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "MK_sofar = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). so_farMk (x l0) (checked l0) (s l0) (checked l) (s l) \<and> x l = x l0)"

text \<open>Thesis: "As checked and s are private to the Collector, they cannot be
  modified by the Mutator and so this is a valid post condition":
  so-farM-k is satisfied despite interference.\<close>

lemma MK_sofar_tolerates: "tolerates hC (rely_C s) I MK_sofar"
  by (rule toleratesC) (auto simp: MK_sofar_def split_beta)

text \<open>Thesis: Lemma 5, transitivity (lemma5_so_farMk_trans).\<close>

lemma MK_sofar_trans:
  assumes "MK_sofar k0 k1" and "MK_sofar k1 k2"
  shows "MK_sofar k0 k2"
proof -
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
  obtain l2 \<sigma>2 where k2: "k2 = (l2,\<sigma>2)" by (cases k2)
  from assms k0 k1 have A: "so_farMk (x l0) (checked l0) (s l0) (checked l1) (s l1)" "x l1 = x l0"
    unfolding MK_sofar_def by simp_all
  from assms k1 k2 have B: "so_farMk (x l1) (checked l1) (s l1) (checked l2) (s l2)" "x l2 = x l1"
    unfolding MK_sofar_def by simp_all
  from B(1) A(2) have B1: "so_farMk (x l0) (checked l1) (s l1) (checked l2) (s l2)" by simp
  from lemma5_so_farMk_trans[OF A(1) B1] A(2) B(2) k0 k2 show ?thesis
    unfolding MK_sofar_def by simp
qed

text \<open>Thesis: one iteration of the body of the loop (lines 3-5): pick i, mark
  the target of (x, i) and protect (x, i) in one atomic step, record i as
  checked.  Each atomic statement has its own post condition.\<close>

definition MK_pick_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "MK_pick_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). i l \<notin> checked l0 \<and> checked l = checked l0 \<and> s l = s l0 \<and> x l = x l0)"

definition MK_mark_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "MK_mark_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). s l = s l0 \<union> {(x l0, i l0)} \<and> checked l = checked l0 \<and>
                                       x l = x l0 \<and> i l = i l0)"

definition MK_add_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "MK_add_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). checked l = checked l0 \<union> {i l0} \<and> s l = s l0 \<and> x l = x l0)"

lemma MK_pick_sat: "coll_sat (\<lambda>k. True) MK_pick MK_guar MK_pick_post"
  unfolding MK_pick_def
proof (rule rule_basicC)
  show "stable hC (rely_C s) (\<lambda>k. True)" by (rule stableC) simp
  show "tolerates hC (rely_C s) (\<lambda>k. True) MK_pick_post"
    by (rule toleratesC) (auto simp: MK_pick_post_def split_beta)
qed (auto simp: MK_guar_def MK_pick_post_def guar_MarkKids_def)

text \<open>Thesis: the atomic step of line 4 satisfies guar-Mark-kids: it marks only
  a child of x, and the edge it protects points to a marked node or to
  nothing.\<close>

lemma MK_mark_sat: "coll_sat (\<lambda>k. True) MK_mark MK_guar MK_mark_post"
  unfolding MK_mark_def
proof (rule rule_basicC)
  show "stable hC (rely_C s) (\<lambda>k. True)" by (rule stableC) simp
  show "tolerates hC (rely_C s) (\<lambda>k. True) MK_mark_post"
    by (rule toleratesC) (auto simp: MK_mark_post_def split_beta)
qed (auto simp: MK_guar_def MK_mark_post_def guar_MarkKids_def kids_def domIff)

lemma MK_add_sat: "coll_sat (\<lambda>k. True) MK_add MK_guar MK_add_post"
  unfolding MK_add_def
proof (rule rule_basicC)
  show "stable hC (rely_C s) (\<lambda>k. True)" by (rule stableC) simp
  show "tolerates hC (rely_C s) (\<lambda>k. True) MK_add_post"
    by (rule toleratesC) (auto simp: MK_add_post_def split_beta)
qed (auto simp: MK_guar_def MK_add_post_def guar_MarkKids_def)

text \<open>Thesis: so-farM-k holds after one iteration (despite interference, by the
  tolerance of each statement's post condition).\<close>

lemma MK_body_sat:
  "coll_sat (\<lambda>k. MK_inv k \<and> MK_test k) (MK_body :: ('a,'i) ccom) MK_guar
            (\<lambda>k0 k. MK_inv k \<and> MK_sofar k0 k)"
proof -
  have "coll_sat (\<lambda>k. True) (Seq MK_mark MK_add) MK_guar (seq_post MK_mark_post MK_add_post)"
    by (rule rule_seq[OF MK_mark_sat MK_add_sat]) simp
  then have V: "coll_sat (\<lambda>k. True) MK_body MK_guar
                   (seq_post MK_pick_post (seq_post MK_mark_post MK_add_post))"
    unfolding MK_body_def by (rule rule_seq[OF MK_pick_sat]) simp
  have Q: "MK_inv k \<and> MK_sofar k0 k"
    if "MK_inv k0 \<and> MK_test k0" and "seq_post MK_pick_post (seq_post MK_mark_post MK_add_post) k0 k"
    for k0 k :: "('a,'i) cconf"
  proof -
    from that(2) obtain k1 k2 where 1: "MK_pick_post k0 k1" and 2: "MK_mark_post k1 k2"
      and 3: "MK_add_post k2 k"
      unfolding seq_post_def by blast
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
    obtain l2 \<sigma>2 where k2: "k2 = (l2,\<sigma>2)" by (cases k2)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from 1 k0 k1 have a: "i l1 \<notin> checked l0" "checked l1 = checked l0" "s l1 = s l0" "x l1 = x l0"
      unfolding MK_pick_post_def by simp_all
    from 2 k1 k2 have b: "s l2 = s l1 \<union> {(x l1, i l1)}" "checked l2 = checked l1" "x l2 = x l1" "i l2 = i l1"
      unfolding MK_mark_post_def by simp_all
    from 3 k2 k have c: "checked l = checked l2 \<union> {i l2}" "s l = s l2" "x l = x l2"
      unfolding MK_add_post_def by simp_all
    have ch: "checked l = checked l0 \<union> {i l1}" using a b c by simp
    have "checked l0 \<subset> checked l" using ch a(1) by auto
    moreover have "checked l - checked l0 = {i l1}" using ch a(1) by auto
    moreover have "s l = s l0 \<union> {(x l0, i l1)}" using a b c by simp
    ultimately have "so_farMk (x l0) (checked l0) (s l0) (checked l) (s l)"
      unfolding so_farMk_def by auto
    moreover have "x l = x l0" using a b c by simp
    ultimately show ?thesis using k0 k unfolding MK_inv_def MK_sofar_def by simp
  qed
  show ?thesis by (rule rule_conseq[OF V _ _ _ Q]) simp_all
qed

text \<open>Thesis: the loop of Mark-kids, by the while rule with Lemma 5 and
  Theorem 1: when the loop exits, checked' = Index, and with checked = {} at
  the start, so-farM-k gives post-Mark-kids.  (The body runs at least once,
  since Index is not empty.)\<close>

definition MK_P0 :: "('a,'i) cconf \<Rightarrow> bool" where
  "MK_P0 = (\<lambda>(l,\<sigma>). checked l = {})"

lemma MK_loop_sat: "coll_sat MK_P0 (While MK_test MK_body) MK_guar MK_post"
proof (rule rule_while[where I = MK_inv and sofar = MK_sofar,
                       OF _ MK_body_sat _ _ MK_sofar_trans MK_sofar_tolerates])
  fix k assume "MK_P0 k"
  then show "MK_inv k" by (simp add: MK_inv_def split_beta)
next
  show "stable hC (rely_C s) MK_inv" by (rule stableC) (simp add: MK_inv_def)
next
  fix k show "MK_test (hupd hC k) = MK_test k" by (cases k) (simp add: MK_test_def)
next
  fix k0 k assume P0: "MK_P0 k0" and T: "\<not> MK_test k"
    and W: "MK_sofar k0 k \<or> envC\<^sup>*\<^sup>* k0 k"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  from P0 k0 have c0: "checked l0 = {}" by (simp add: MK_P0_def)
  from T k have c: "checked l = UNIV" by (simp add: MK_test_def)
  from W show "MK_post k0 k"
  proof
    assume "MK_sofar k0 k"
    then have "so_farMk (x l0) {} (s l0) UNIV (s l)" using k0 k c0 c by (simp add: MK_sofar_def)
    from theorem1_post_MarkKids[OF this] show ?thesis using k0 k by (simp add: MK_post_def)
  next
    assume "envC\<^sup>*\<^sup>* k0 k"
    then have "envC\<^sup>*\<^sup>* (l0,\<sigma>0) (l,\<sigma>)" using k0 k by simp
    from envC_star_sel(2)[OF this] c0 c show ?thesis by simp
  qed
next
  fix k0 k k' assume Q: "MK_post k0 k" and E: "envC k k'"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
  from E k k' have l': "l' = hC l \<sigma>'" by (simp add: rely_C_def)
  from Q k0 k have "post_MarkKids (x l0) (s l0) (s l) \<sigma>" by (simp add: MK_post_def)
  then have "post_MarkKids (x l0) (s l0) (s l) \<sigma>'" by (rule post_MarkKids_any)
  then show "MK_post k0 k'" using k0 k' l' by (simp add: MK_post_def)
qed

text \<open>Thesis: line 1, checked \<leftarrow> {}.\<close>

definition MK_init_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "MK_init_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). checked l = {} \<and> s l = s l0 \<and> x l = x l0)"

lemma MK_init_sat: "coll_sat MK_pre MK_init MK_guar MK_init_post"
  unfolding MK_init_def
proof (rule rule_basicC)
  show "stable hC (rely_C s) MK_pre"
    by (rule stableC) (auto simp: MK_pre_def dest: env_marked)
  show "tolerates hC (rely_C s) MK_pre MK_init_post"
    by (rule toleratesC) (auto simp: MK_init_post_def split_beta)
qed (auto simp: MK_guar_def MK_init_post_def guar_MarkKids_def)

text \<open>Thesis: "by Lemma 5 and Theorem 1, Mark-kids terminates and satisfies its
  post condition": Mark-kids meets its specification.\<close>

theorem MarkKids_sat: "coll_sat MK_pre MarkKids MK_guar MK_post"
proof -
  have "coll_sat MK_pre MarkKids MK_guar (seq_post MK_init_post MK_post)"
    unfolding MarkKids_def
    by (rule rule_seq[OF MK_init_sat MK_loop_sat]) (auto simp: MK_init_post_def MK_P0_def split_beta)
  then show ?thesis
    by (rule rule_conseq) (auto simp: seq_post_def MK_init_post_def MK_post_def split_beta)
qed

section \<open>Propagate (Section 4.8.1)\<close>

text \<open>Thesis: the specification of Propagate (Section 4.8.1, Appendix C):
    pre  true
    rely rely-Collector
    guar marked \<subseteq> marked' \<and> s \<subseteq> s'
    post (\<forall>x \<in> marked \<cdot> kids(x, hp') \<subseteq> marked' \<union> BadA(s', \<sigma>')) \<and>
         (marked' = marked \<Rightarrow> reach(roots, hp') \<subseteq> marked')
  In Isabelle:
    - the pre condition states the invariants inv-\<Sigma> and invB, which the
      thesis has in every state (Sections 4.4.2 and 4.7) and which Theorem 2
      uses;
    - the guarantee says, step by step, that every step is a step of
      Mark-kids(x) for a marked x (line 5) or changes only private variables;
      it implies the thesis's guarantee (P_guar_thesis), and Lemma 9 uses
      exactly this;
    - the post condition is post-Propagate (GC_Mark) with two facts that the
      thesis has at this point (so-farP with consid = {} and consid' = Addr):
      every node marked at the start has all its edges in s', and
      marked \<subseteq> marked'.  With them the post condition is satisfied despite
      interference after Propagate ends.\<close>

definition P_pre :: "('a,'i) cconf \<Rightarrow> bool" where
  "P_pre = (\<lambda>(l,\<sigma>). inv_state \<sigma> \<and> invB (s l) \<sigma>)"

definition P_guar :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "P_guar = (\<lambda>(l,\<sigma>) (l',\<sigma>'). (stutter (s l) \<sigma> (s l') \<sigma>' \<or> (\<exists>y\<in>marked \<sigma>. guar_MarkKids y (s l) \<sigma> (s l') \<sigma>')) \<and>
      mc l' = mc l \<and> cleared l' = cleared l \<and> Fv l' = Fv l)"

definition P_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "P_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). post_Propagate (s l0) \<sigma>0 (s l) \<sigma> \<and>
                 (\<forall>y\<in>marked \<sigma>0. \<forall>j. (y,j) \<in> s l) \<and> marked \<sigma>0 \<subseteq> marked \<sigma>)"

text \<open>Thesis: the guarantee of Propagate: marked \<subseteq> marked' \<and> s \<subseteq> s'.\<close>

lemma P_guar_thesis:
  assumes "P_guar (l,\<sigma>) (l',\<sigma>')"
  shows "marked \<sigma> \<subseteq> marked \<sigma>' \<and> s l \<subseteq> s l'"
  using assms unfolding P_guar_def stutter_def guar_MarkKids_def by auto

text \<open>Mechanisation only: a step of Propagate is a step of Mark (guar_Mark,
  GC_Collector_Steps); such steps keep inv-\<Sigma> and, by Lemma 4, invB.\<close>

lemma P_guar_Mark: "P_guar (l,\<sigma>) (l',\<sigma>') \<Longrightarrow> guar_Mark (s l) \<sigma> (s l') \<sigma>'"
  unfolding P_guar_def guar_Mark_def by auto

lemma guar_Mark_frame:
  assumes "guar_Mark S \<sigma> S' \<sigma>'"
  shows "hp \<sigma>' = hp \<sigma> \<and> roots \<sigma>' = roots \<sigma> \<and> free \<sigma>' = free \<sigma> \<and> marked \<sigma> \<subseteq> marked \<sigma>'"
  using assms unfolding guar_Mark_def stutter_def guar_MarkEnd_def guar_MarkKids_def by auto

lemma guar_Mark_inv_state:
  assumes G: "guar_Mark S \<sigma> S' \<sigma>'" and I: "inv_state \<sigma>"
  shows "inv_state \<sigma>'"
proof -
  from guar_Mark_frame[OF G] have h: "hp \<sigma>' = hp \<sigma>" and r: "roots \<sigma>' = roots \<sigma>"
    and f: "free \<sigma>' = free \<sigma>" and m: "marked \<sigma> \<subseteq> marked \<sigma>'" by simp_all
  have "free \<sigma> \<union> roots \<sigma> \<subseteq> marked \<sigma>" using I unfolding inv_state_def by blast
  then have "free \<sigma>' \<union> roots \<sigma>' \<subseteq> marked \<sigma>'" using f r m by blast
  moreover have "card (free \<sigma>' \<inter> reach (roots \<sigma>') (hp \<sigma>')) \<le> 1"
    using I h r f unfolding inv_state_def by simp
  moreover have "\<forall>a\<in>free \<sigma>'. \<forall>i. (a,i) \<notin> dom (hp \<sigma>')"
    using I h f unfolding inv_state_def by simp
  ultimately show ?thesis unfolding inv_state_def by blast
qed

lemma guar_Mark_invB:
  fixes \<sigma> \<sigma>' :: "('a::finite,'i::finite) state"
  assumes "guar_Mark S \<sigma> S' \<sigma>'" and "invB S \<sigma>"
  shows "invB S' \<sigma>'"
proof -
  have "step_Collector S \<sigma> S' \<sigma>'" using assms(1) unfolding step_Collector_def by blast
  from lemma4_prog_invB[OF this assms(2)] show ?thesis .
qed

text \<open>Mechanisation only: if every edge of y is protected, every child of y is
  marked or the target of a Bad edge (the argument of Theorem 1 and
  Lemma 7).\<close>

lemma kids_protected:
  assumes "\<forall>j. (y,j) \<in> S"
  shows "kids y (hp \<sigma>) \<subseteq> marked \<sigma> \<union> BadA S \<sigma>"
proof
  fix b assume "b \<in> kids y (hp \<sigma>)"
  then obtain j where hb: "hp \<sigma> (y,j) = Some b" unfolding kids_def by blast
  show "b \<in> marked \<sigma> \<union> BadA S \<sigma>"
  proof (cases "b \<in> marked \<sigma>")
    case True
    then show ?thesis by simp
  next
    case False
    have "(y,j) \<in> Bad S \<sigma>" using assms hb False unfolding Bad_def by blast
    with hb show ?thesis unfolding BadA_def by blast
  qed
qed

text \<open>Beyond the thesis: the post condition of Propagate is satisfied despite
  interference after Propagate ends.  The first conjunct holds because every
  edge of a node marked at the start is protected; for the second, if marked
  has not grown then all reachable nodes are marked (inv-safe), and then by
  Lemma 15 interference keeps them marked and marks nothing new.\<close>

lemma P_post_right:
  assumes Q: "P_post (l0,\<sigma>0) (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  shows "P_post (l0,\<sigma>0) (hC l \<sigma>', \<sigma>')"
proof -
  from Q have S: "\<forall>y\<in>marked \<sigma>0. \<forall>j. (y,j) \<in> s l" and M: "marked \<sigma>0 \<subseteq> marked \<sigma>"
    and P2: "marked \<sigma> = marked \<sigma>0 \<longrightarrow> reach (roots \<sigma>) (hp \<sigma>) \<subseteq> marked \<sigma>"
    unfolding P_post_def post_Propagate_def by simp_all
  have M': "marked \<sigma>0 \<subseteq> marked \<sigma>'" using M envs_marked[OF E] by blast
  have C1: "\<forall>y\<in>marked \<sigma>0. kids y (hp \<sigma>') \<subseteq> marked \<sigma>' \<union> BadA (s l) \<sigma>'"
  proof
    fix y assume "y \<in> marked \<sigma>0"
    with S have "\<forall>j. (y,j) \<in> s l" by (rule bspec)
    then show "kids y (hp \<sigma>') \<subseteq> marked \<sigma>' \<union> BadA (s l) \<sigma>'" by (rule kids_protected)
  qed
  have C2: "reach (roots \<sigma>') (hp \<sigma>') \<subseteq> marked \<sigma>'" if eq: "marked \<sigma>' = marked \<sigma>0"
  proof -
    have "marked \<sigma> = marked \<sigma>0" using eq M envs_marked[OF E] by blast
    with P2 have "inv_safe \<sigma>" unfolding inv_safe_def by simp
    from envs_inv_safe[OF E this] show ?thesis unfolding inv_safe_def by blast
  qed
  have C2': "marked \<sigma>' = marked \<sigma>0 \<longrightarrow> reach (roots \<sigma>') (hp \<sigma>') \<subseteq> marked \<sigma>'"
    using C2 by blast
  have "post_Propagate (s l0) \<sigma>0 (s l) \<sigma>'" unfolding post_Propagate_def using C1 C2' by blast
  then show ?thesis using S M' by (simp add: P_post_def)
qed

text \<open>Beyond the thesis: and despite interference before Propagate starts (only
  marked can change, and it only grows).\<close>

lemma P_post_left:
  assumes Q: "P_post (l1,\<sigma>1) k" and S: "s l1 = s l0" and M: "marked \<sigma>0 \<subseteq> marked \<sigma>1"
  shows "P_post (l0,\<sigma>0) k"
proof -
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  from Q k have A: "\<forall>y\<in>marked \<sigma>1. kids y (hp \<sigma>) \<subseteq> marked \<sigma> \<union> BadA (s l) \<sigma>"
    and B: "marked \<sigma> = marked \<sigma>1 \<longrightarrow> reach (roots \<sigma>) (hp \<sigma>) \<subseteq> marked \<sigma>"
    and C: "\<forall>y\<in>marked \<sigma>1. \<forall>j. (y,j) \<in> s l" and D: "marked \<sigma>1 \<subseteq> marked \<sigma>"
    unfolding P_post_def post_Propagate_def by simp_all
  have B': "marked \<sigma> = marked \<sigma>0 \<longrightarrow> reach (roots \<sigma>) (hp \<sigma>) \<subseteq> marked \<sigma>"
    using B M D by blast
  show ?thesis using A B' C D M S k unfolding P_post_def post_Propagate_def by auto
qed

subsection \<open>The Propagate loop\<close>

text \<open>Thesis: test, inv and so-far for the loop of Propagate (Section 4.8.1,
  "Propagate Loop"):
    testP  \<triangleq> consid \<noteq> Addr                                (consid_test)
    invP   \<triangleq> consid \<subseteq> Addr                                (P_inv)
    so-farP \<triangleq> consid \<subset> consid' \<and> marked \<subseteq> marked' \<and> s \<subseteq> s' \<and>
             \<forall>x \<in> (marked \<inter> (consid' - consid)) \<cdot> {(x, i) | i \<in> Index} \<subseteq> s'
                                                            (P_sofar)
  Addr is the type 'a, so invP always holds; P_inv states instead the
  invariants inv-\<Sigma> and invB, which hold in every state (Theorem 2 uses
  invB).  so-farP is so_farP of GC_Mark.\<close>

definition P_inv :: "('a,'i) cconf \<Rightarrow> bool" where
  "P_inv = (\<lambda>(l,\<sigma>). inv_state \<sigma> \<and> invB (s l) \<sigma>)"

definition P_sofar :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "P_sofar = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). so_farP (consid l0) (s l0) \<sigma>0 (consid l) (s l) \<sigma>)"

definition P_P0 :: "('a,'i) cconf \<Rightarrow> bool" where
  "P_P0 = (\<lambda>(l,\<sigma>). consid l = {} \<and> inv_state \<sigma> \<and> invB (s l) \<sigma>)"

text \<open>Thesis: the invariants hold despite interference (Lemma 2 for invB).\<close>

lemma P_inv_stable: "stable hC (rely_C s) (P_inv :: ('a::finite,'i::finite) cconf \<Rightarrow> bool)"
proof (rule stableC)
  fix l and \<sigma> \<sigma>' :: "('a,'i) state"
  assume I: "P_inv (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  from I have inv: "inv_state \<sigma>" and IB: "invB (s l) \<sigma>" unfolding P_inv_def by simp_all
  have "inv_state \<sigma>'" by (rule envs_inv_state[OF E inv])
  moreover have "invB (s l) \<sigma>'" by (rule envs_invB[OF E IB])
  ultimately show "P_inv (hC l \<sigma>', \<sigma>')" unfolding P_inv_def by simp
qed

text \<open>Thesis: "Since consid and s are private to the Collector, they cannot be
  modified by the environment and the rely condition ensures that
  marked \<subseteq> marked'": so-farP is satisfied despite interference.\<close>

lemma P_sofar_tolerates: "tolerates hC (rely_C s) I P_sofar"
proof (rule toleratesC)
  fix k0 l \<sigma> \<sigma>' assume Q: "P_sofar k0 (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  show "P_sofar k0 (hC l \<sigma>', \<sigma>')"
    using Q envs_marked[OF E] by (cases k0) (auto simp: P_sofar_def so_farP_def)
next
  fix l0 \<sigma>0 \<sigma>0' k assume E: "env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0" and Q: "P_sofar (hC l0 \<sigma>0', \<sigma>0') k"
  show "P_sofar (l0,\<sigma>0) k"
    using Q envs_marked[OF E] by (cases k) (auto simp: P_sofar_def so_farP_def)
qed

text \<open>Thesis: Lemma 6, transitivity (lemma6_so_farP_trans).\<close>

lemma P_sofar_trans:
  assumes "P_sofar k0 k1" and "P_sofar k1 k2"
  shows "P_sofar k0 k2"
proof -
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
  obtain l2 \<sigma>2 where k2: "k2 = (l2,\<sigma>2)" by (cases k2)
  from assms k0 k1 have A: "so_farP (consid l0) (s l0) \<sigma>0 (consid l1) (s l1) \<sigma>1"
    unfolding P_sofar_def by simp
  from assms k1 k2 have B: "so_farP (consid l1) (s l1) \<sigma>1 (consid l2) (s l2) \<sigma>2"
    unfolding P_sofar_def by simp
  from lemma6_so_farP_trans[OF A B] k0 k2 show ?thesis unfolding P_sofar_def by simp
qed

text \<open>Thesis: one iteration of the body (lines 3-6): pick x; if x is marked,
  Mark-kids(x); add x to consid.\<close>

definition P_pick_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "P_pick_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). x l \<notin> consid l0 \<and> consid l = consid l0 \<and> s l = s l0 \<and>
                                     marked \<sigma>0 \<subseteq> marked \<sigma>)"

definition P_if_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "P_if_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). x l = x l0 \<and> consid l = consid l0 \<and> s l0 \<subseteq> s l \<and>
                   marked \<sigma>0 \<subseteq> marked \<sigma> \<and> (x l0 \<in> marked \<sigma>0 \<longrightarrow> (\<forall>j. (x l0, j) \<in> s l)))"

definition P_add_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "P_add_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). consid l = consid l0 \<union> {x l0} \<and> s l = s l0 \<and> x l = x l0 \<and>
                                    marked \<sigma>0 \<subseteq> marked \<sigma>)"

lemma P_pick_sat: "coll_sat (\<lambda>k. True) pick_x P_guar P_pick_post"
  unfolding pick_x_def
proof (rule rule_basicC)
  show "stable hC (rely_C s) (\<lambda>k. True)" by (rule stableC) simp
  show "tolerates hC (rely_C s) (\<lambda>k. True) P_pick_post"
  proof (rule toleratesC)
    fix k0 l \<sigma> \<sigma>' assume "P_pick_post k0 (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    then show "P_pick_post k0 (hC l \<sigma>', \<sigma>')"
      using envs_marked[OF E] by (cases k0) (auto simp: P_pick_post_def)
  next
    fix l0 \<sigma>0 \<sigma>0' k assume E: "env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0" and "P_pick_post (hC l0 \<sigma>0', \<sigma>0') k"
    then show "P_pick_post (l0,\<sigma>0) k"
      using envs_marked[OF E] by (cases k) (auto simp: P_pick_post_def)
  qed
qed (auto simp: P_guar_def P_pick_post_def stutter_def)

lemma P_add_sat: "coll_sat (\<lambda>k. True) consid_add P_guar P_add_post"
  unfolding consid_add_def
proof (rule rule_basicC)
  show "stable hC (rely_C s) (\<lambda>k. True)" by (rule stableC) simp
  show "tolerates hC (rely_C s) (\<lambda>k. True) P_add_post"
  proof (rule toleratesC)
    fix k0 l \<sigma> \<sigma>' assume "P_add_post k0 (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    then show "P_add_post k0 (hC l \<sigma>', \<sigma>')"
      using envs_marked[OF E] by (cases k0) (auto simp: P_add_post_def)
  next
    fix l0 \<sigma>0 \<sigma>0' k assume E: "env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0" and "P_add_post (hC l0 \<sigma>0', \<sigma>0') k"
    then show "P_add_post (l0,\<sigma>0) k"
      using envs_marked[OF E] by (cases k) (auto simp: P_add_post_def)
  qed
qed (auto simp: P_guar_def P_add_post_def stutter_def)

text \<open>Thesis: line 5, "if x \<in> marked then Mark-kids(x)": Mark-kids meets its
  specification (MarkKids_sat), its pre condition x \<in> marked holds
  throughout, so each of its steps is a step of Mark-kids(x) for a marked x;
  "we have already shown [Mark-kids] will terminate, and its post condition
  will be satisfied despite interference.  Therefore, at the end of the
  iteration we will have {(x, i) | i \<in> Index} added to s'".\<close>

lemma P_if_sat:
  "coll_sat (\<lambda>k. True) (IfThen (\<lambda>(l,\<sigma>). x l \<in> marked \<sigma>) (MarkKids :: ('a,'i) ccom)) P_guar P_if_post"
proof (rule rule_if)
  have MK_pre_stable: "stable hC (rely_C s) (MK_pre :: ('a,'i) cconf \<Rightarrow> bool)"
    by (rule stableC) (auto simp: MK_pre_def dest: env_marked)
  have V1: "coll_sat MK_pre (MarkKids :: ('a,'i) ccom) (\<lambda>k k'. MK_guar k k' \<and> MK_pre k) (\<lambda>k0 k. MK_post k0 k \<and> MK_pre k)"
  proof (rule rule_inv[OF MarkKids_sat _ MK_pre_stable])
    fix k assume "MK_pre k"
    then show "MK_pre k" .
  next
    fix k k' assume "MK_pre k" and "MK_guar k k'"
    then show "MK_pre k'"
      by (cases k, cases k') (auto simp: MK_pre_def MK_guar_def guar_MarkKids_def)
  qed
  define T :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
    "T = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). x l = x l0 \<and> consid l = consid l0 \<and> s l0 \<subseteq> s l \<and> marked \<sigma>0 \<subseteq> marked \<sigma>)"
  have V2: "coll_sat MK_pre (MarkKids :: ('a,'i) ccom) (\<lambda>k k'. MK_guar k k' \<and> MK_pre k)
                (\<lambda>k0 k. (MK_post k0 k \<and> MK_pre k) \<and> T k0 k)"
  proof (rule rule_trace[OF V1])
    fix k show "T k k" by (cases k) (simp add: T_def)
  next
    fix k0 k k' assume T: "T k0 k" and E: "envC k k'"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from E k k' have l': "l' = hC l \<sigma>'" and E': "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
      by (simp_all add: rely_C_def)
    from T k0 k have "x l = x l0 \<and> consid l = consid l0 \<and> s l0 \<subseteq> s l \<and> marked \<sigma>0 \<subseteq> marked \<sigma>"
      by (simp add: T_def)
    with envs_marked[OF E'] l' k0 k' show "T k0 k'" by (auto simp: T_def)
  next
    fix k0 k k' assume "T k0 k" and "MK_guar k k' \<and> MK_pre k"
    then show "T k0 k'"
      by (cases k0, cases k, cases k') (auto simp: T_def MK_guar_def guar_MarkKids_def)
  qed
  show "coll_sat (\<lambda>k. True \<and> (\<lambda>(l,\<sigma>). x l \<in> marked \<sigma>) k) (MarkKids :: ('a,'i) ccom) P_guar P_if_post"
  proof (rule rule_weaken[OF V2])
    fix k :: "('a,'i) cconf" assume "True \<and> (\<lambda>(l,\<sigma>). x l \<in> marked \<sigma>) k"
    then show "MK_pre k" by (cases k) (simp add: MK_pre_def)
  next
    fix k k' assume "MK_guar k k' \<and> MK_pre k"
    then show "P_guar k k'"
      by (cases k, cases k') (auto simp: MK_guar_def MK_pre_def P_guar_def)
  next
    fix k0 k assume "(MK_post k0 k \<and> MK_pre k) \<and> T k0 k"
    then show "P_if_post k0 k"
      by (cases k0, cases k) (auto simp: MK_post_def T_def P_if_post_def post_MarkKids_def)
  qed
next
  fix k0 k assume P: "True \<and> \<not> (\<lambda>(l,\<sigma>). x l \<in> marked \<sigma>) k0" and RS: "envC\<^sup>*\<^sup>* k0 k"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  from RS k0 k have RS': "envC\<^sup>*\<^sup>* (l0,\<sigma>0) (l,\<sigma>)" by simp
  have "marked \<sigma>0 \<subseteq> marked \<sigma>" using envC_star_state(1)[OF RS'] by simp
  with envC_star_sel[OF RS'] P k0 k show "P_if_post k0 k" by (auto simp: P_if_post_def)
next
  show "stable hC (rely_C s) (\<lambda>k. True)" by (rule stableC) simp
next
  fix k show "(\<lambda>(l,\<sigma>). x l \<in> marked \<sigma>) (hupd hC k) = (\<lambda>(l,\<sigma>). x l \<in> marked \<sigma>) k"
    by (cases k) simp
next
  fix k0 k0' k assume E: "envC k0 k0'" and Q: "P_if_post k0' k"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l0' \<sigma>0' where k0': "k0' = (l0',\<sigma>0')" by (cases k0')
  from E k0 k0' have l0': "l0' = hC l0 \<sigma>0'" and E': "env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0"
    by (simp_all add: rely_C_def)
  show "P_if_post k0 k"
    using Q envs_marked[OF E'] k0 k0' l0' by (cases k) (auto simp: P_if_post_def)
qed

lemma P_body_sat:
  "coll_sat (\<lambda>k. P_inv k \<and> consid_test k) (P_body :: ('a::finite,'i::finite) ccom) P_guar
            (\<lambda>k0 k. P_inv k \<and> P_sofar k0 k)"
proof -
  have "coll_sat (\<lambda>k. True) (Seq (IfThen (\<lambda>(l,\<sigma>). x l \<in> marked \<sigma>) MarkKids) consid_add :: ('a,'i) ccom) P_guar
          (seq_post P_if_post P_add_post)"
    by (rule rule_seq[OF P_if_sat P_add_sat]) simp
  then have V: "coll_sat (\<lambda>k. True) (P_body :: ('a,'i) ccom) P_guar
                  (seq_post P_pick_post (seq_post P_if_post P_add_post))"
    unfolding P_body_def by (rule rule_seq[OF P_pick_sat]) simp
  have SF: "P_sofar k0 k"
    if "P_inv k0 \<and> consid_test k0" and "seq_post P_pick_post (seq_post P_if_post P_add_post) k0 k"
    for k0 k :: "('a,'i) cconf"
  proof -
    from that(2) obtain k1 k2 where 1: "P_pick_post k0 k1" and 2: "P_if_post k1 k2"
      and 3: "P_add_post k2 k"
      unfolding seq_post_def by blast
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
    obtain l2 \<sigma>2 where k2: "k2 = (l2,\<sigma>2)" by (cases k2)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from 1 k0 k1 have a: "x l1 \<notin> consid l0" "consid l1 = consid l0" "s l1 = s l0" "marked \<sigma>0 \<subseteq> marked \<sigma>1"
      unfolding P_pick_post_def by simp_all
    from 2 k1 k2 have b: "x l2 = x l1" "consid l2 = consid l1" "s l1 \<subseteq> s l2" "marked \<sigma>1 \<subseteq> marked \<sigma>2"
      "x l1 \<in> marked \<sigma>1 \<longrightarrow> (\<forall>j. (x l1, j) \<in> s l2)"
      unfolding P_if_post_def by simp_all
    from 3 k2 k have c: "consid l = consid l2 \<union> {x l2}" "s l = s l2" "marked \<sigma>2 \<subseteq> marked \<sigma>"
      unfolding P_add_post_def by simp_all
    have cc: "consid l = consid l0 \<union> {x l1}" using a b c by simp
    have "consid l0 \<subset> consid l" using cc a(1) by auto
    moreover have "marked \<sigma>0 \<subseteq> marked \<sigma>" using a b c by blast
    moreover have "s l0 \<subseteq> s l" using a b c by simp
    moreover have "\<forall>y \<in> marked \<sigma>0 \<inter> (consid l - consid l0). \<forall>j. (y,j) \<in> s l"
    proof (intro ballI allI)
      fix y j assume "y \<in> marked \<sigma>0 \<inter> (consid l - consid l0)"
      then have y: "y = x l1" and "x l1 \<in> marked \<sigma>1" using cc a by auto
      with b c show "(y,j) \<in> s l" by simp
    qed
    ultimately have "so_farP (consid l0) (s l0) \<sigma>0 (consid l) (s l) \<sigma>" unfolding so_farP_def by blast
    then show ?thesis using k0 k unfolding P_sofar_def by simp
  qed
  have V': "coll_sat (\<lambda>k. P_inv k \<and> consid_test k) (P_body :: ('a,'i) ccom) P_guar P_sofar"
    by (rule rule_weaken[OF V _ _ SF]) simp_all
  have IG: "P_inv k'" if I: "P_inv k" and G: "P_guar k k'" for k k' :: "('a,'i) cconf"
  proof -
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    have GM: "guar_Mark (s l) \<sigma> (s l') \<sigma>'" by (rule P_guar_Mark[OF G[unfolded k k']])
    from I k have inv: "inv_state \<sigma>" and IB: "invB (s l) \<sigma>" by (simp_all add: P_inv_def)
    have "inv_state \<sigma>'" by (rule guar_Mark_inv_state[OF GM inv])
    moreover have "invB (s l') \<sigma>'" by (rule guar_Mark_invB[OF GM IB])
    ultimately show ?thesis using k' by (simp add: P_inv_def)
  qed
  have V'': "coll_sat (\<lambda>k. P_inv k \<and> consid_test k) (P_body :: ('a,'i) ccom)
               (\<lambda>k k'. P_guar k k' \<and> P_inv k) (\<lambda>k0 k. P_sofar k0 k \<and> P_inv k)"
    by (rule rule_inv[OF V' _ P_inv_stable IG]) simp
  show ?thesis by (rule rule_weaken[OF V'']) auto
qed

text \<open>Thesis: the loop of Propagate, by the while rule with Lemma 6 and Theorem
  2: when the loop exits, consid' = Addr, and with consid = {} at the start,
  so-farP gives post-Propagate (Theorem 2, which uses invB in the final
  state).\<close>

lemma P_loop_sat:
  "coll_sat P_P0 (While consid_test (P_body :: ('a::finite,'i::finite) ccom)) P_guar P_post"
proof (rule rule_while[where I = P_inv and sofar = P_sofar,
                       OF _ P_body_sat P_inv_stable _ P_sofar_trans P_sofar_tolerates])
  fix k :: "('a,'i) cconf" assume "P_P0 k"
  then show "P_inv k" by (cases k) (simp add: P_P0_def P_inv_def)
next
  fix k :: "('a,'i) cconf" show "consid_test (hupd hC k) = consid_test k" by (cases k) (simp add: consid_test_def)
next
  fix k0 k :: "('a,'i) cconf" assume P0: "P_P0 k0" and I: "P_inv k" and T: "\<not> consid_test k"
    and W: "P_sofar k0 k \<or> envC\<^sup>*\<^sup>* k0 k"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  from P0 k0 have c0: "consid l0 = {}" by (simp add: P_P0_def)
  from T k have c: "consid l = UNIV" by (simp add: consid_test_def)
  from I k have inv: "inv_state \<sigma>" and IB: "invB (s l) \<sigma>" by (simp_all add: P_inv_def)
  from W show "P_post k0 k"
  proof
    assume "P_sofar k0 k"
    then have SF: "so_farP {} (s l0) \<sigma>0 UNIV (s l) \<sigma>" using k0 k c0 c by (simp add: P_sofar_def)
    have "post_Propagate (s l0) \<sigma>0 (s l) \<sigma>" by (rule theorem2_post_Propagate[OF SF inv IB])
    moreover have "\<forall>y\<in>marked \<sigma>0. \<forall>j. (y,j) \<in> s l" and "marked \<sigma>0 \<subseteq> marked \<sigma>"
      using SF unfolding so_farP_def by auto
    ultimately show ?thesis using k0 k by (simp add: P_post_def)
  next
    assume "envC\<^sup>*\<^sup>* k0 k"
    then have "envC\<^sup>*\<^sup>* (l0,\<sigma>0) (l,\<sigma>)" using k0 k by simp
    from envC_star_sel(1)[OF this] c0 c show ?thesis by simp
  qed
next
  fix k0 k k' :: "('a,'i) cconf" assume Q: "P_post k0 k" and E: "envC k k'"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
  from E k k' have l': "l' = hC l \<sigma>'" and E': "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    by (simp_all add: rely_C_def)
  from P_post_right[OF Q[unfolded k0 k] E'] show "P_post k0 k'" using k0 k' l' by simp
qed

text \<open>Thesis: line 1, consid \<leftarrow> {}.\<close>

definition P_reset_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "P_reset_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). consid l = {} \<and> s l = s l0 \<and> marked \<sigma>0 \<subseteq> marked \<sigma> \<and>
                                      inv_state \<sigma> \<and> invB (s l) \<sigma>)"

lemma P_reset_sat:
  "coll_sat P_pre (consid_reset :: ('a::finite,'i::finite) ccom) P_guar P_reset_post"
  unfolding consid_reset_def
proof (rule rule_basicC)
  show "stable hC (rely_C s) (P_pre :: ('a,'i) cconf \<Rightarrow> bool)"
    using P_inv_stable unfolding P_inv_def P_pre_def .
  show "tolerates hC (rely_C s) P_pre (P_reset_post :: ('a,'i) cconf \<Rightarrow> _)"
  proof (rule toleratesC)
    fix k0 l and \<sigma> \<sigma>' :: "('a,'i) state"
    assume Q: "P_reset_post k0 (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    then show "P_reset_post k0 (hC l \<sigma>', \<sigma>')"
      using envs_marked[OF E] envs_inv_state[OF E] envs_invB[OF E]
      by (cases k0) (auto simp: P_reset_post_def)
  next
    fix l0 \<sigma>0 \<sigma>0' k assume E: "env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0"
      and Q: "P_reset_post (hC l0 \<sigma>0', \<sigma>0') k"
    then show "P_reset_post (l0,\<sigma>0) k"
      using envs_marked[OF E] by (cases k) (auto simp: P_reset_post_def)
  qed
qed (auto simp: P_guar_def P_reset_post_def P_pre_def stutter_def)

text \<open>Thesis: "by Lemma 6 and Theorem 2", Propagate meets its specification.\<close>

theorem Propagate_sat:
  "coll_sat P_pre (Propagate :: ('a::finite,'i::finite) ccom) P_guar P_post"
proof -
  have V: "coll_sat P_pre (Propagate :: ('a,'i) ccom) P_guar (seq_post P_reset_post P_post)"
    unfolding Propagate_def
    by (rule rule_seq[OF P_reset_sat P_loop_sat]) (auto simp: P_reset_post_def P_P0_def split_beta)
  have Q: "P_post k0 k" if "P_pre k0" and "seq_post P_reset_post P_post k0 k" for k0 k :: "('a,'i) cconf"
  proof -
    from that(2) obtain k1 where 1: "P_reset_post k0 k1" and 2: "P_post k1 k"
      unfolding seq_post_def by blast
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
    from 1 k0 k1 have "s l1 = s l0" and "marked \<sigma>0 \<subseteq> marked \<sigma>1" by (simp_all add: P_reset_post_def)
    from P_post_left[OF 2[unfolded k1] this] k0 show ?thesis by simp
  qed
  show ?thesis by (rule rule_weaken[OF V _ _ Q]) simp_all
qed

section \<open>Mark (Section 4.8.1)\<close>

text \<open>Thesis: the specification of Mark (Section 4.8.1, Appendix C):
    pre  true
    rely rely-Collector
    guar marked \<subseteq> marked'
    post reach(roots, hp') \<subseteq> marked' \<and> marked' \<subseteq> reach(marked, hp) \<and> s' = {}
  In Isabelle the pre condition states the invariants inv-\<Sigma> and invB, as for
  Propagate; the guarantee is guar-Mark (GC_Collector_Steps), step by step: a step of
  Mark-kids(x) for a marked x, the final step s \<leftarrow> {}, or a step that changes
  only private variables; and the post condition is post_Mark (GC_Mark).\<close>

definition M_pre :: "('a,'i) cconf \<Rightarrow> bool" where
  "M_pre = (\<lambda>(l,\<sigma>). inv_state \<sigma> \<and> invB (s l) \<sigma>)"

definition M_guar :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "M_guar = (\<lambda>(l,\<sigma>) (l',\<sigma>'). guar_Mark (s l) \<sigma> (s l') \<sigma>' \<and> cleared l' = cleared l \<and> Fv l' = Fv l)"

definition M_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "M_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). post_Mark \<sigma>0 (s l) \<sigma>)"

text \<open>Thesis: the guarantee of Mark: marked \<subseteq> marked'.\<close>

lemma M_guar_thesis: "M_guar (l,\<sigma>) (l',\<sigma>') \<Longrightarrow> marked \<sigma> \<subseteq> marked \<sigma>'"
  unfolding M_guar_def guar_Mark_def stutter_def guar_MarkEnd_def guar_MarkKids_def by auto

text \<open>Mechanisation only: a step of Propagate is a step of Mark.\<close>

lemma P_guar_M_guar: "P_guar k k' \<Longrightarrow> M_guar k k'"
  by (cases k, cases k') (auto simp: P_guar_def M_guar_def guar_Mark_def)

text \<open>Thesis: post-Mark is satisfied despite interference after Mark ends: all
  reachable nodes are marked, so by Lemma 15 they stay marked and nothing new
  is marked; and Lemma 9 for interference before Mark starts.\<close>

lemma post_Mark_right:
  assumes Q: "post_Mark \<sigma>0 S \<sigma>" and E: "env_step S' \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  shows "post_Mark \<sigma>0 S \<sigma>'"
proof -
  from Q have IS: "inv_safe \<sigma>" and M: "marked \<sigma> \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0)" and S: "S = {}"
    unfolding post_Mark_def inv_safe_def by simp_all
  from envs_inv_safe[OF E IS] have IS': "inv_safe \<sigma>'" and EQ: "marked \<sigma>' = marked \<sigma>" by blast+
  have "marked \<sigma>' \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0)" using M EQ by simp
  with IS' S show ?thesis unfolding post_Mark_def inv_safe_def by blast
qed

text \<open>Thesis: Lemma 9 for environment steps.\<close>

lemma envs_reach_marked:
  assumes E: "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  shows "reach (marked \<sigma>') (hp \<sigma>') \<subseteq> reach (marked \<sigma>) (hp \<sigma>)"
proof (cases "\<sigma>' = \<sigma>")
  case True
  then show ?thesis by simp
next
  case False
  with E have ES: "env_step S \<sigma> \<sigma>'" by simp
  then have "inv_state \<sigma>" unfolding env_step_def by blast
  from lemma9_reach_marked_mono[OF this disjI2[OF ES]] show ?thesis .
qed

text \<open>Mechanisation only: the same, for an environment step alone.\<close>

lemmas env_reach_marked = envs_reach_marked[OF disjI1]

subsection \<open>The Mark loop\<close>

text \<open>Thesis: test, inv and so-far for the loop of Mark (Section 4.8.1, "Mark
  Loop"), with Mark written as Algorithm 7 (the body runs at least once):
    testM  \<triangleq> card marked \<noteq> mc                        (M_test)
    invM   \<triangleq> mc \<le> card marked \<and> marked \<subseteq> Addr          (M_inv)
    so-farM \<triangleq> ((card marked < card marked' \<and> mc' < card marked') \<or>
               (reach(roots, hp') \<subseteq> marked' \<and> mc' = card marked')) \<and>
              marked \<subseteq> marked' \<and> reach(marked', hp') \<subseteq> reach(marked, hp)
                                                       (M_sofar)
  M_inv also states the invariants inv-\<Sigma> and invB.  so-farM is so_farM of
  GC_Mark.\<close>

definition M_inv :: "('a,'i) cconf \<Rightarrow> bool" where
  "M_inv = (\<lambda>(l,\<sigma>). mc l \<le> card (marked \<sigma>) \<and> inv_state \<sigma> \<and> invB (s l) \<sigma>)"

definition M_sofar :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "M_sofar = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). so_farM (mc l0) \<sigma>0 (mc l) \<sigma>)"

text \<open>Thesis: "this invariant always holds as marked \<subseteq> marked' during
  Propagate and during any environment steps".\<close>

lemma M_inv_stable: "stable hC (rely_C s) (M_inv :: ('a::finite,'i::finite) cconf \<Rightarrow> bool)"
proof (rule stableC)
  fix l and \<sigma> \<sigma>' :: "('a,'i) state"
  assume I: "M_inv (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  from I have mc: "mc l \<le> card (marked \<sigma>)" and inv: "inv_state \<sigma>" and IB: "invB (s l) \<sigma>"
    unfolding M_inv_def by simp_all
  have "card (marked \<sigma>) \<le> card (marked \<sigma>')"
    by (rule card_mono[OF finite_subset[OF subset_UNIV finite_UNIV] envs_marked[OF E]])
  with mc have "mc l \<le> card (marked \<sigma>')" by simp
  moreover have "inv_state \<sigma>'" by (rule envs_inv_state[OF E inv])
  moreover have "invB (s l) \<sigma>'" by (rule envs_invB[OF E IB])
  ultimately show "M_inv (hC l \<sigma>', \<sigma>')" unfolding M_inv_def by simp
qed

text \<open>Thesis: "Note that mc is private to the Collector so the environment cannot
  change it.  The second conjunct is true as marked does not decrease for any
  step during Mark, and the third conjunct is true by Lemma 9": so-farM is
  satisfied despite interference.  When the first disjunct holds it only
  grows stronger; when the second holds, all reachable nodes are marked, so
  by Lemma 15 interference marks nothing new.\<close>

lemma so_farM_right:
  fixes \<sigma> \<sigma>' :: "('a::finite,'i) state"
  assumes Q: "so_farM m0 \<sigma>0 m \<sigma>" and E: "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  shows "so_farM m0 \<sigma>0 m \<sigma>'"
proof -
  have fin: "finite (marked \<sigma>')" by (rule finite_subset[OF subset_UNIV finite_UNIV])
  have M: "marked \<sigma> \<subseteq> marked \<sigma>'" by (rule envs_marked[OF E])
  have C: "card (marked \<sigma>) \<le> card (marked \<sigma>')" by (rule card_mono[OF fin M])
  from Q have D: "(card (marked \<sigma>0) < card (marked \<sigma>) \<and> m < card (marked \<sigma>)) \<or>
                  (reach (roots \<sigma>) (hp \<sigma>) \<subseteq> marked \<sigma> \<and> m = card (marked \<sigma>))"
    and M0: "marked \<sigma>0 \<subseteq> marked \<sigma>" and R0: "reach (marked \<sigma>) (hp \<sigma>) \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0)"
    unfolding so_farM_def by simp_all
  have D': "(card (marked \<sigma>0) < card (marked \<sigma>') \<and> m < card (marked \<sigma>')) \<or>
            (reach (roots \<sigma>') (hp \<sigma>') \<subseteq> marked \<sigma>' \<and> m = card (marked \<sigma>'))"
    using D
  proof
    assume A: "card (marked \<sigma>0) < card (marked \<sigma>) \<and> m < card (marked \<sigma>)"
    then have a1: "card (marked \<sigma>0) < card (marked \<sigma>)" and a2: "m < card (marked \<sigma>)" by simp_all
    from a1 C have "card (marked \<sigma>0) < card (marked \<sigma>')" by (rule less_le_trans)
    moreover from a2 C have "m < card (marked \<sigma>')" by (rule less_le_trans)
    ultimately show ?thesis by blast
  next
    assume A: "reach (roots \<sigma>) (hp \<sigma>) \<subseteq> marked \<sigma> \<and> m = card (marked \<sigma>)"
    then have "inv_safe \<sigma>" unfolding inv_safe_def by simp
    from envs_inv_safe[OF E this] have IS': "reach (roots \<sigma>') (hp \<sigma>') \<subseteq> marked \<sigma>'"
      and EQ: "marked \<sigma>' = marked \<sigma>" unfolding inv_safe_def by blast+
    from A EQ have "m = card (marked \<sigma>')" by simp
    with IS' show ?thesis by blast
  qed
  have "reach (marked \<sigma>') (hp \<sigma>') \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0)"
    using envs_reach_marked[OF E] R0 by blast
  with D' M0 M show ?thesis unfolding so_farM_def by blast
qed

lemma so_farM_left:
  fixes \<sigma>0 \<sigma>0' :: "('a::finite,'i) state"
  assumes E: "env_step S \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0" and Q: "so_farM m0 \<sigma>0' m \<sigma>"
  shows "so_farM m0 \<sigma>0 m \<sigma>"
proof -
  have fin: "finite (marked \<sigma>0')" by (rule finite_subset[OF subset_UNIV finite_UNIV])
  have M: "marked \<sigma>0 \<subseteq> marked \<sigma>0'" by (rule envs_marked[OF E])
  have C: "card (marked \<sigma>0) \<le> card (marked \<sigma>0')" by (rule card_mono[OF fin M])
  have R: "reach (marked \<sigma>0') (hp \<sigma>0') \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0)" by (rule envs_reach_marked[OF E])
  from Q have D: "(card (marked \<sigma>0') < card (marked \<sigma>) \<and> m < card (marked \<sigma>)) \<or>
                  (reach (roots \<sigma>) (hp \<sigma>) \<subseteq> marked \<sigma> \<and> m = card (marked \<sigma>))"
    and M0: "marked \<sigma>0' \<subseteq> marked \<sigma>" and R0: "reach (marked \<sigma>) (hp \<sigma>) \<subseteq> reach (marked \<sigma>0') (hp \<sigma>0')"
    unfolding so_farM_def by simp_all
  have D': "(card (marked \<sigma>0) < card (marked \<sigma>) \<and> m < card (marked \<sigma>)) \<or>
            (reach (roots \<sigma>) (hp \<sigma>) \<subseteq> marked \<sigma> \<and> m = card (marked \<sigma>))"
    using D
  proof
    assume A: "card (marked \<sigma>0') < card (marked \<sigma>) \<and> m < card (marked \<sigma>)"
    then have a1: "card (marked \<sigma>0') < card (marked \<sigma>)" and a2: "m < card (marked \<sigma>)" by simp_all
    from C a1 have "card (marked \<sigma>0) < card (marked \<sigma>)" by (rule le_less_trans)
    with a2 show ?thesis by blast
  next
    assume "reach (roots \<sigma>) (hp \<sigma>) \<subseteq> marked \<sigma> \<and> m = card (marked \<sigma>)"
    then show ?thesis by blast
  qed
  have "marked \<sigma>0 \<subseteq> marked \<sigma>" using M M0 by blast
  moreover have "reach (marked \<sigma>) (hp \<sigma>) \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0)" using R0 R by blast
  ultimately show ?thesis using D' unfolding so_farM_def by blast
qed

lemma M_sofar_tolerates: "tolerates hC (rely_C s) I (M_sofar :: ('a::finite,'i::finite) cconf \<Rightarrow> _)"
proof (rule toleratesC)
  fix k0 l and \<sigma> \<sigma>' :: "('a,'i) state"
  assume Q: "M_sofar k0 (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  from Q k0 have "so_farM (mc l0) \<sigma>0 (mc l) \<sigma>" by (simp add: M_sofar_def)
  from so_farM_right[OF this E] k0 show "M_sofar k0 (hC l \<sigma>', \<sigma>')" by (simp add: M_sofar_def)
next
  fix l0 and \<sigma>0 \<sigma>0' :: "('a,'i) state" and k
  assume E: "env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0" and Q: "M_sofar (hC l0 \<sigma>0', \<sigma>0') k"
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  from Q k have "so_farM (mc l0) \<sigma>0' (mc l) \<sigma>" by (simp add: M_sofar_def)
  from so_farM_left[OF E this] k show "M_sofar (l0,\<sigma>0) k" by (simp add: M_sofar_def)
qed

text \<open>Thesis: Lemma 10, transitivity (lemma10_so_farM_trans).\<close>

lemma M_sofar_trans:
  assumes "M_sofar k0 k1" and "M_sofar k1 k2"
  shows "M_sofar (k0 :: ('a::finite,'i) cconf) k2"
proof -
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
  obtain l2 \<sigma>2 where k2: "k2 = (l2,\<sigma>2)" by (cases k2)
  from assms k0 k1 have A: "so_farM (mc l0) \<sigma>0 (mc l1) \<sigma>1" by (simp add: M_sofar_def)
  from assms k1 k2 have B: "so_farM (mc l1) \<sigma>1 (mc l2) \<sigma>2" by (simp add: M_sofar_def)
  from lemma10_so_farM_trans[OF A B] k0 k2 show ?thesis by (simp add: M_sofar_def)
qed

text \<open>Thesis: one run of the body, mc \<leftarrow> card marked; Propagate, establishes
  so-farM from before it: "After one iteration of Propagate, either the
  marked set has strictly grown and mc' < card marked' since mc was set to
  the cardinality of marked before Propagate; or the set did not grow and we
  must have reach(roots, hp') \<subseteq> marked' from post-Propagate."  The first
  statement's post condition records that mc is the cardinality of some
  value of marked between the start and the end (marked may grow by
  interference before and after the assignment).\<close>

definition mc_count_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "mc_count_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). (\<exists>Mk. marked \<sigma>0 \<subseteq> Mk \<and> Mk \<subseteq> marked \<sigma> \<and> mc l = card Mk) \<and>
                      s l = s l0 \<and> inv_state \<sigma> \<and> invB (s l) \<sigma> \<and>
                      reach (marked \<sigma>) (hp \<sigma>) \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0))"

lemma mc_count_sat:
  "coll_sat M_pre (mc_count :: ('a::finite,'i::finite) ccom) M_guar mc_count_post"
  unfolding mc_count_def
proof (rule rule_basicC)
  show "stable hC (rely_C s) (M_pre :: ('a,'i) cconf \<Rightarrow> bool)"
    using P_inv_stable unfolding P_inv_def M_pre_def .
  show "tolerates hC (rely_C s) M_pre (mc_count_post :: ('a,'i) cconf \<Rightarrow> _)"
  proof (rule toleratesC)
    fix k0 l and \<sigma> \<sigma>' :: "('a,'i) state"
    assume Q: "mc_count_post k0 (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    from Q k0 obtain Mk where Mk: "marked \<sigma>0 \<subseteq> Mk" "Mk \<subseteq> marked \<sigma>" "mc l = card Mk"
      and S: "s l = s l0" and inv: "inv_state \<sigma>" and IB: "invB (s l) \<sigma>"
      and R: "reach (marked \<sigma>) (hp \<sigma>) \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0)"
      unfolding mc_count_post_def by auto
    have "Mk \<subseteq> marked \<sigma>'" using Mk(2) envs_marked[OF E] by blast
    moreover have "inv_state \<sigma>'" by (rule envs_inv_state[OF E inv])
    moreover have "invB (s l) \<sigma>'" by (rule envs_invB[OF E IB])
    moreover have "reach (marked \<sigma>') (hp \<sigma>') \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0)"
      using envs_reach_marked[OF E] R by blast
    ultimately show "mc_count_post k0 (hC l \<sigma>', \<sigma>')"
      using Mk S k0 unfolding mc_count_post_def by auto
  next
    fix l0 and \<sigma>0 \<sigma>0' :: "('a,'i) state" and k
    assume E: "env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0" and Q: "mc_count_post (hC l0 \<sigma>0', \<sigma>0') k"
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from Q k obtain Mk where Mk: "marked \<sigma>0' \<subseteq> Mk" "Mk \<subseteq> marked \<sigma>" "mc l = card Mk"
      and rest: "s l = s l0" "inv_state \<sigma>" "invB (s l) \<sigma>"
      and R: "reach (marked \<sigma>) (hp \<sigma>) \<subseteq> reach (marked \<sigma>0') (hp \<sigma>0')"
      unfolding mc_count_post_def by auto
    have "marked \<sigma>0 \<subseteq> Mk" using Mk(1) envs_marked[OF E] by blast
    moreover have "reach (marked \<sigma>) (hp \<sigma>) \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0)"
      using envs_reach_marked[OF E] R by blast
    ultimately show "mc_count_post (l0,\<sigma>0) k" using Mk rest k unfolding mc_count_post_def by auto
  qed
next
  fix l and \<sigma> :: "('a,'i) state" and l' \<sigma>'
  assume P: "M_pre (l,\<sigma>)"
    and St: "(\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l\<lparr>mc := card (marked \<sigma>)\<rparr> \<and> \<sigma>' = \<sigma>) (l,\<sigma>) (l',\<sigma>')"
  from St have l': "l' = l\<lparr>mc := card (marked \<sigma>)\<rparr>" and s': "\<sigma>' = \<sigma>" by simp_all
  have G: "M_guar (l,\<sigma>) (l',\<sigma>')" using l' s' unfolding M_guar_def guar_Mark_def stutter_def by simp
  have "mc_count_post (l,\<sigma>) (hC l' \<sigma>', \<sigma>')"
    using P l' s' unfolding mc_count_post_def M_pre_def by (auto intro!: exI[of _ "marked \<sigma>"])
  with G show "M_guar (l,\<sigma>) (l',\<sigma>') \<and> mc_count_post (l,\<sigma>) (hC l' \<sigma>', \<sigma>')" by simp
qed

text \<open>Mechanisation only: during Propagate, mc does not change, inv-\<Sigma> and invB
  hold, and the region reachable from marked nodes does not grow (Lemma 9,
  for program steps and for interference).\<close>

definition M_trace :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "M_trace = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). mc l = mc l0 \<and> inv_state \<sigma> \<and> invB (s l) \<sigma> \<and>
                 reach (marked \<sigma>) (hp \<sigma>) \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0))"

lemma Propagate_M_sat:
  "coll_sat P_pre (Propagate :: ('a::finite,'i::finite) ccom) M_guar (\<lambda>k0 k. P_post k0 k \<and> M_trace k0 k)"
proof -
  have V: "coll_sat P_pre (Propagate :: ('a,'i) ccom) P_guar (\<lambda>k0 k. P_post k0 k \<and> M_trace k0 k)"
  proof (rule rule_trace[OF Propagate_sat])
    fix k :: "('a,'i) cconf" assume "P_pre k"
    then show "M_trace k k" by (cases k) (simp add: P_pre_def M_trace_def)
  next
    fix k0 k k' :: "('a,'i) cconf" assume T: "M_trace k0 k" and E: "envC k k'"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from E k k' have l': "l' = hC l \<sigma>'" and E': "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
      by (simp_all add: rely_C_def)
    from T k0 k have a: "mc l = mc l0" "inv_state \<sigma>" "invB (s l) \<sigma>"
      "reach (marked \<sigma>) (hp \<sigma>) \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0)" by (simp_all add: M_trace_def)
    have "inv_state \<sigma>'" by (rule envs_inv_state[OF E' a(2)])
    moreover have "invB (s l) \<sigma>'" by (rule envs_invB[OF E' a(3)])
    moreover have "reach (marked \<sigma>') (hp \<sigma>') \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0)"
      using envs_reach_marked[OF E'] a(4) by blast
    ultimately show "M_trace k0 k'" using a(1) k0 k' l' by (simp add: M_trace_def)
  next
    fix k0 k k' :: "('a,'i) cconf" assume T: "M_trace k0 k" and G: "P_guar k k'"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from T k0 k have a: "mc l = mc l0" "inv_state \<sigma>" "invB (s l) \<sigma>"
      "reach (marked \<sigma>) (hp \<sigma>) \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0)" by (simp_all add: M_trace_def)
    have GM: "guar_Mark (s l) \<sigma> (s l') \<sigma>'" by (rule P_guar_Mark[OF G[unfolded k k']])
    from G k k' have mc': "mc l' = mc l" by (simp add: P_guar_def)
    have "inv_state \<sigma>'" by (rule guar_Mark_inv_state[OF GM a(2)])
    moreover have "invB (s l') \<sigma>'" by (rule guar_Mark_invB[OF GM a(3)])
    moreover have "reach (marked \<sigma>') (hp \<sigma>') \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0)"
      using lemma9_reach_marked_mono[OF a(2) disjI1[OF GM]] a(4) by blast
    ultimately show "M_trace k0 k'" using a(1) mc' k0 k' by (simp add: M_trace_def)
  qed
  show ?thesis by (rule rule_weaken[OF V]) (simp_all add: P_guar_M_guar)
qed

lemma M_body_sat:
  "coll_sat M_pre (M_body :: ('a::finite,'i::finite) ccom) M_guar (\<lambda>k0 k. M_inv k \<and> M_sofar k0 k)"
proof -
  have V: "coll_sat M_pre (M_body :: ('a,'i) ccom) M_guar
             (seq_post mc_count_post (\<lambda>k0 k. P_post k0 k \<and> M_trace k0 k))"
    unfolding M_body_def
    by (rule rule_seq[OF mc_count_sat Propagate_M_sat]) (auto simp: mc_count_post_def P_pre_def split_beta)
  have Q: "M_inv k \<and> M_sofar k0 k"
    if "M_pre k0" and "seq_post mc_count_post (\<lambda>k0 k. P_post k0 k \<and> M_trace k0 k) k0 k"
    for k0 k :: "('a,'i) cconf"
  proof -
    from that(2) obtain k1 where 1: "mc_count_post k0 k1" and 2: "P_post k1 k" and 3: "M_trace k1 k"
      unfolding seq_post_def by blast
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from 1 k0 k1 obtain Mk where Mk: "marked \<sigma>0 \<subseteq> Mk" "Mk \<subseteq> marked \<sigma>1" "mc l1 = card Mk"
      and R1: "reach (marked \<sigma>1) (hp \<sigma>1) \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0)"
      unfolding mc_count_post_def by auto
    from 2 k1 k have M1: "marked \<sigma>1 \<subseteq> marked \<sigma>"
      and P2: "marked \<sigma> = marked \<sigma>1 \<longrightarrow> reach (roots \<sigma>) (hp \<sigma>) \<subseteq> marked \<sigma>"
      unfolding P_post_def post_Propagate_def by simp_all
    from 3 k1 k have mc: "mc l = mc l1" and inv: "inv_state \<sigma>" and IB: "invB (s l) \<sigma>"
      and R2: "reach (marked \<sigma>) (hp \<sigma>) \<subseteq> reach (marked \<sigma>1) (hp \<sigma>1)"
      unfolding M_trace_def by simp_all
    have fin: "finite (marked \<sigma>)" "finite (marked \<sigma>1)"
      by (rule finite_subset[OF subset_UNIV finite_UNIV])+
    have c1: "card Mk \<le> card (marked \<sigma>1)" by (rule card_mono[OF fin(2) Mk(2)])
    have c2: "card (marked \<sigma>1) \<le> card (marked \<sigma>)" by (rule card_mono[OF fin(1) M1])
    have c0: "card (marked \<sigma>0) \<le> card Mk"
      by (rule card_mono[OF finite_subset[OF Mk(2) fin(2)] Mk(1)])
    have D: "(card (marked \<sigma>0) < card (marked \<sigma>) \<and> mc l < card (marked \<sigma>)) \<or>
             (reach (roots \<sigma>) (hp \<sigma>) \<subseteq> marked \<sigma> \<and> mc l = card (marked \<sigma>))"
    proof (cases "Mk = marked \<sigma>")
      case True
      then have "marked \<sigma> = marked \<sigma>1" using Mk(2) M1 by blast
      with P2 True mc Mk(3) show ?thesis by simp
    next
      case False
      then have "Mk \<subset> marked \<sigma>" using Mk(2) M1 by blast
      then have lt: "card Mk < card (marked \<sigma>)" by (rule psubset_card_mono[OF fin(1)])
      have "card (marked \<sigma>0) < card (marked \<sigma>)" using c0 lt by linarith
      moreover have "mc l < card (marked \<sigma>)" using lt mc Mk(3) by simp
      ultimately show ?thesis by blast
    qed
    have "marked \<sigma>0 \<subseteq> marked \<sigma>" using Mk M1 by blast
    moreover have "reach (marked \<sigma>) (hp \<sigma>) \<subseteq> reach (marked \<sigma>0) (hp \<sigma>0)" using R1 R2 by blast
    ultimately have "so_farM (mc l0) \<sigma>0 (mc l) \<sigma>" using D unfolding so_farM_def by blast
    moreover have "mc l \<le> card (marked \<sigma>)" using D by auto
    ultimately show ?thesis using inv IB k0 k unfolding M_inv_def M_sofar_def by simp
  qed
  show ?thesis by (rule rule_weaken[OF V _ _ Q]) simp_all
qed

text \<open>Thesis: the loop's post condition inv \<and> \<not>test \<and> so-far ("we know that the
  post condition of this loop will be {inv \<and> \<not>test \<and> so-far}"), as a
  relation from the start of Mark.  It is satisfied despite interference
  after the loop: as card marked = mc, the second disjunct of so-farM holds,
  so all reachable nodes are marked and interference marks nothing new.\<close>

definition M_loop_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "M_loop_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). card (marked \<sigma>) = mc l \<and> so_farM (mc l0) \<sigma>0 (mc l) \<sigma>)"

lemma M_loop_post_right:
  fixes \<sigma> \<sigma>' :: "('a::finite,'i) state"
  assumes Q: "M_loop_post (l0,\<sigma>0) (l,\<sigma>)" and E: "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  shows "M_loop_post (l0,\<sigma>0) (hC l \<sigma>', \<sigma>')"
proof -
  from Q have c: "card (marked \<sigma>) = mc l" and SF: "so_farM (mc l0) \<sigma>0 (mc l) \<sigma>"
    unfolding M_loop_post_def by simp_all
  have "inv_safe \<sigma>" using lemma11_post_Mark1[OF c SF] unfolding inv_safe_def .
  from envs_inv_safe[OF E this] have "marked \<sigma>' = marked \<sigma>" by blast
  with c so_farM_right[OF SF E] show ?thesis unfolding M_loop_post_def by simp
qed

text \<open>Thesis: Theorem 3 (Mark post condition): card marked' = mc' \<and>
  so-farM(\<sigma>, \<sigma>') \<and> endM(\<sigma>', \<sigma>'') \<Rightarrow> post-Mark(\<sigma>, \<sigma>''), where endM is the
  final step s \<leftarrow> {}.  So Mark meets its specification, by the while rule
  for a body that runs at least once (rule_repeat) with Lemma 10 and
  Lemmas 11 and 12 (inside Theorem 3).\<close>

theorem Mark_sat: "coll_sat M_pre (Mark :: ('a::finite,'i::finite) ccom) M_guar M_post"
proof -
  have loop: "coll_sat M_pre (Seq M_body (While M_test M_body) :: ('a,'i) ccom) M_guar M_loop_post"
  proof (rule rule_repeat[where I = M_inv and sofar = M_sofar, OF M_body_sat _ M_inv_stable _
                          M_sofar_trans M_sofar_tolerates])
    fix k :: "('a,'i) cconf" assume "M_inv k" and "M_test k"
    then show "M_pre k" by (cases k) (simp add: M_inv_def M_pre_def)
  next
    fix k :: "('a,'i) cconf" show "M_test (hupd hC k) = M_test k" by (cases k) (simp add: M_test_def)
  next
    fix k0 k :: "('a,'i) cconf" assume "M_inv k" and T: "\<not> M_test k" and SF: "M_sofar k0 k"
    then show "M_loop_post k0 k" by (cases k0, cases k) (simp add: M_test_def M_sofar_def M_loop_post_def)
  next
    fix k0 k k' :: "('a,'i) cconf" assume Q: "M_loop_post k0 k" and E: "envC k k'"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from E k k' have l': "l' = hC l \<sigma>'" and E': "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
      by (simp_all add: rely_C_def)
    from M_loop_post_right[OF Q[unfolded k0 k] E'] k0 k' l' show "M_loop_post k0 k'" by simp
  qed
  show ?thesis
    unfolding Mark_def s_reset_def
  proof (rule rule_seq_basic[OF loop])
    fix k0 k k' :: "('a,'i) cconf" assume Q: "M_loop_post k0 k" and E: "envC k k'"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from E k k' have l': "l' = hC l \<sigma>'" and E': "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
      by (simp_all add: rely_C_def)
    from M_loop_post_right[OF Q[unfolded k0 k] E'] k0 k' l' show "M_loop_post k0 k'" by simp
  next
    fix k0 k k' :: "('a,'i) cconf" assume Q: "M_loop_post k0 k"
      and St: "(\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l\<lparr>s := {}\<rparr> \<and> \<sigma>' = \<sigma>) k k'"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from St k k' have l': "l' = l\<lparr>s := {}\<rparr>" and s': "\<sigma>' = \<sigma>" by simp_all
    from Q k0 k have c: "card (marked \<sigma>) = mc l" and SF: "so_farM (mc l0) \<sigma>0 (mc l) \<sigma>"
      by (simp_all add: M_loop_post_def)
    have endM: "endM \<sigma> {} \<sigma>'" using s' unfolding endM_def by simp
    have "post_Mark \<sigma>0 {} \<sigma>'" by (rule theorem3_post_Mark[OF c SF endM])
    then have Post: "M_post k0 (hupd hC k')" using k0 k' l' by (simp add: M_post_def)
    have "M_guar k k'" using k k' l' s' unfolding M_guar_def guar_Mark_def guar_MarkEnd_def by simp
    with Post show "M_guar k k' \<and> M_post k0 (hupd hC k')" by simp
  next
    fix k0 k k' :: "('a,'i) cconf" assume Q: "M_post k0 k" and E: "envC k k'"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from E k k' have l': "l' = hC l \<sigma>'" and E': "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
      by (simp_all add: rely_C_def)
    from Q k0 k have "post_Mark \<sigma>0 (s l) \<sigma>" by (simp add: M_post_def)
    from post_Mark_right[OF this E'] k0 k' l' show "M_post k0 k'" by (simp add: M_post_def)
  qed
qed

end
