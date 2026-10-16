(*  GC_Unmark_Sat: Unmark meets its specification (Section 4.8.2).

    Unmark's specification (Appendix C); the test, inv and so-far of its
    loop; that they hold despite interference; the statements of the loop
    body one by one; and Unmark meeting its specification, with Lemma 13 and
    Theorem 4 of GC_Unmark.

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
      Unmark meets its specification                Unmark_sat            *)

theory GC_Unmark_Sat
  imports GC_Unmark GC_Mark_Sat
begin

section \<open>Unmark (Section 4.8.2)\<close>

text \<open>Thesis: the specification of Unmark (Section 4.8.2, Appendix C):
    pre  true
    rely rely-Collector
    guar marked' \<subseteq> marked
    post garbage \<inter> marked' = {}
  In Isabelle:
    - the guarantee U_guar says, step by step, what the ext clause and the
      code give: hp, roots and free are only read, marked only shrinks, and a
      node is unmarked only if it is not in roots \<union> free (line 4); of the
      private variables only consid and x change;
    - the pre condition states inv-\<Sigma> and s = {} (s = {} throughout Unmark,
      Section 4.7.2); with them every step of Unmark is a step of guar-Unmark
      (U_guar_Unmark) and keeps inv-\<Sigma> (U_guar_pre);
    - the post condition is post-Unmark (GC_Unmark), together with two facts
      that Section 4.8.5 uses for Lemma 20: garbage does not decrease during
      Unmark (so-farU), and no pointer out of the old free or reachable
      region points into the old garbage (Sublemma 1; no_new_ptr in
      GC_Safety).\<close>

definition U_pre :: "('a,'i) cconf \<Rightarrow> bool" where
  "U_pre = (\<lambda>(l,\<sigma>). inv_state \<sigma> \<and> s l = {})"

definition U_guar :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "U_guar = (\<lambda>(l,\<sigma>) (l',\<sigma>'). hp \<sigma>' = hp \<sigma> \<and> roots \<sigma>' = roots \<sigma> \<and> free \<sigma>' = free \<sigma> \<and>
      marked \<sigma>' \<subseteq> marked \<sigma> \<and> (marked \<sigma> - marked \<sigma>') \<inter> (roots \<sigma> \<union> free \<sigma>) = {} \<and>
      s l' = s l \<and> checked l' = checked l \<and> mc l' = mc l \<and> cleared l' = cleared l \<and> Fv l' = Fv l)"

definition U_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "U_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). post_Unmark \<sigma>0 \<sigma> \<and> garbage \<sigma>0 \<subseteq> garbage \<sigma> \<and> no_new_ptr \<sigma>0 \<sigma>)"

text \<open>Thesis: the guarantee of Unmark, marked' \<subseteq> marked.\<close>

lemma U_guar_thesis: "U_guar (l,\<sigma>) (l',\<sigma>') \<Longrightarrow> marked \<sigma>' \<subseteq> marked \<sigma>"
  unfolding U_guar_def by simp

text \<open>Mechanisation only: with s = {}, a step of Unmark is a step of guar-Unmark
  (GC_Collector_Steps), and it keeps inv-\<Sigma> and s = {}: roots and free stay marked.\<close>

lemma U_guar_Unmark:
  assumes "U_guar (l,\<sigma>) (l',\<sigma>')" and "s l = {}"
  shows "guar_Unmark (s l) \<sigma> (s l') \<sigma>'"
  using assms unfolding U_guar_def guar_Unmark_def by simp

lemma U_guar_pre:
  assumes G: "U_guar (l,\<sigma>) (l',\<sigma>')" and I: "U_pre (l,\<sigma>)"
  shows "U_pre (l',\<sigma>')"
proof -
  from G have h: "hp \<sigma>' = hp \<sigma>" and r: "roots \<sigma>' = roots \<sigma>" and f: "free \<sigma>' = free \<sigma>"
    and m: "(marked \<sigma> - marked \<sigma>') \<inter> (roots \<sigma> \<union> free \<sigma>) = {}" and sl: "s l' = s l"
    unfolding U_guar_def by simp_all
  from I have inv: "inv_state \<sigma>" and s0: "s l = {}" unfolding U_pre_def by simp_all
  have FR: "free \<sigma> \<union> roots \<sigma> \<subseteq> marked \<sigma>" using inv unfolding inv_state_def by blast
  have FR': "free \<sigma> \<union> roots \<sigma> \<subseteq> marked \<sigma>'"
  proof
    fix y assume y: "y \<in> free \<sigma> \<union> roots \<sigma>"
    with FR have yM: "y \<in> marked \<sigma>" by blast
    show "y \<in> marked \<sigma>'"
    proof (rule ccontr)
      assume "y \<notin> marked \<sigma>'"
      with yM y have "y \<in> (marked \<sigma> - marked \<sigma>') \<inter> (roots \<sigma> \<union> free \<sigma>)" by blast
      with m show False by blast
    qed
  qed
  have "free \<sigma>' \<union> roots \<sigma>' \<subseteq> marked \<sigma>'" using FR' f r by simp
  moreover have "card (free \<sigma>' \<inter> reach (roots \<sigma>') (hp \<sigma>')) \<le> 1"
    using inv h r f unfolding inv_state_def by simp
  moreover have "\<forall>a\<in>free \<sigma>'. \<forall>i. (a,i) \<notin> dom (hp \<sigma>')"
    using inv h f unfolding inv_state_def by simp
  ultimately have "inv_state \<sigma>'" unfolding inv_state_def by blast
  with sl s0 show ?thesis unfolding U_pre_def by simp
qed

text \<open>Mechanisation only: what interference does during Unmark: garbage does
  not decrease, and no garbage node becomes marked, since the Mutator marks
  only reachable nodes (rely-Collector).  U_env \<sigma>0 \<sigma> states the two.\<close>

definition U_env :: "('a,'i) state \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "U_env \<sigma>0 \<sigma> \<longleftrightarrow> garbage \<sigma>0 \<subseteq> garbage \<sigma> \<and> marked \<sigma> \<inter> garbage \<sigma>0 \<subseteq> marked \<sigma>0"

lemma U_env_refl: "U_env \<sigma> \<sigma>"
  unfolding U_env_def by blast

lemma U_env_trans:
  assumes "U_env \<sigma>0 \<sigma>1" and "U_env \<sigma>1 \<sigma>2"
  shows "U_env \<sigma>0 \<sigma>2"
proof -
  from assms have g1: "garbage \<sigma>0 \<subseteq> garbage \<sigma>1" and m1: "marked \<sigma>1 \<inter> garbage \<sigma>0 \<subseteq> marked \<sigma>0"
    and g2: "garbage \<sigma>1 \<subseteq> garbage \<sigma>2" and m2: "marked \<sigma>2 \<inter> garbage \<sigma>1 \<subseteq> marked \<sigma>1"
    unfolding U_env_def by blast+
  have "garbage \<sigma>0 \<subseteq> garbage \<sigma>2" using g1 g2 by blast
  moreover have "marked \<sigma>2 \<inter> garbage \<sigma>0 \<subseteq> marked \<sigma>0" using g1 m1 m2 by blast
  ultimately show ?thesis unfolding U_env_def by blast
qed

lemma U_env_step:
  assumes E: "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  shows "U_env \<sigma> \<sigma>'"
proof -
  have G: "garbage \<sigma> \<subseteq> garbage \<sigma>'" by (rule envs_garbage[OF E])
  have M: "marked \<sigma>' \<inter> garbage \<sigma> \<subseteq> marked \<sigma>"
  proof
    fix y assume y: "y \<in> marked \<sigma>' \<inter> garbage \<sigma>"
    show "y \<in> marked \<sigma>"
    proof (rule ccontr)
      assume yM: "y \<notin> marked \<sigma>"
      from y have yG: "y \<in> garbage \<sigma>" by blast
      from envs_garbage_unmarked[OF E yG yM] y show False by blast
    qed
  qed
  from G M show ?thesis unfolding U_env_def by blast
qed

lemma U_env_right: "U_env \<sigma>0 \<sigma> \<Longrightarrow> env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma> \<Longrightarrow> U_env \<sigma>0 \<sigma>'"
  by (rule U_env_trans[OF _ U_env_step])

lemma U_env_left: "env_step S \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0 \<Longrightarrow> U_env \<sigma>0' \<sigma> \<Longrightarrow> U_env \<sigma>0 \<sigma>"
  by (rule U_env_trans[OF U_env_step])

lemma U_env_guar:
  assumes "U_guar (l,\<sigma>) (l',\<sigma>')"
  shows "U_env \<sigma> \<sigma>'"
proof -
  from assms have h: "hp \<sigma>' = hp \<sigma>" and r: "roots \<sigma>' = roots \<sigma>" and f: "free \<sigma>' = free \<sigma>"
    and m: "marked \<sigma>' \<subseteq> marked \<sigma>" unfolding U_guar_def by simp_all
  have "garbage \<sigma>' = garbage \<sigma>" unfolding garbage_def using h r f by simp
  with m show ?thesis unfolding U_env_def by blast
qed

lemma envC_star_U_env:
  assumes "envC\<^sup>*\<^sup>* k0 k"
  shows "U_env (snd k0) (snd k)"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (rule U_env_refl)
next
  case (step y z)
  have E: "env_step (s (fst y)) (snd y) (snd z) \<or> snd z = snd y"
    using step.hyps(2) by (cases y, cases z) (simp add: rely_C_def)
  from U_env_right[OF step.IH E] show ?case .
qed

text \<open>Thesis: so-farU "holds despite environment interference" (Section
  4.8.2): garbage does not decrease, and the Mutator cannot mark garbage.\<close>

lemma so_farU_right:
  assumes Q: "so_farU c \<sigma>0 c' \<sigma>" and E: "U_env \<sigma> \<sigma>'"
  shows "so_farU c \<sigma>0 c' \<sigma>'"
proof -
  from Q have cc: "c \<subset> c'" and g: "garbage \<sigma>0 \<subseteq> garbage \<sigma>"
    and m: "marked \<sigma> \<inter> garbage \<sigma>0 \<subseteq> marked \<sigma>0 \<inter> garbage \<sigma>0"
    and u: "\<forall>y \<in> garbage \<sigma>0 \<inter> (c' - c). y \<notin> marked \<sigma>"
    unfolding so_farU_def by blast+
  from E have g': "garbage \<sigma> \<subseteq> garbage \<sigma>'" and m': "marked \<sigma>' \<inter> garbage \<sigma> \<subseteq> marked \<sigma>"
    unfolding U_env_def by blast+
  have "garbage \<sigma>0 \<subseteq> garbage \<sigma>'" using g g' by blast
  moreover have "marked \<sigma>' \<inter> garbage \<sigma>0 \<subseteq> marked \<sigma>0 \<inter> garbage \<sigma>0" using g m m' by blast
  moreover have "\<forall>y \<in> garbage \<sigma>0 \<inter> (c' - c). y \<notin> marked \<sigma>'" using g m' u by blast
  ultimately show ?thesis using cc unfolding so_farU_def by blast
qed

lemma so_farU_left:
  assumes E: "U_env \<sigma>0 \<sigma>0'" and Q: "so_farU c \<sigma>0' c' \<sigma>"
  shows "so_farU c \<sigma>0 c' \<sigma>"
proof -
  from Q have cc: "c \<subset> c'" and g: "garbage \<sigma>0' \<subseteq> garbage \<sigma>"
    and m: "marked \<sigma> \<inter> garbage \<sigma>0' \<subseteq> marked \<sigma>0' \<inter> garbage \<sigma>0'"
    and u: "\<forall>y \<in> garbage \<sigma>0' \<inter> (c' - c). y \<notin> marked \<sigma>"
    unfolding so_farU_def by blast+
  from E have g0: "garbage \<sigma>0 \<subseteq> garbage \<sigma>0'" and m0: "marked \<sigma>0' \<inter> garbage \<sigma>0 \<subseteq> marked \<sigma>0"
    unfolding U_env_def by blast+
  have "garbage \<sigma>0 \<subseteq> garbage \<sigma>" using g0 g by blast
  moreover have "marked \<sigma> \<inter> garbage \<sigma>0 \<subseteq> marked \<sigma>0 \<inter> garbage \<sigma>0" using g0 m m0 by blast
  moreover have "\<forall>y \<in> garbage \<sigma>0 \<inter> (c' - c). y \<notin> marked \<sigma>" using g0 u by blast
  ultimately show ?thesis using cc unfolding so_farU_def by blast
qed

subsection \<open>The Unmark loop\<close>

text \<open>Thesis: test, inv and so-far for the loop of Unmark (Section 4.8.2):
    testU  \<triangleq> consid \<noteq> Addr                                    (consid_test)
    invU   \<triangleq> consid \<subseteq> Addr                                    (U_inv)
    so-farU \<triangleq> consid \<subset> consid' \<and> garbage \<subseteq> garbage' \<and>
              (marked' \<inter> garbage) \<subseteq> (marked \<inter> garbage) \<and>
              \<forall>x \<in> (garbage \<inter> (consid' - consid)) \<cdot> x \<notin> marked'    (U_sofar)
  Addr is the type 'a, so invU always holds; U_inv states instead inv-\<Sigma> and
  s = {}, as the pre condition does.  so-farU is so_farU of GC_Unmark.\<close>

definition U_inv :: "('a,'i) cconf \<Rightarrow> bool" where
  "U_inv = U_pre"

definition U_sofar :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "U_sofar = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). so_farU (consid l0) \<sigma>0 (consid l) \<sigma>)"

definition U_P0 :: "('a,'i) cconf \<Rightarrow> bool" where
  "U_P0 = (\<lambda>(l,\<sigma>). consid l = {} \<and> inv_state \<sigma> \<and> s l = {})"

text \<open>Thesis: inv-\<Sigma> and s = {} hold despite interference (s is private).\<close>

lemma U_inv_stable: "stable hC (rely_C s) U_inv"
proof (rule stableC)
  fix l \<sigma> \<sigma>' assume I: "U_inv (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  from I have inv: "inv_state \<sigma>" and s0: "s l = {}" unfolding U_inv_def U_pre_def by simp_all
  have "inv_state \<sigma>'" by (rule envs_inv_state[OF E inv])
  with s0 show "U_inv (hC l \<sigma>', \<sigma>')" unfolding U_inv_def U_pre_def by simp
qed

lemma U_sofar_tolerates: "tolerates hC (rely_C s) I U_sofar"
proof (rule toleratesC)
  fix k0 l \<sigma> \<sigma>' assume Q: "U_sofar k0 (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  from Q k0 have "so_farU (consid l0) \<sigma>0 (consid l) \<sigma>" unfolding U_sofar_def by simp
  from so_farU_right[OF this U_env_step[OF E]] k0 show "U_sofar k0 (hC l \<sigma>', \<sigma>')"
    unfolding U_sofar_def by simp
next
  fix l0 \<sigma>0 \<sigma>0' k assume E: "env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0" and Q: "U_sofar (hC l0 \<sigma>0', \<sigma>0') k"
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  from Q k have "so_farU (consid l0) \<sigma>0' (consid l) \<sigma>" unfolding U_sofar_def by simp
  from so_farU_left[OF U_env_step[OF E] this] k show "U_sofar (l0,\<sigma>0) k"
    unfolding U_sofar_def by simp
qed

text \<open>Thesis: Lemma 13, transitivity (lemma13_so_farU_trans).\<close>

lemma U_sofar_trans:
  assumes "U_sofar k0 k1" and "U_sofar k1 k2"
  shows "U_sofar k0 k2"
proof -
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
  obtain l2 \<sigma>2 where k2: "k2 = (l2,\<sigma>2)" by (cases k2)
  from assms k0 k1 have A: "so_farU (consid l0) \<sigma>0 (consid l1) \<sigma>1" unfolding U_sofar_def by simp
  from assms k1 k2 have B: "so_farU (consid l1) \<sigma>1 (consid l2) \<sigma>2" unfolding U_sofar_def by simp
  from lemma13_so_farU_trans[OF A B] k0 k2 show ?thesis unfolding U_sofar_def by simp
qed

text \<open>Thesis: one iteration of the body (lines 3-6): pick x; if x is not a root
  and not free, unmark it; add x to consid.  "For any x that was garbage at
  the beginning of an iteration and was added to consid afterwards, will be
  unmarked by the end ... the Mutator cannot interfere with the unmarking of
  nodes in garbage".  Each statement has its own post condition.\<close>

definition U_pick_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "U_pick_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). x l \<notin> consid l0 \<and> consid l = consid l0 \<and> U_env \<sigma>0 \<sigma>)"

definition U_if_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "U_if_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). x l = x l0 \<and> consid l = consid l0 \<and> U_env \<sigma>0 \<sigma> \<and>
                   (x l0 \<in> garbage \<sigma>0 \<longrightarrow> x l0 \<notin> marked \<sigma>))"

definition U_add_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "U_add_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). consid l = consid l0 \<union> {x l0} \<and> x l = x l0 \<and> U_env \<sigma>0 \<sigma>)"

lemma U_pick_sat: "coll_sat (\<lambda>k. True) pick_x U_guar U_pick_post"
  unfolding pick_x_def
proof (rule rule_basicC)
  show "stable hC (rely_C s) (\<lambda>k. True)" by (rule stableC) simp
  show "tolerates hC (rely_C s) (\<lambda>k. True) U_pick_post"
  proof (rule toleratesC)
    fix k0 l \<sigma> \<sigma>' assume Q: "U_pick_post k0 (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    from Q k0 have a: "x l \<notin> consid l0" "consid l = consid l0" and u: "U_env \<sigma>0 \<sigma>"
      unfolding U_pick_post_def by simp_all
    have "U_env \<sigma>0 \<sigma>'" by (rule U_env_right[OF u E])
    with a k0 show "U_pick_post k0 (hC l \<sigma>', \<sigma>')" unfolding U_pick_post_def by simp
  next
    fix l0 \<sigma>0 \<sigma>0' k assume E: "env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0"
      and Q: "U_pick_post (hC l0 \<sigma>0', \<sigma>0') k"
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from Q k have a: "x l \<notin> consid l0" "consid l = consid l0" and u: "U_env \<sigma>0' \<sigma>"
      unfolding U_pick_post_def by simp_all
    have "U_env \<sigma>0 \<sigma>" by (rule U_env_left[OF E u])
    with a k show "U_pick_post (l0,\<sigma>0) k" unfolding U_pick_post_def by simp
  qed
qed (auto simp: U_guar_def U_pick_post_def U_env_refl)

lemma U_unmark_sat: "coll_sat (\<lambda>k. True \<and> U_test k) unmark_x U_guar U_if_post"
  unfolding unmark_x_def
proof (rule rule_basicC)
  show "stable hC (rely_C s) (\<lambda>k. True \<and> U_test k)"
  proof (rule stableC)
    fix l \<sigma> \<sigma>' assume P: "True \<and> U_test (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    from P have "x l \<notin> roots \<sigma> \<union> free \<sigma>" unfolding U_test_def by simp
    moreover have "roots \<sigma>' = roots \<sigma>" by (rule envs_roots[OF E])
    moreover have "free \<sigma>' \<subseteq> free \<sigma>" by (rule envs_free[OF E])
    ultimately have "x l \<notin> roots \<sigma>' \<union> free \<sigma>'" by blast
    then show "True \<and> U_test (hC l \<sigma>', \<sigma>')" unfolding U_test_def by simp
  qed
  show "tolerates hC (rely_C s) (\<lambda>k. True \<and> U_test k) U_if_post"
  proof (rule toleratesC)
    fix k0 l \<sigma> \<sigma>' assume Q: "U_if_post k0 (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    from Q k0 have a: "x l = x l0" "consid l = consid l0" and u: "U_env \<sigma>0 \<sigma>"
      and g: "x l0 \<in> garbage \<sigma>0 \<longrightarrow> x l0 \<notin> marked \<sigma>"
      unfolding U_if_post_def by simp_all
    have u': "U_env \<sigma>0 \<sigma>'" by (rule U_env_right[OF u E])
    have "x l0 \<notin> marked \<sigma>'" if G0: "x l0 \<in> garbage \<sigma>0"
    proof -
      have "x l0 \<notin> marked \<sigma>" using g G0 by blast
      moreover have "x l0 \<in> garbage \<sigma>" using u G0 unfolding U_env_def by blast
      ultimately show ?thesis using envs_garbage_unmarked[OF E] by blast
    qed
    with a u' k0 show "U_if_post k0 (hC l \<sigma>', \<sigma>')" unfolding U_if_post_def by simp
  next
    fix l0 \<sigma>0 \<sigma>0' k assume E: "env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0"
      and Q: "U_if_post (hC l0 \<sigma>0', \<sigma>0') k"
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from Q k have a: "x l = x l0" "consid l = consid l0" and u: "U_env \<sigma>0' \<sigma>"
      and g: "x l0 \<in> garbage \<sigma>0' \<longrightarrow> x l0 \<notin> marked \<sigma>"
      unfolding U_if_post_def by simp_all
    have u0: "U_env \<sigma>0 \<sigma>" by (rule U_env_left[OF E u])
    have "garbage \<sigma>0 \<subseteq> garbage \<sigma>0'" by (rule envs_garbage[OF E])
    with g have "x l0 \<in> garbage \<sigma>0 \<longrightarrow> x l0 \<notin> marked \<sigma>" by blast
    with a u0 k show "U_if_post (l0,\<sigma>0) k" unfolding U_if_post_def by simp
  qed
next
  fix l \<sigma> l' \<sigma>'
  assume P: "True \<and> U_test (l,\<sigma>)"
    and St: "(\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l \<and> \<sigma>' = \<sigma>\<lparr>marked := marked \<sigma> - {x l}\<rparr>) (l,\<sigma>) (l',\<sigma>')"
  from St have l': "l' = l" and \<sigma>': "\<sigma>' = \<sigma>\<lparr>marked := marked \<sigma> - {x l}\<rparr>" by simp_all
  from P have xn: "x l \<notin> roots \<sigma> \<union> free \<sigma>" unfolding U_test_def by simp
  have G: "U_guar (l,\<sigma>) (l',\<sigma>')" using l' \<sigma>' xn unfolding U_guar_def by auto
  have "garbage \<sigma>' = garbage \<sigma>" using \<sigma>' unfolding garbage_def by simp
  then have "U_env \<sigma> \<sigma>'" using \<sigma>' unfolding U_env_def by auto
  moreover have "x l \<notin> marked \<sigma>'" using \<sigma>' by simp
  ultimately have "U_if_post (l,\<sigma>) (hC l' \<sigma>', \<sigma>')" using l' unfolding U_if_post_def by simp
  with G show "U_guar (l,\<sigma>) (l',\<sigma>') \<and> U_if_post (l,\<sigma>) (hC l' \<sigma>', \<sigma>')" by blast
qed

lemma U_add_sat: "coll_sat (\<lambda>k. True) consid_add U_guar U_add_post"
  unfolding consid_add_def
proof (rule rule_basicC)
  show "stable hC (rely_C s) (\<lambda>k. True)" by (rule stableC) simp
  show "tolerates hC (rely_C s) (\<lambda>k. True) U_add_post"
  proof (rule toleratesC)
    fix k0 l \<sigma> \<sigma>' assume Q: "U_add_post k0 (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    from Q k0 have a: "consid l = consid l0 \<union> {x l0}" "x l = x l0" and u: "U_env \<sigma>0 \<sigma>"
      unfolding U_add_post_def by simp_all
    have "U_env \<sigma>0 \<sigma>'" by (rule U_env_right[OF u E])
    with a k0 show "U_add_post k0 (hC l \<sigma>', \<sigma>')" unfolding U_add_post_def by simp
  next
    fix l0 \<sigma>0 \<sigma>0' k assume E: "env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0"
      and Q: "U_add_post (hC l0 \<sigma>0', \<sigma>0') k"
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from Q k have a: "consid l = consid l0 \<union> {x l0}" "x l = x l0" and u: "U_env \<sigma>0' \<sigma>"
      unfolding U_add_post_def by simp_all
    have "U_env \<sigma>0 \<sigma>" by (rule U_env_left[OF E u])
    with a k show "U_add_post (l0,\<sigma>0) k" unfolding U_add_post_def by simp
  qed
qed (auto simp: U_guar_def U_add_post_def U_env_refl)

text \<open>Thesis: line 4, "if x \<notin> (roots \<union> free) then marked \<leftarrow> marked - {x}".
  If the test fails, x is a root or free, so it is not garbage.\<close>

lemma U_if_sat: "coll_sat (\<lambda>k. True) (IfThen U_test unmark_x) U_guar U_if_post"
proof (rule rule_if[OF U_unmark_sat])
  fix k0 k :: "('a,'i) cconf"
  assume P: "True \<and> \<not> U_test k0" and RS: "envC\<^sup>*\<^sup>* k0 k"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  from RS k0 k have RS': "envC\<^sup>*\<^sup>* (l0,\<sigma>0) (l,\<sigma>)" by simp
  from P k0 have "x l0 \<in> roots \<sigma>0 \<union> free \<sigma>0" unfolding U_test_def by simp
  then have ng: "x l0 \<notin> garbage \<sigma>0" unfolding garbage_def using reach_refl[of "roots \<sigma>0" "hp \<sigma>0"] by blast
  have u: "U_env \<sigma>0 \<sigma>" using envC_star_U_env[OF RS'] by simp
  from envC_star_sel[OF RS'] u ng show "U_if_post k0 k" using k0 k unfolding U_if_post_def by simp
next
  show "stable hC (rely_C s) (\<lambda>k. True)" by (rule stableC) simp
next
  fix k :: "('a,'i) cconf"
  show "U_test (hupd hC k) = U_test k" by (cases k) (simp add: U_test_def)
next
  fix k0 k0' k :: "('a,'i) cconf"
  assume E: "envC k0 k0'" and Q: "U_if_post k0' k"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l0' \<sigma>0' where k0': "k0' = (l0',\<sigma>0')" by (cases k0')
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  from E k0 k0' have l0': "l0' = hC l0 \<sigma>0'" and E': "env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0"
    by (simp_all add: rely_C_def)
  from Q k0' k l0' have a: "x l = x l0" "consid l = consid l0" and u: "U_env \<sigma>0' \<sigma>"
    and g: "x l0 \<in> garbage \<sigma>0' \<longrightarrow> x l0 \<notin> marked \<sigma>"
    unfolding U_if_post_def by simp_all
  have u0: "U_env \<sigma>0 \<sigma>" by (rule U_env_left[OF E' u])
  have "garbage \<sigma>0 \<subseteq> garbage \<sigma>0'" by (rule envs_garbage[OF E'])
  with g have "x l0 \<in> garbage \<sigma>0 \<longrightarrow> x l0 \<notin> marked \<sigma>" by blast
  with a u0 k0 k show "U_if_post k0 k" unfolding U_if_post_def by simp
qed

text \<open>Thesis: one iteration establishes so-farU, and keeps inv-\<Sigma> and s = {}.\<close>

lemma U_body_sat:
  "coll_sat (\<lambda>k. U_inv k \<and> consid_test k) U_body U_guar (\<lambda>k0 k. U_inv k \<and> U_sofar k0 k)"
proof -
  have "coll_sat (\<lambda>k. True) (Seq (IfThen U_test unmark_x) consid_add :: ('a,'i) ccom) U_guar
          (seq_post U_if_post U_add_post)"
    by (rule rule_seq[OF U_if_sat U_add_sat]) simp
  then have V: "coll_sat (\<lambda>k. True) (U_body :: ('a,'i) ccom) U_guar
                  (seq_post U_pick_post (seq_post U_if_post U_add_post))"
    unfolding U_body_def by (rule rule_seq[OF U_pick_sat]) simp
  have SF: "U_sofar k0 k"
    if "U_inv k0 \<and> consid_test k0" and "seq_post U_pick_post (seq_post U_if_post U_add_post) k0 k"
    for k0 k :: "('a,'i) cconf"
  proof -
    from that(2) obtain k1 k2 where 1: "U_pick_post k0 k1" and 2: "U_if_post k1 k2"
      and 3: "U_add_post k2 k"
      unfolding seq_post_def by blast
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
    obtain l2 \<sigma>2 where k2: "k2 = (l2,\<sigma>2)" by (cases k2)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from 1 k0 k1 have a: "x l1 \<notin> consid l0" "consid l1 = consid l0" and u1: "U_env \<sigma>0 \<sigma>1"
      unfolding U_pick_post_def by simp_all
    from 2 k1 k2 have b: "x l2 = x l1" "consid l2 = consid l1" and u2: "U_env \<sigma>1 \<sigma>2"
      and g: "x l1 \<in> garbage \<sigma>1 \<longrightarrow> x l1 \<notin> marked \<sigma>2"
      unfolding U_if_post_def by simp_all
    from 3 k2 k have c: "consid l = consid l2 \<union> {x l2}" and u3: "U_env \<sigma>2 \<sigma>"
      unfolding U_add_post_def by simp_all
    have cc: "consid l = consid l0 \<union> {x l1}" using a b c by simp
    have U: "U_env \<sigma>0 \<sigma>" by (rule U_env_trans[OF U_env_trans[OF u1 u2] u3])
    have "consid l0 \<subset> consid l" using cc a(1) by auto
    moreover have "garbage \<sigma>0 \<subseteq> garbage \<sigma>" using U unfolding U_env_def by blast
    moreover have "marked \<sigma> \<inter> garbage \<sigma>0 \<subseteq> marked \<sigma>0 \<inter> garbage \<sigma>0" using U unfolding U_env_def by blast
    moreover have "\<forall>y \<in> garbage \<sigma>0 \<inter> (consid l - consid l0). y \<notin> marked \<sigma>"
    proof
      fix y assume y: "y \<in> garbage \<sigma>0 \<inter> (consid l - consid l0)"
      then have yx: "y = x l1" using cc by auto
      have "y \<in> garbage \<sigma>1" using y u1 unfolding U_env_def by blast
      with g yx have m2: "y \<notin> marked \<sigma>2" by blast
      have "y \<in> garbage \<sigma>2" using \<open>y \<in> garbage \<sigma>1\<close> u2 unfolding U_env_def by blast
      with m2 u3 show "y \<notin> marked \<sigma>" unfolding U_env_def by blast
    qed
    ultimately have "so_farU (consid l0) \<sigma>0 (consid l) \<sigma>" unfolding so_farU_def by blast
    then show ?thesis using k0 k unfolding U_sofar_def by simp
  qed
  have V': "coll_sat (\<lambda>k. U_inv k \<and> consid_test k) (U_body :: ('a,'i) ccom) U_guar U_sofar"
    by (rule rule_weaken[OF V _ _ SF]) simp_all
  have IG: "U_inv k'" if I: "U_inv k" and G: "U_guar k k'" for k k' :: "('a,'i) cconf"
  proof -
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from U_guar_pre[OF G[unfolded k k'] I[unfolded k U_inv_def]] k' show ?thesis
      unfolding U_inv_def by simp
  qed
  have V'': "coll_sat (\<lambda>k. U_inv k \<and> consid_test k) (U_body :: ('a,'i) ccom)
               (\<lambda>k k'. U_guar k k' \<and> U_inv k) (\<lambda>k0 k. U_sofar k0 k \<and> U_inv k)"
    by (rule rule_inv[OF V' _ U_inv_stable IG]) simp
  show ?thesis by (rule rule_weaken[OF V'']) auto
qed

text \<open>Thesis: the loop of Unmark, by the while rule with Lemma 13 and Theorem 4:
  when the loop exits, consid' = Addr, and with consid = {} at the start
  so-farU gives post-Unmark.  The loop's post condition also keeps U_env
  from the start, and both are satisfied despite interference after the
  loop: the Mutator cannot mark garbage.\<close>

definition U_loop_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "U_loop_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). post_Unmark \<sigma>0 \<sigma> \<and> U_env \<sigma>0 \<sigma>)"

lemma U_loop_post_right:
  assumes Q: "U_loop_post (l0,\<sigma>0) (l,\<sigma>)" and E: "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  shows "U_loop_post (l0,\<sigma>0) (l',\<sigma>')"
proof -
  from Q have P: "garbage \<sigma>0 \<inter> marked \<sigma> = {}" and u: "U_env \<sigma>0 \<sigma>"
    unfolding U_loop_post_def post_Unmark_def by simp_all
  have u': "U_env \<sigma>0 \<sigma>'" by (rule U_env_right[OF u E])
  have us: "U_env \<sigma> \<sigma>'" by (rule U_env_step[OF E])
  have "garbage \<sigma>0 \<inter> marked \<sigma>' = {}"
    using P u us unfolding U_env_def by blast
  with u' show ?thesis unfolding U_loop_post_def post_Unmark_def by simp
qed

lemma U_loop_sat: "coll_sat U_P0 (While consid_test U_body) U_guar U_loop_post"
proof (rule rule_while[where I = U_inv and sofar = U_sofar,
                       OF _ U_body_sat U_inv_stable _ U_sofar_trans U_sofar_tolerates])
  fix k :: "('a,'i) cconf" assume "U_P0 k"
  then show "U_inv k" by (cases k) (simp add: U_P0_def U_inv_def U_pre_def)
next
  fix k :: "('a,'i) cconf"
  show "consid_test (hupd hC k) = consid_test k" by (cases k) (simp add: consid_test_def)
next
  fix k0 k :: "('a,'i) cconf"
  assume P0: "U_P0 k0" and T: "\<not> consid_test k" and W: "U_sofar k0 k \<or> envC\<^sup>*\<^sup>* k0 k"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  from P0 k0 have c0: "consid l0 = {}" by (simp add: U_P0_def)
  from T k have c: "consid l = UNIV" by (simp add: consid_test_def)
  from W show "U_loop_post k0 k"
  proof
    assume "U_sofar k0 k"
    then have SF: "so_farU {} \<sigma>0 UNIV \<sigma>" using k0 k c0 c by (simp add: U_sofar_def)
    have "post_Unmark \<sigma>0 \<sigma>" by (rule theorem4_post_Unmark[OF SF])
    moreover have "U_env \<sigma>0 \<sigma>" using SF unfolding so_farU_def U_env_def by blast
    ultimately show ?thesis using k0 k by (simp add: U_loop_post_def)
  next
    assume "envC\<^sup>*\<^sup>* k0 k"
    then have "envC\<^sup>*\<^sup>* (l0,\<sigma>0) (l,\<sigma>)" using k0 k by simp
    from envC_star_sel(1)[OF this] c0 c show ?thesis by simp
  qed
next
  fix k0 k k' :: "('a,'i) cconf"
  assume Q: "U_loop_post k0 k" and E: "envC k k'"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
  from E k k' have E': "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>" by (simp add: rely_C_def)
  from U_loop_post_right[OF Q[unfolded k0 k] E'] k0 k' show "U_loop_post k0 k'" by simp
qed

text \<open>Thesis: line 1, consid \<leftarrow> {}.\<close>

definition U_reset_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "U_reset_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). consid l = {} \<and> U_env \<sigma>0 \<sigma>)"

lemma U_reset_sat: "coll_sat (\<lambda>k. True) consid_reset U_guar U_reset_post"
  unfolding consid_reset_def
proof (rule rule_basicC)
  show "stable hC (rely_C s) (\<lambda>k. True)" by (rule stableC) simp
  show "tolerates hC (rely_C s) (\<lambda>k. True) U_reset_post"
  proof (rule toleratesC)
    fix k0 l \<sigma> \<sigma>' assume Q: "U_reset_post k0 (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    from Q k0 have a: "consid l = {}" and u: "U_env \<sigma>0 \<sigma>" unfolding U_reset_post_def by simp_all
    have "U_env \<sigma>0 \<sigma>'" by (rule U_env_right[OF u E])
    with a k0 show "U_reset_post k0 (hC l \<sigma>', \<sigma>')" unfolding U_reset_post_def by simp
  next
    fix l0 \<sigma>0 \<sigma>0' k assume E: "env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0"
      and Q: "U_reset_post (hC l0 \<sigma>0', \<sigma>0') k"
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from Q k have a: "consid l = {}" and u: "U_env \<sigma>0' \<sigma>" unfolding U_reset_post_def by simp_all
    have "U_env \<sigma>0 \<sigma>" by (rule U_env_left[OF E u])
    with a k show "U_reset_post (l0,\<sigma>0) k" unfolding U_reset_post_def by simp
  qed
qed (auto simp: U_guar_def U_reset_post_def U_env_refl)

text \<open>Thesis: the property of the whole of Unmark that Sublemma 1 (Section
  4.8.5) relies on: "by applying the rely condition to each environment step
  of Unmark and using that garbage never decreases during this phase
  (so-farU) and that the Collector does not modify hp during Unmark", no
  pointer out of the old free or reachable region points into the old
  garbage.\<close>

text \<open>Mechanisation only: conjunct (4.2) of rely-Collector: a pointer the
  environment changes does not point into garbage.\<close>

lemma rely_new_target:
  assumes "rely_Collector S \<sigma> \<sigma>'" and "hp \<sigma>' e \<noteq> hp \<sigma> e" and "hp \<sigma>' e = Some b"
  shows "b \<notin> garbage \<sigma>"
proof -
  have A6: "hp \<sigma>' e \<noteq> hp \<sigma> e \<longrightarrow>
              fst e \<notin> garbage \<sigma> \<and> (\<forall>b. hp \<sigma>' e = Some b \<longrightarrow> b \<notin> garbage \<sigma>)"
    using assms(1)[unfolded rely_Collector_def, THEN conjunct2, THEN conjunct2, THEN conjunct2,
                   THEN conjunct2, THEN conjunct2, THEN conjunct1]
    by (rule spec)
  from mp[OF A6 assms(2)] have "\<forall>b. hp \<sigma>' e = Some b \<longrightarrow> b \<notin> garbage \<sigma>" by (rule conjunct2)
  with assms(3) show ?thesis by blast
qed

definition U_trace :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "U_trace = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). garbage \<sigma>0 \<subseteq> garbage \<sigma> \<and> no_new_ptr \<sigma>0 \<sigma>)"

lemma U_trace_env:
  assumes T: "U_trace (l0,\<sigma>0) (l,\<sigma>)" and E: "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  shows "U_trace (l0,\<sigma>0) (l',\<sigma>')"
proof -
  from T have g: "garbage \<sigma>0 \<subseteq> garbage \<sigma>" and N: "no_new_ptr \<sigma>0 \<sigma>"
    unfolding U_trace_def by simp_all
  have g': "garbage \<sigma>0 \<subseteq> garbage \<sigma>'" using g envs_garbage[OF E] by blast
  have "no_new_ptr \<sigma>0 \<sigma>'"
    unfolding no_new_ptr_def
  proof (intro ballI allI impI)
    fix y j b assume y: "y \<in> free \<sigma>0 \<union> reach (roots \<sigma>0) (hp \<sigma>0)" and hb: "hp \<sigma>' (y,j) = Some b"
    show "b \<in> free \<sigma>0 \<union> reach (roots \<sigma>0) (hp \<sigma>0)"
    proof (cases "hp \<sigma>' (y,j) = hp \<sigma> (y,j)")
      case True
      with hb have "hp \<sigma> (y,j) = Some b" by simp
      with N y show ?thesis unfolding no_new_ptr_def by blast
    next
      case False
      then have "\<sigma>' \<noteq> \<sigma>" by auto
      with E have "env_step S \<sigma> \<sigma>'" by blast
      then have R: "rely_Collector S \<sigma> \<sigma>'" unfolding env_step_def by blast
      from rely_new_target[OF R False hb] have "b \<notin> garbage \<sigma>" .
      with g have "b \<notin> garbage \<sigma>0" by blast
      then show ?thesis unfolding garbage_def by blast
    qed
  qed
  with g' show ?thesis unfolding U_trace_def by simp
qed

text \<open>Thesis: Unmark meets its specification (Section 4.8.2): "by Lemma 13 and
  Theorem 4".  Every step of Unmark is taken in a state where inv-\<Sigma> and
  s = {} hold, so it is a step of guar-Unmark.\<close>

theorem Unmark_sat:
  "coll_sat U_pre Unmark (\<lambda>k k'. U_guar k k' \<and> U_inv k) (\<lambda>k0 k. U_post k0 k \<and> U_inv k)"
proof -
  have IG: "U_inv k'" if I: "U_inv k" and G: "U_guar k k'" for k k' :: "('a,'i) cconf"
  proof -
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from U_guar_pre[OF G[unfolded k k'] I[unfolded k U_inv_def]] k' show ?thesis
      unfolding U_inv_def by simp
  qed
  have R0: "coll_sat U_pre (consid_reset :: ('a,'i) ccom) U_guar U_reset_post"
    by (rule rule_weaken[OF U_reset_sat]) simp_all
  have R1: "coll_sat U_pre (consid_reset :: ('a,'i) ccom) (\<lambda>k k'. U_guar k k' \<and> U_inv k)
              (\<lambda>k0 k. U_reset_post k0 k \<and> U_inv k)"
    by (rule rule_inv[OF R0 _ U_inv_stable IG]) (simp add: U_inv_def)
  have R: "coll_sat U_pre (consid_reset :: ('a,'i) ccom) U_guar (\<lambda>k0 k. U_reset_post k0 k \<and> U_inv k)"
    by (rule rule_weaken[OF R1]) simp_all
  have V1: "coll_sat U_pre (Unmark :: ('a,'i) ccom) U_guar
              (seq_post (\<lambda>k0 k. U_reset_post k0 k \<and> U_inv k) U_loop_post)"
    unfolding Unmark_def
    by (rule rule_seq[OF R U_loop_sat])
       (auto simp: U_reset_post_def U_P0_def U_inv_def U_pre_def split_beta)
  have V2: "coll_sat U_pre (Unmark :: ('a,'i) ccom) U_guar
              (\<lambda>k0 k. seq_post (\<lambda>k0 k. U_reset_post k0 k \<and> U_inv k) U_loop_post k0 k \<and> U_trace k0 k)"
  proof (rule rule_trace[OF V1])
    fix k :: "('a,'i) cconf" assume P: "U_pre k"
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from P k have inv: "inv_state \<sigma>" unfolding U_pre_def by simp
    have "no_new_ptr \<sigma> \<sigma>"
      unfolding no_new_ptr_def
    proof (intro ballI allI impI)
      fix y j b assume y: "y \<in> free \<sigma> \<union> reach (roots \<sigma>) (hp \<sigma>)" and hb: "hp \<sigma> (y,j) = Some b"
      from y show "b \<in> free \<sigma> \<union> reach (roots \<sigma>) (hp \<sigma>)"
      proof
        assume "y \<in> free \<sigma>"
        with inv hb have False unfolding inv_state_def by (auto simp: domIff)
        then show ?thesis ..
      next
        assume "y \<in> reach (roots \<sigma>) (hp \<sigma>)"
        from reach_step[OF this hb] show ?thesis by blast
      qed
    qed
    then show "U_trace k k" using k unfolding U_trace_def by simp
  next
    fix k0 k k' :: "('a,'i) cconf" assume T: "U_trace k0 k" and E: "envC k k'"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from E k k' have E': "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>" by (simp add: rely_C_def)
    from U_trace_env[OF T[unfolded k0 k] E'] k0 k' show "U_trace k0 k'" by simp
  next
    fix k0 k k' :: "('a,'i) cconf" assume T: "U_trace k0 k" and G: "U_guar k k'"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from G k k' have h: "hp \<sigma>' = hp \<sigma>" and r: "roots \<sigma>' = roots \<sigma>" and f: "free \<sigma>' = free \<sigma>"
      unfolding U_guar_def by simp_all
    have g: "garbage \<sigma>' = garbage \<sigma>" unfolding garbage_def using h r f by simp
    from T[unfolded k0 k] have "garbage \<sigma>0 \<subseteq> garbage \<sigma> \<and> no_new_ptr \<sigma>0 \<sigma>"
      unfolding U_trace_def by simp
    with g h have "garbage \<sigma>0 \<subseteq> garbage \<sigma>' \<and> no_new_ptr \<sigma>0 \<sigma>'"
      unfolding no_new_ptr_def by simp
    then show "U_trace k0 k'" using k0 k' unfolding U_trace_def by simp
  qed
  have V3: "coll_sat U_pre (Unmark :: ('a,'i) ccom) (\<lambda>k k'. U_guar k k' \<and> U_inv k)
              (\<lambda>k0 k. (seq_post (\<lambda>k0 k. U_reset_post k0 k \<and> U_inv k) U_loop_post k0 k \<and>
                        U_trace k0 k) \<and> U_inv k)"
    by (rule rule_inv[OF V2 _ U_inv_stable IG]) (simp add: U_inv_def)
  have Q: "U_post k0 k"
    if "seq_post (\<lambda>k0 k. U_reset_post k0 k \<and> U_inv k) U_loop_post k0 k" and "U_trace k0 k"
    for k0 k :: "('a,'i) cconf"
  proof -
    from that(1) obtain k1 where 1: "U_reset_post k0 k1" and 2: "U_loop_post k1 k"
      unfolding seq_post_def by blast
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from 1 k0 k1 have u1: "U_env \<sigma>0 \<sigma>1" unfolding U_reset_post_def by simp
    from 2 k1 k have P: "garbage \<sigma>1 \<inter> marked \<sigma> = {}"
      unfolding U_loop_post_def post_Unmark_def by simp
    have "garbage \<sigma>0 \<subseteq> garbage \<sigma>1" using u1 unfolding U_env_def by blast
    with P have "post_Unmark \<sigma>0 \<sigma>" unfolding post_Unmark_def by blast
    moreover from that(2) k0 k have "garbage \<sigma>0 \<subseteq> garbage \<sigma> \<and> no_new_ptr \<sigma>0 \<sigma>"
      unfolding U_trace_def by simp
    ultimately show ?thesis using k0 k unfolding U_post_def by simp
  qed
  show ?thesis by (rule rule_weaken[OF V3]) (auto intro: Q)
qed

end
