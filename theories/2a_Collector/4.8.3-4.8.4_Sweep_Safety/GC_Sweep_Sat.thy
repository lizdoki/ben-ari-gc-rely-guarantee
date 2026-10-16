(*  GC_Sweep_Sat: Add-to-free and Sweep meet their specifications (Sections
    4.8.3 and 4.8.4).

    The specifications of Sweep and Add-to-free (Appendix C); what holds in
    every state of Sweep (inv-safe, Lemmas 15 and 16) and of Add-to-free
    (invA, Lemmas 17 and 18); the test, inv and so-far of the two loops; the
    statements one by one; and Add-to-free and Sweep meeting their
    specifications, with Lemma 14 and Theorem 5 of GC_Sweep.

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
      Add-to-free meets its specification           AddToFree_sat
      Sweep meets its specification                 Sweep_sat             *)

theory GC_Sweep_Sat
  imports GC_Sweep GC_Safety GC_Unmark_Sat
begin

section \<open>Interference and the Add-to-free invariant (Lemma 17)\<close>

text \<open>Thesis: Lemma 17 (an environment step preserves invA).\<close>

lemma envs_invA:
  assumes E: "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>" and A: "invA y \<sigma>"
  shows "invA y \<sigma>'"
  using E
proof
  assume "env_step S \<sigma> \<sigma>'"
  then have "rely_Collector S \<sigma> \<sigma>'" unfolding env_step_def by blast
  from lemma17_env_invA[OF this A] show ?thesis .
next
  assume "\<sigma>' = \<sigma>"
  with A show ?thesis by simp
qed

text \<open>Mechanisation only: the same, for an environment step alone.\<close>

lemmas env_invA = envs_invA[OF disjI1]

section \<open>Add-to-free and Sweep (Sections 4.8.3 and 4.8.4)\<close>

text \<open>Thesis: the guarantee of Sweep (Section 4.8.3, Appendix C),
    guar free \<subseteq> free' \<and> marked \<subseteq> marked' \<and> hp' \<subseteq> hp,
  and of Add-to-free(x), for the steps that change free or hp,
    guar marked \<subseteq> marked' \<and> free \<subseteq> free' \<and> hp' \<subseteq> hp \<and> (marked' - marked) \<subseteq> {x} \<and>
         (free' - free) \<subseteq> {x} \<and> dom (hp - hp') \<subseteq> ({x} \<times> Index).
  In Isabelle S_guar says, step by step, that a step of Sweep satisfies
  guar-Sweep (GC_Collector_Steps), and either leaves free and hp alone or is a step of
  Add-to-free(x) taken while invA(x, \<sigma>) holds, exactly as in step-Collector
  (Section 4.7.2) and the proof of Theorem 6; that it marks at most x; that
  it keeps inv-\<Sigma>; and that of the private variables only consid, x, i and
  cleared change.\<close>

definition S_guar :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "S_guar = (\<lambda>(l,\<sigma>) (l',\<sigma>'). guar_Sweep \<sigma> \<sigma>' \<and>
      ((free \<sigma>' = free \<sigma> \<and> hp \<sigma>' = hp \<sigma>) \<or> (guar_AddToFree (x l) \<sigma> \<sigma>' \<and> invA (x l) \<sigma>)) \<and>
      marked \<sigma>' - marked \<sigma> \<subseteq> {x l} \<and> (inv_state \<sigma> \<longrightarrow> inv_state \<sigma>') \<and>
      s l' = s l \<and> checked l' = checked l \<and> mc l' = mc l \<and> Fv l' = Fv l)"

text \<open>Thesis: what holds in every state of Sweep: inv-\<Sigma>, inv-safe (Section
  4.8.4: "the pre condition of Sweep is exactly the requirement of this
  invariant", and Lemmas 15 and 16 keep it) and s = {} (Section 4.7.2).\<close>

definition S_J :: "('a,'i) cconf \<Rightarrow> bool" where
  "S_J = (\<lambda>(l,\<sigma>). inv_state \<sigma> \<and> inv_safe \<sigma> \<and> s l = {})"

text \<open>Thesis: Lemma 15 (with inv-\<Sigma> and s private): S_J holds despite
  interference; and while inv-safe holds, "no environment steps change
  marked during this phase" (Section 4.8.3).\<close>

lemma S_J_stable: "stable hC (rely_C s) S_J"
proof (rule stableC)
  fix l \<sigma> \<sigma>' assume J: "S_J (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  from J have inv: "inv_state \<sigma>" and IS: "inv_safe \<sigma>" and s0: "s l = {}" unfolding S_J_def by simp_all
  have "inv_state \<sigma>'" by (rule envs_inv_state[OF E inv])
  moreover have "inv_safe \<sigma>'" using envs_inv_safe[OF E IS] by blast
  ultimately show "S_J (hC l \<sigma>', \<sigma>')" using s0 unfolding S_J_def by simp
qed

lemma S_J_marked:
  assumes "S_J (l,\<sigma>)" and "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  shows "marked \<sigma>' = marked \<sigma>"
proof -
  from assms(1) have "inv_safe \<sigma>" unfolding S_J_def by simp
  from envs_inv_safe[OF assms(2) this] show ?thesis by blast
qed

text \<open>Thesis: Lemma 16 (a step of Sweep keeps inv-safe), with inv-\<Sigma> and s.\<close>

lemma S_guar_J:
  assumes G: "S_guar (l,\<sigma>) (l',\<sigma>')" and J: "S_J (l,\<sigma>)"
  shows "S_J (l',\<sigma>')"
proof -
  from G have GS: "guar_Sweep \<sigma> \<sigma>'" and I: "inv_state \<sigma> \<longrightarrow> inv_state \<sigma>'" and sl: "s l' = s l"
    unfolding S_guar_def by simp_all
  from J have inv: "inv_state \<sigma>" and IS: "inv_safe \<sigma>" and s0: "s l = {}" unfolding S_J_def by simp_all
  have "inv_safe \<sigma>'" by (rule lemma16_prog_inv_safe[OF GS IS])
  with I inv sl s0 show ?thesis unfolding S_J_def by simp
qed

text \<open>Mechanisation only: every step of Sweep, taken where S_J holds, is a step
  of step-Collector (Section 4.7.2) and keeps inv-\<Sigma>.\<close>

lemma S_guar_step:
  assumes G: "S_guar (l,\<sigma>) (l',\<sigma>')" and J: "S_J (l,\<sigma>)"
  shows "step_Collector (s l) \<sigma> (s l') \<sigma>' \<and> inv_state \<sigma>'"
proof -
  from G have GS: "guar_Sweep \<sigma> \<sigma>'" and I: "inv_state \<sigma> \<longrightarrow> inv_state \<sigma>'" and sl: "s l' = s l"
    and D: "(free \<sigma>' = free \<sigma> \<and> hp \<sigma>' = hp \<sigma>) \<or> (guar_AddToFree (x l) \<sigma> \<sigma>' \<and> invA (x l) \<sigma>)"
    unfolding S_guar_def by simp_all
  from J have inv: "inv_state \<sigma>" and s0: "s l = {}" unfolding S_J_def by simp_all
  from D have "(free \<sigma>' = free \<sigma> \<and> hp \<sigma>' = hp \<sigma>) \<or> (\<exists>y. guar_AddToFree y \<sigma> \<sigma>' \<and> invA y \<sigma>)" by blast
  with GS sl s0 have "step_Collector (s l) \<sigma> (s l') \<sigma>'" unfolding step_Collector_def by simp
  with I inv show ?thesis by simp
qed

text \<open>Mechanisation only: a statement of Sweep that changes only private
  variables.  Its post condition says what it does to them, that marked does
  not change (by S_J, interference marks nothing), that the history
  variable only records, and that S_J still holds.\<close>

lemma S_private_sat:
  assumes R: "\<And>l \<sigma> l' \<sigma>'. r (l,\<sigma>) (l',\<sigma>') \<Longrightarrow>
                \<sigma>' = \<sigma> \<and> s l' = s l \<and> checked l' = checked l \<and> mc l' = mc l \<and> Fv l' = Fv l \<and> Pr l l'"
    and PrR: "\<And>l0 l \<sigma>. Pr l0 (hC l \<sigma>) = Pr l0 l"
    and PrL: "\<And>l0 l \<sigma>. Pr (hC l0 \<sigma>) l = Pr l0 l"
  shows "coll_sat S_J (Basic r) S_guar
           (\<lambda>(l0,\<sigma>0) (l,\<sigma>). Pr l0 l \<and> marked \<sigma> = marked \<sigma>0 \<and> hist_ok (l0,\<sigma>0) (l,\<sigma>) \<and> S_J (l,\<sigma>))"
proof (rule rule_basicC[OF S_J_stable])
  show "tolerates hC (rely_C s) S_J
          (\<lambda>(l0,\<sigma>0) (l,\<sigma>). Pr l0 l \<and> marked \<sigma> = marked \<sigma>0 \<and> hist_ok (l0,\<sigma>0) (l,\<sigma>) \<and> S_J (l,\<sigma>))"
  proof (rule toleratesC)
    fix k0 l \<sigma> \<sigma>'
    assume Q: "(\<lambda>(l0,\<sigma>0) (l,\<sigma>). Pr l0 l \<and> marked \<sigma> = marked \<sigma>0 \<and> hist_ok (l0,\<sigma>0) (l,\<sigma>) \<and> S_J (l,\<sigma>)) k0 (l,\<sigma>)"
      and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    from Q k0 have a: "Pr l0 l" and m: "marked \<sigma> = marked \<sigma>0" and H: "hist_ok (l0,\<sigma>0) (l,\<sigma>)"
      and J: "S_J (l,\<sigma>)" by simp_all
    have m': "marked \<sigma>' = marked \<sigma>" by (rule S_J_marked[OF J E])
    have H': "hist_ok (l0,\<sigma>0) (hC l \<sigma>', \<sigma>')" using hist_ok_step[OF H refl, of \<sigma>'] by blast
    have J': "S_J (hC l \<sigma>', \<sigma>')" by (rule stableD[OF S_J_stable J]) (simp add: rely_C_def E)
    from a m m' H' J' k0 PrR
    show "(\<lambda>(l0,\<sigma>0) (l,\<sigma>). Pr l0 l \<and> marked \<sigma> = marked \<sigma>0 \<and> hist_ok (l0,\<sigma>0) (l,\<sigma>) \<and> S_J (l,\<sigma>)) k0 (hC l \<sigma>', \<sigma>')"
      by simp
  next
    fix l0 \<sigma>0 \<sigma>0' k
    assume J0: "S_J (l0,\<sigma>0)" and E: "env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0"
      and Q: "(\<lambda>(l0,\<sigma>0) (l,\<sigma>). Pr l0 l \<and> marked \<sigma> = marked \<sigma>0 \<and> hist_ok (l0,\<sigma>0) (l,\<sigma>) \<and> S_J (l,\<sigma>))
                (hC l0 \<sigma>0', \<sigma>0') k"
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from Q k PrL have a: "Pr l0 l" and m: "marked \<sigma> = marked \<sigma>0'" and H: "hist_ok (hC l0 \<sigma>0', \<sigma>0') (l,\<sigma>)"
      and J: "S_J (l,\<sigma>)" by simp_all
    have m0: "marked \<sigma>0' = marked \<sigma>0" by (rule S_J_marked[OF J0 E])
    have E': "envC (l0,\<sigma>0) (hC l0 \<sigma>0', \<sigma>0')" using E by (simp add: rely_C_def)
    have H0: "hist_ok (l0,\<sigma>0) (l,\<sigma>)" using hist_ok_env_left[OF E' H] by blast
    from a m m0 H0 J k
    show "(\<lambda>(l0,\<sigma>0) (l,\<sigma>). Pr l0 l \<and> marked \<sigma> = marked \<sigma>0 \<and> hist_ok (l0,\<sigma>0) (l,\<sigma>) \<and> S_J (l,\<sigma>)) (l0,\<sigma>0) k"
      by simp
  qed
next
  fix l \<sigma> l' \<sigma>' assume J: "S_J (l,\<sigma>)" and St: "r (l,\<sigma>) (l',\<sigma>')"
  from R[OF St] have \<sigma>': "\<sigma>' = \<sigma>" and fr: "s l' = s l" "checked l' = checked l" "mc l' = mc l" "Fv l' = Fv l"
    and a: "Pr l l'" by blast+
  have GS: "guar_Sweep \<sigma> \<sigma>" unfolding guar_Sweep_def by (simp add: map_le_refl)
  have G: "S_guar (l,\<sigma>) (l',\<sigma>')" using GS \<sigma>' fr unfolding S_guar_def by simp
  have H: "hist_ok (l,\<sigma>) (hC l' \<sigma>', \<sigma>')" using hist_ok_step[OF hist_ok_refl[of "(l,\<sigma>)"] fr(4), of \<sigma>'] by blast
  have J': "S_J (hC l' \<sigma>', \<sigma>')" using J \<sigma>' fr(1) unfolding S_J_def by simp
  from G a H J' \<sigma>' PrR
  show "S_guar (l,\<sigma>) (l',\<sigma>') \<and>
        (\<lambda>(l0,\<sigma>0) (l,\<sigma>). Pr l0 l \<and> marked \<sigma> = marked \<sigma>0 \<and> hist_ok (l0,\<sigma>0) (l,\<sigma>) \<and> S_J (l,\<sigma>))
          (l,\<sigma>) (hC l' \<sigma>', \<sigma>')"
    by simp
qed

subsection \<open>Add-to-free (Algorithm 20)\<close>

text \<open>Thesis: the specification of Add-to-free(x) (Section 4.8.3, Appendix C):
    pre  x \<notin> marked
    rely rely-Collector
    guar (as above)
    post x \<in> marked' \<and> x \<in> free' \<and> kids(x, hp') = {}
  In Isabelle:
    - the pre condition also states what holds in every state of Sweep
      (S_J).  Then invA(x, \<sigma>) holds in the first state (invA_init, Section
      4.8.4), and by Lemmas 17 and 18 "invA(x, \<sigma>) holds in every state of
      Add-to-free until x is added to free";
    - the guarantee A_guar is S_guar, with x and consid unchanged;
    - the post condition: x is marked, and free contained x at some point
      during Add-to-free, that is x \<in> f for some f in free~, the possible
      values of free (Section 2.3).  The thesis's x \<in> free' and
      kids(x, hp') = {} are not satisfied despite interference, since the
      Mutator may allocate x as soon as it is free; Section 4.8.3 makes this
      point for Sweep, whose post condition uses free~ for this reason.
      Also: Add-to-free marks only x, the history variable only records, and
      S_J still holds.\<close>

definition A_pre :: "('a,'i) cconf \<Rightarrow> bool" where
  "A_pre = (\<lambda>(l,\<sigma>). S_J (l,\<sigma>) \<and> x l \<notin> marked \<sigma>)"

definition A_guar :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "A_guar = (\<lambda>(l,\<sigma>) (l',\<sigma>'). S_guar (l,\<sigma>) (l',\<sigma>') \<and> x l' = x l \<and> consid l' = consid l)"

definition A_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "A_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). x l = x l0 \<and> consid l = consid l0 \<and>
                 marked \<sigma> = insert (x l0) (marked \<sigma>0) \<and> (\<exists>f\<in>pv (l0,\<sigma>0) (l,\<sigma>). x l0 \<in> f) \<and>
                 hist_ok (l0,\<sigma>0) (l,\<sigma>) \<and> S_J (l,\<sigma>))"

text \<open>Mechanisation only: invA(x, \<sigma>) makes x garbage, so interference does not
  change the pointers out of x (conjunct (4.1) of rely-Collector).\<close>

lemma invA_garbage: "invA y \<sigma> \<Longrightarrow> y \<in> garbage \<sigma>"
  unfolding invA_def garbage_def by blast

lemma invA_edges_env:
  assumes "invA y \<sigma>" and "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  shows "hp \<sigma>' (y,j) = hp \<sigma> (y,j)"
  by (rule envs_garbage_edges[OF assms(2) invA_garbage[OF assms(1)]])

text \<open>Thesis: what holds during Add-to-free(x) before x is added to free: S_J
  and invA(x, \<sigma>).  It holds despite interference (Lemmas 2, 15 and 17).\<close>

definition A_J :: "('a,'i) cconf \<Rightarrow> bool" where
  "A_J = (\<lambda>(l,\<sigma>). S_J (l,\<sigma>) \<and> invA (x l) \<sigma>)"

lemma A_J_stable: "stable hC (rely_C s) A_J"
proof (rule stableC)
  fix l \<sigma> \<sigma>' assume J: "A_J (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  from J have J1: "S_J (l,\<sigma>)" and A: "invA (x l) \<sigma>" unfolding A_J_def by simp_all
  have "S_J (hC l \<sigma>', \<sigma>')" by (rule stableD[OF S_J_stable J1]) (simp add: rely_C_def E)
  moreover have "invA (x l) \<sigma>'" by (rule envs_invA[OF E A])
  ultimately show "A_J (hC l \<sigma>', \<sigma>')" unfolding A_J_def by simp
qed

text \<open>Thesis: the loop of Algorithm 20, line 1, "for i \<in> Index do
  hp(x, i) \<leftarrow> null", written as a while-loop over cleared, the indices done
  so far.  Its invariant: A_J, and every pointer of x already cleared is
  null (it stays null despite interference, since x is garbage).  Its
  so-far: cleared grows, x is unchanged.\<close>

definition A_inv :: "('a,'i) cconf \<Rightarrow> bool" where
  "A_inv = (\<lambda>(l,\<sigma>). A_J (l,\<sigma>) \<and> (\<forall>j\<in>cleared l. hp \<sigma> (x l, j) = None))"

definition A_sofar :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "A_sofar = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). cleared l0 \<subset> cleared l \<and> x l = x l0)"

definition A_P0 :: "('a,'i) cconf \<Rightarrow> bool" where
  "A_P0 = (\<lambda>(l,\<sigma>). cleared l = {} \<and> A_J (l,\<sigma>))"

lemma A_inv_stable: "stable hC (rely_C s) A_inv"
proof (rule stableC)
  fix l \<sigma> \<sigma>' assume I: "A_inv (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  from I have J: "A_J (l,\<sigma>)" and N: "\<forall>j\<in>cleared l. hp \<sigma> (x l, j) = None" unfolding A_inv_def by simp_all
  from J have A: "invA (x l) \<sigma>" unfolding A_J_def by simp
  have "A_J (hC l \<sigma>', \<sigma>')" by (rule stableD[OF A_J_stable J]) (simp add: rely_C_def E)
  moreover have "\<forall>j\<in>cleared l. hp \<sigma>' (x l, j) = None" using N invA_edges_env[OF A E] by simp
  ultimately show "A_inv (hC l \<sigma>', \<sigma>')" unfolding A_inv_def by simp
qed

lemma A_sofar_tolerates: "tolerates hC (rely_C s) I A_sofar"
  by (rule toleratesC) (auto simp: A_sofar_def split_beta)

lemma A_sofar_trans: "A_sofar k0 k1 \<Longrightarrow> A_sofar k1 k2 \<Longrightarrow> A_sofar k0 k2"
  by (cases k0, cases k1, cases k2) (auto simp: A_sofar_def)

text \<open>Thesis: one iteration: let i \<in> (Index - cleared); hp(x, i) \<leftarrow> null;
  cleared \<leftarrow> cleared \<union> {i}.  The heap update is a step of Add-to-free(x)
  taken while invA(x, \<sigma>) holds; it keeps invA by Lemma 18.\<close>

definition A_pick_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "A_pick_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). i l \<notin> cleared l0 \<and> cleared l = cleared l0 \<and> x l = x l0 \<and> A_inv (l,\<sigma>))"

definition A_null_pre :: "('a,'i) cconf \<Rightarrow> bool" where
  "A_null_pre = (\<lambda>(l,\<sigma>). A_J (l,\<sigma>) \<and> (\<forall>j\<in>cleared l. hp \<sigma> (x l, j) = None))"

definition A_null_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "A_null_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). i l = i l0 \<and> cleared l = cleared l0 \<and> x l = x l0 \<and>
                     A_J (l,\<sigma>) \<and> (\<forall>j\<in>insert (i l) (cleared l). hp \<sigma> (x l, j) = None))"

definition A_add_pre :: "('a,'i) cconf \<Rightarrow> bool" where
  "A_add_pre = (\<lambda>(l,\<sigma>). A_J (l,\<sigma>) \<and> (\<forall>j\<in>insert (i l) (cleared l). hp \<sigma> (x l, j) = None))"

definition A_add_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "A_add_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). cleared l = insert (i l0) (cleared l0) \<and> x l = x l0 \<and> A_inv (l,\<sigma>))"

lemma A_pick_sat: "coll_sat A_inv A_pick A_guar A_pick_post"
  unfolding A_pick_def
proof (rule rule_basicC[OF A_inv_stable])
  show "tolerates hC (rely_C s) A_inv A_pick_post"
  proof (rule toleratesC)
    fix k0 l \<sigma> \<sigma>' assume Q: "A_pick_post k0 (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    from Q k0 have a: "i l \<notin> cleared l0" "cleared l = cleared l0" "x l = x l0" and I: "A_inv (l,\<sigma>)"
      unfolding A_pick_post_def by simp_all
    have "A_inv (hC l \<sigma>', \<sigma>')" by (rule stableD[OF A_inv_stable I]) (simp add: rely_C_def E)
    with a k0 show "A_pick_post k0 (hC l \<sigma>', \<sigma>')" unfolding A_pick_post_def by simp
  next
    fix l0 \<sigma>0 \<sigma>0' k assume Q: "A_pick_post (hC l0 \<sigma>0', \<sigma>0') k"
    then show "A_pick_post (l0,\<sigma>0) k" by (cases k) (simp add: A_pick_post_def)
  qed
next
  fix l \<sigma> l' \<sigma>' assume I: "A_inv (l,\<sigma>)"
    and St: "(\<lambda>(l,\<sigma>) (l',\<sigma>'). (\<exists>j. j \<notin> cleared l \<and> l' = l\<lparr>i := j\<rparr>) \<and> \<sigma>' = \<sigma>) (l,\<sigma>) (l',\<sigma>')"
  from St obtain j where j: "j \<notin> cleared l" and l': "l' = l\<lparr>i := j\<rparr>" and \<sigma>': "\<sigma>' = \<sigma>" by auto
  have GS: "guar_Sweep \<sigma> \<sigma>" unfolding guar_Sweep_def by (simp add: map_le_refl)
  have G: "A_guar (l,\<sigma>) (l',\<sigma>')" using GS l' \<sigma>' unfolding A_guar_def S_guar_def by simp
  have "A_inv (hC l' \<sigma>', \<sigma>')" using I l' \<sigma>' unfolding A_inv_def A_J_def S_J_def by simp
  with j l' have "A_pick_post (l,\<sigma>) (hC l' \<sigma>', \<sigma>')" unfolding A_pick_post_def by simp
  with G show "A_guar (l,\<sigma>) (l',\<sigma>') \<and> A_pick_post (l,\<sigma>) (hC l' \<sigma>', \<sigma>')" by blast
qed

lemma A_null_sat: "coll_sat A_null_pre (null_ptr :: ('a::finite,'i::finite) ccom) A_guar A_null_post"
  unfolding null_ptr_def
proof (rule rule_basicC)
  show "stable hC (rely_C s) (A_null_pre :: ('a,'i) cconf \<Rightarrow> bool)"
    using A_inv_stable unfolding A_inv_def A_null_pre_def .
  show "tolerates hC (rely_C s) A_null_pre (A_null_post :: ('a,'i) cconf \<Rightarrow> _)"
  proof (rule toleratesC)
    fix k0 l and \<sigma> \<sigma>' :: "('a,'i) state"
    assume Q: "A_null_post k0 (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    note QQ = Q[unfolded k0 A_null_post_def prod.case]
    have a1: "i l = i l0" by (rule QQ[THEN conjunct1])
    have a2: "cleared l = cleared l0" by (rule QQ[THEN conjunct2, THEN conjunct1])
    have a3: "x l = x l0" by (rule QQ[THEN conjunct2, THEN conjunct2, THEN conjunct1])
    have J: "A_J (l,\<sigma>)" by (rule QQ[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1])
    have N: "\<forall>j\<in>insert (i l) (cleared l). hp \<sigma> (x l, j) = None" by (rule QQ[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2])
    note a = a1 a2 a3
    from J have A: "invA (x l) \<sigma>" unfolding A_J_def by simp
    have "A_J (hC l \<sigma>', \<sigma>')" by (rule stableD[OF A_J_stable J]) (simp add: rely_C_def E)
    moreover have "\<forall>j\<in>insert (i l) (cleared l). hp \<sigma>' (x l, j) = None"
      using N invA_edges_env[OF A E] by simp
    ultimately show "A_null_post k0 (hC l \<sigma>', \<sigma>')" using a k0 unfolding A_null_post_def by simp
  next
    fix l0 \<sigma>0 \<sigma>0' k assume Q: "A_null_post (hC l0 \<sigma>0', \<sigma>0') k"
    then show "A_null_post (l0,\<sigma>0) k" by (cases k) (simp (no_asm_use) add: A_null_post_def)
  qed
next
  fix l and \<sigma> :: "('a,'i) state" and l' \<sigma>'
  assume P: "A_null_pre (l,\<sigma>)"
    and St: "(\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l \<and> \<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((x l, i l) := None)\<rparr>) (l,\<sigma>) (l',\<sigma>')"
  from St have l': "l' = l" and \<sigma>': "\<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((x l, i l) := None)\<rparr>" by simp_all
  from P have inv: "inv_state \<sigma>" and IS: "inv_safe \<sigma>" and s0: "s l = {}" and A: "invA (x l) \<sigma>"
    and N: "\<forall>j\<in>cleared l. hp \<sigma> (x l, j) = None"
    unfolding A_null_pre_def A_J_def S_J_def by simp_all
  have HL: "hp \<sigma>' \<subseteq>\<^sub>m hp \<sigma>" using \<sigma>' by (simp add: map_le_del)
  have GS: "guar_Sweep \<sigma> \<sigma>'" using \<sigma>' HL unfolding guar_Sweep_def by simp
  have GA: "guar_AddToFree (x l) \<sigma> \<sigma>'"
    using \<sigma>' HL unfolding guar_AddToFree_def by (auto simp: domIff split: if_splits)
  have inv': "inv_state \<sigma>'" using inv_state_del[OF inv] \<sigma>' by simp
  have G: "A_guar (l,\<sigma>) (l',\<sigma>')" using GS GA A inv' l' \<sigma>' unfolding A_guar_def S_guar_def by simp
  have IS': "inv_safe \<sigma>'" by (rule lemma16_prog_inv_safe[OF GS IS])
  have A': "invA (x l) \<sigma>'" by (rule lemma18_prog_invA[OF GA _ A]) (simp add: \<sigma>')
  have N': "\<forall>j\<in>insert (i l) (cleared l). hp \<sigma>' (x l, j) = None" using N \<sigma>' by simp
  have "A_null_post (l,\<sigma>) (hC l' \<sigma>', \<sigma>')"
    using inv' IS' s0 A' N' l' unfolding A_null_post_def A_J_def S_J_def by simp
  with G show "A_guar (l,\<sigma>) (l',\<sigma>') \<and> A_null_post (l,\<sigma>) (hC l' \<sigma>', \<sigma>')" by blast
qed

lemma A_add_sat: "coll_sat A_add_pre cleared_add A_guar A_add_post"
  unfolding cleared_add_def
proof (rule rule_basicC)
  show "stable hC (rely_C s) A_add_pre"
  proof (rule stableC)
    fix l \<sigma> \<sigma>' assume P: "A_add_pre (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    from P have J: "A_J (l,\<sigma>)" and N: "\<forall>j\<in>insert (i l) (cleared l). hp \<sigma> (x l, j) = None"
      unfolding A_add_pre_def by simp_all
    from J have A: "invA (x l) \<sigma>" unfolding A_J_def by simp
    have "A_J (hC l \<sigma>', \<sigma>')" by (rule stableD[OF A_J_stable J]) (simp add: rely_C_def E)
    moreover have "\<forall>j\<in>insert (i l) (cleared l). hp \<sigma>' (x l, j) = None"
      using N invA_edges_env[OF A E] by simp
    ultimately show "A_add_pre (hC l \<sigma>', \<sigma>')" unfolding A_add_pre_def by simp
  qed
  show "tolerates hC (rely_C s) A_add_pre A_add_post"
  proof (rule toleratesC)
    fix k0 l \<sigma> \<sigma>' assume Q: "A_add_post k0 (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    from Q k0 have a: "cleared l = insert (i l0) (cleared l0)" "x l = x l0" and I: "A_inv (l,\<sigma>)"
      unfolding A_add_post_def by simp_all
    have "A_inv (hC l \<sigma>', \<sigma>')" by (rule stableD[OF A_inv_stable I]) (simp add: rely_C_def E)
    with a k0 show "A_add_post k0 (hC l \<sigma>', \<sigma>')" unfolding A_add_post_def by simp
  next
    fix l0 \<sigma>0 \<sigma>0' k assume Q: "A_add_post (hC l0 \<sigma>0', \<sigma>0') k"
    then show "A_add_post (l0,\<sigma>0) k" by (cases k) (simp add: A_add_post_def)
  qed
next
  fix l \<sigma> l' \<sigma>' assume P: "A_add_pre (l,\<sigma>)"
    and St: "(\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l\<lparr>cleared := cleared l \<union> {i l}\<rparr> \<and> \<sigma>' = \<sigma>) (l,\<sigma>) (l',\<sigma>')"
  from St have l': "l' = l\<lparr>cleared := cleared l \<union> {i l}\<rparr>" and \<sigma>': "\<sigma>' = \<sigma>" by simp_all
  have GS: "guar_Sweep \<sigma> \<sigma>" unfolding guar_Sweep_def by (simp add: map_le_refl)
  have G: "A_guar (l,\<sigma>) (l',\<sigma>')" using GS l' \<sigma>' unfolding A_guar_def S_guar_def by simp
  have "A_inv (hC l' \<sigma>', \<sigma>')" using P l' \<sigma>' unfolding A_add_pre_def A_inv_def A_J_def S_J_def by simp
  with l' have "A_add_post (l,\<sigma>) (hC l' \<sigma>', \<sigma>')" unfolding A_add_post_def by simp
  with G show "A_guar (l,\<sigma>) (l',\<sigma>') \<and> A_add_post (l,\<sigma>) (hC l' \<sigma>', \<sigma>')" by blast
qed

text \<open>Mechanisation only: the post condition of each statement of the body gives
  the pre condition of the next.\<close>

lemma A_pick_post_null_pre:
  assumes "A_pick_post k0 k"
  shows "A_null_pre k"
proof -
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  note QQ = assms[unfolded k0 k A_pick_post_def prod.case]
  have "A_inv (l,\<sigma>)" by (rule QQ[THEN conjunct2, THEN conjunct2, THEN conjunct2])
  then show ?thesis using k unfolding A_inv_def A_null_pre_def by simp
qed

lemma A_null_post_add_pre:
  assumes "A_null_post k0 k"
  shows "A_add_pre k"
proof -
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  note QQ = assms[unfolded k0 k A_null_post_def prod.case]
  have J: "A_J (l,\<sigma>)" by (rule QQ[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1])
  have N: "\<forall>j\<in>insert (i l) (cleared l). hp \<sigma> (x l, j) = None"
    by (rule QQ[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2])
  from J N k show ?thesis unfolding A_add_pre_def by simp
qed

lemma A_body_sat:
  "coll_sat (\<lambda>k. A_inv k \<and> A_test k) (A_body :: ('a::finite,'i::finite) ccom) A_guar
            (\<lambda>k0 k. A_inv k \<and> A_sofar k0 k)"
proof -
  have "coll_sat A_null_pre (Seq null_ptr cleared_add :: ('a,'i) ccom) A_guar
          (seq_post A_null_post A_add_post)"
    by (rule rule_seq[OF A_null_sat A_add_sat]) (erule A_null_post_add_pre)
  then have V: "coll_sat A_inv (A_body :: ('a,'i) ccom) A_guar
                  (seq_post A_pick_post (seq_post A_null_post A_add_post))"
    unfolding A_body_def
    by (rule rule_seq[OF A_pick_sat]) (erule A_pick_post_null_pre)
  have Q: "A_inv k \<and> A_sofar k0 k"
    if "A_inv k0 \<and> A_test k0" and "seq_post A_pick_post (seq_post A_null_post A_add_post) k0 k"
    for k0 k :: "('a,'i) cconf"
  proof -
    from that(2) obtain k1 k2 where 1: "A_pick_post k0 k1" and 2: "A_null_post k1 k2"
      and 3: "A_add_post k2 k"
      unfolding seq_post_def by blast
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
    obtain l2 \<sigma>2 where k2: "k2 = (l2,\<sigma>2)" by (cases k2)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from 1 k0 k1 have a: "i l1 \<notin> cleared l0" "cleared l1 = cleared l0" "x l1 = x l0"
      unfolding A_pick_post_def by simp_all
    from 2 k1 k2 have b: "i l2 = i l1" "cleared l2 = cleared l1" "x l2 = x l1"
      unfolding A_null_post_def by simp_all
    from 3 k2 k have c: "cleared l = insert (i l2) (cleared l2)" "x l = x l2" and I: "A_inv (l,\<sigma>)"
      unfolding A_add_post_def by simp_all
    have "cleared l0 \<subset> cleared l" using a b c by auto
    moreover have "x l = x l0" using a b c by simp
    ultimately show ?thesis using I k0 k unfolding A_sofar_def by simp
  qed
  show ?thesis by (rule rule_weaken[OF V _ _ Q]) (simp_all add: A_inv_def)
qed

text \<open>Thesis: when the loop exits, cleared = Index: every pointer of x is null,
  so kids(x, hp') = {}; this holds despite interference since x is garbage.\<close>

definition A_loop_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "A_loop_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). x l = x l0 \<and> A_J (l,\<sigma>) \<and> (\<forall>j. hp \<sigma> (x l, j) = None))"

lemma A_loop_sat:
  "coll_sat A_P0 (While A_test (A_body :: ('a::finite,'i::finite) ccom)) A_guar A_loop_post"
proof (rule rule_while[where I = A_inv and sofar = A_sofar,
                       OF _ A_body_sat A_inv_stable _ A_sofar_trans A_sofar_tolerates])
  fix k :: "('a,'i) cconf" assume "A_P0 k"
  then show "A_inv k" by (cases k) (simp add: A_P0_def A_inv_def)
next
  fix k :: "('a,'i) cconf"
  show "A_test (hupd hC k) = A_test k" by (cases k) (simp add: A_test_def)
next
  fix k0 k :: "('a,'i) cconf"
  assume P0: "A_P0 k0" and I: "A_inv k" and T: "\<not> A_test k" and W: "A_sofar k0 k \<or> envC\<^sup>*\<^sup>* k0 k"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  from P0 k0 have c0: "cleared l0 = {}" by (simp add: A_P0_def)
  from T k have c: "cleared l = UNIV" by (simp add: A_test_def)
  from I[unfolded k A_inv_def prod.case] have J: "A_J (l,\<sigma>)"
    and N0: "\<forall>j\<in>cleared l. hp \<sigma> (x l, j) = None" by blast+
  from N0 have N: "\<forall>j. hp \<sigma> (x l, j) = None" by (simp add: c)
  have "x l = x l0" using W
  proof
    assume "A_sofar k0 k"
    then show ?thesis using k0 k by (simp add: A_sofar_def)
  next
    assume "envC\<^sup>*\<^sup>* k0 k"
    then have "envC\<^sup>*\<^sup>* (l0,\<sigma>0) (l,\<sigma>)" using k0 k by simp
    from envC_star_sel(5)[OF this] show ?thesis .
  qed
  with J N k0 k show "A_loop_post k0 k" unfolding A_loop_post_def by simp
next
  fix k0 k k' :: "('a,'i) cconf"
  assume Q: "A_loop_post k0 k" and E: "envC k k'"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
  from E k k' have l': "l' = hC l \<sigma>'" and E': "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    by (simp_all add: rely_C_def)
  note QQ = Q[unfolded k0 k A_loop_post_def prod.case]
  have a: "x l = x l0" by (rule QQ[THEN conjunct1])
  have J: "A_J (l,\<sigma>)" by (rule QQ[THEN conjunct2, THEN conjunct1])
  have N: "\<forall>j. hp \<sigma> (x l, j) = None" by (rule QQ[THEN conjunct2, THEN conjunct2])
  from J have A: "invA (x l) \<sigma>" unfolding A_J_def by simp
  have "A_J (hC l \<sigma>', \<sigma>')" by (rule stableD[OF A_J_stable J]) (simp add: rely_C_def E')
  moreover have "\<forall>j. hp \<sigma>' (x l, j) = None" using N invA_edges_env[OF A E'] by simp
  ultimately show "A_loop_post k0 k'" using a k0 k' l' unfolding A_loop_post_def by simp
qed

text \<open>Thesis: the start of the loop: cleared \<leftarrow> {}.  invA(x, \<sigma>) holds at the
  start of Add-to-free (invA_init: x \<notin> marked, with inv-safe and inv-\<Sigma>).\<close>

definition A_reset_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "A_reset_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). cleared l = {} \<and> x l = x l0 \<and> A_J (l,\<sigma>))"

lemma A_reset_sat: "coll_sat A_pre cleared_reset A_guar A_reset_post"
  unfolding cleared_reset_def
proof (rule rule_basicC)
  show "stable hC (rely_C s) A_pre"
  proof (rule stableC)
    fix l \<sigma> \<sigma>' assume P: "A_pre (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    from P have J: "S_J (l,\<sigma>)" and xm: "x l \<notin> marked \<sigma>" unfolding A_pre_def by simp_all
    have "S_J (hC l \<sigma>', \<sigma>')" by (rule stableD[OF S_J_stable J]) (simp add: rely_C_def E)
    moreover have "marked \<sigma>' = marked \<sigma>" by (rule S_J_marked[OF J E])
    ultimately show "A_pre (hC l \<sigma>', \<sigma>')" using xm unfolding A_pre_def by simp
  qed
  show "tolerates hC (rely_C s) A_pre A_reset_post"
  proof (rule toleratesC)
    fix k0 l \<sigma> \<sigma>' assume Q: "A_reset_post k0 (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    from Q k0 have a: "cleared l = {}" "x l = x l0" and J: "A_J (l,\<sigma>)"
      unfolding A_reset_post_def by simp_all
    have "A_J (hC l \<sigma>', \<sigma>')" by (rule stableD[OF A_J_stable J]) (simp add: rely_C_def E)
    with a k0 show "A_reset_post k0 (hC l \<sigma>', \<sigma>')" unfolding A_reset_post_def by simp
  next
    fix l0 \<sigma>0 \<sigma>0' k assume Q: "A_reset_post (hC l0 \<sigma>0', \<sigma>0') k"
    then show "A_reset_post (l0,\<sigma>0) k" by (cases k) (simp add: A_reset_post_def)
  qed
next
  fix l \<sigma> l' \<sigma>' assume P: "A_pre (l,\<sigma>)"
    and St: "(\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l\<lparr>cleared := {}\<rparr> \<and> \<sigma>' = \<sigma>) (l,\<sigma>) (l',\<sigma>')"
  from St have l': "l' = l\<lparr>cleared := {}\<rparr>" and \<sigma>': "\<sigma>' = \<sigma>" by simp_all
  from P have J: "S_J (l,\<sigma>)" and xm: "x l \<notin> marked \<sigma>" unfolding A_pre_def by simp_all
  from J have inv: "inv_state \<sigma>" and IS: "inv_safe \<sigma>" unfolding S_J_def by simp_all
  have A: "invA (x l) \<sigma>" by (rule invA_init[OF inv IS xm])
  have GS: "guar_Sweep \<sigma> \<sigma>" unfolding guar_Sweep_def by (simp add: map_le_refl)
  have G: "A_guar (l,\<sigma>) (l',\<sigma>')" using GS l' \<sigma>' unfolding A_guar_def S_guar_def by simp
  have "A_J (hC l' \<sigma>', \<sigma>')" using J A l' \<sigma>' unfolding A_J_def S_J_def by simp
  with l' have "A_reset_post (l,\<sigma>) (hC l' \<sigma>', \<sigma>')" unfolding A_reset_post_def by simp
  with G show "A_guar (l,\<sigma>) (l',\<sigma>') \<and> A_reset_post (l,\<sigma>) (hC l' \<sigma>', \<sigma>')" by blast
qed

text \<open>Mechanisation only: what Add-to-free does across all its steps: x and
  consid stay the same, it marks only x, and the history variable only
  records.  With inv-safe, interference marks nothing (Lemma 15).\<close>

definition A_trace :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "A_trace = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). x l = x l0 \<and> consid l = consid l0 \<and> marked \<sigma>0 \<subseteq> marked \<sigma> \<and>
                  marked \<sigma> \<subseteq> insert (x l0) (marked \<sigma>0) \<and> inv_safe \<sigma> \<and> hist_ok (l0,\<sigma>0) (l,\<sigma>))"

lemma A_trace_env:
  assumes T: "A_trace k0 k" and E: "envC k k'"
  shows "A_trace k0 k'"
proof -
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
  from E k k' have l': "l' = hC l \<sigma>'" and E': "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    by (simp_all add: rely_C_def)
  from T k0 k have a: "x l = x l0" "consid l = consid l0" "marked \<sigma>0 \<subseteq> marked \<sigma>"
    "marked \<sigma> \<subseteq> insert (x l0) (marked \<sigma>0)" and IS: "inv_safe \<sigma>" and H: "hist_ok (l0,\<sigma>0) (l,\<sigma>)"
    unfolding A_trace_def by simp_all
  from envs_inv_safe[OF E' IS] have IS': "inv_safe \<sigma>'" and m: "marked \<sigma>' = marked \<sigma>" by blast+
  have H': "hist_ok (l0,\<sigma>0) (l',\<sigma>')" using hist_ok_env[OF H] E k k' by blast
  from a IS' m H' l' k0 k' show ?thesis unfolding A_trace_def by simp
qed

lemma A_trace_guar:
  assumes T: "A_trace k0 k" and G: "A_guar k k'"
  shows "A_trace k0 (hupd hC k')"
proof -
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
  from T k0 k have a: "x l = x l0" "consid l = consid l0" "marked \<sigma>0 \<subseteq> marked \<sigma>"
    "marked \<sigma> \<subseteq> insert (x l0) (marked \<sigma>0)" and IS: "inv_safe \<sigma>" and H: "hist_ok (l0,\<sigma>0) (l,\<sigma>)"
    unfolding A_trace_def by simp_all
  from G k k' have GS: "guar_Sweep \<sigma> \<sigma>'" and m: "marked \<sigma>' - marked \<sigma> \<subseteq> {x l}"
    and b: "x l' = x l" "consid l' = consid l" and F: "Fv l' = Fv l"
    unfolding A_guar_def S_guar_def by simp_all
  from GS have mm: "marked \<sigma> \<subseteq> marked \<sigma>'" unfolding guar_Sweep_def by simp
  have IS': "inv_safe \<sigma>'" by (rule lemma16_prog_inv_safe[OF GS IS])
  have H': "hist_ok (l0,\<sigma>0) (hC l' \<sigma>', \<sigma>')" using hist_ok_step[OF H F] by blast
  have "marked \<sigma>' \<subseteq> insert (x l0) (marked \<sigma>0)" using a(1) a(4) m by auto
  with a b mm IS' H' k0 k' show ?thesis unfolding A_trace_def by auto
qed

text \<open>Thesis: lines 3 and 4 of Algorithm 20: marked \<leftarrow> marked \<union> {x}, then
  free \<leftarrow> free \<union> {x}.  "A node is also added to marked before it is added to
  free in order to satisfy free \<subseteq> marked."  The step adding x to free is a
  step of Add-to-free(x) taken while invA(x, \<sigma>) holds; it keeps inv-\<Sigma>
  because x is marked, has no pointers, and is not reachable.\<close>

definition A_mark_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "A_mark_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). x l = x l0 \<and> A_J (l,\<sigma>) \<and> (\<forall>j. hp \<sigma> (x l, j) = None) \<and>
                     x l \<in> marked \<sigma>)"

lemma inv_state_add_free:
  fixes \<sigma> :: "('a,'i) state"
  assumes inv: "inv_state \<sigma>" and m: "y \<in> marked \<sigma>" and e: "\<forall>j. hp \<sigma> (y,j) = None"
    and r: "y \<notin> reach (roots \<sigma>) (hp \<sigma>)"
  shows "inv_state (\<sigma>\<lparr>free := free \<sigma> \<union> {y}\<rparr>)"
proof -
  have eq: "(free \<sigma> \<union> {y}) \<inter> reach (roots \<sigma>) (hp \<sigma>) = free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>)"
    using r by blast
  from inv have A: "free \<sigma> \<union> roots \<sigma> \<subseteq> marked \<sigma>"
    and B: "card (free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>)) \<le> 1"
    and C: "\<forall>a\<in>free \<sigma>. \<forall>i. (a,i) \<notin> dom (hp \<sigma>)" unfolding inv_state_def by simp_all
  have "(free \<sigma> \<union> {y}) \<union> roots \<sigma> \<subseteq> marked \<sigma>" using A m by blast
  moreover have "card ((free \<sigma> \<union> {y}) \<inter> reach (roots \<sigma>) (hp \<sigma>)) \<le> 1" using B eq by simp
  moreover have "\<forall>a\<in>free \<sigma> \<union> {y}. \<forall>i. (a,i) \<notin> dom (hp \<sigma>)" using C e by (auto simp: domIff)
  ultimately show ?thesis unfolding inv_state_def by simp
qed

text \<open>Thesis: Add-to-free(x) meets its specification.  By Lemmas 17 and 18,
  invA(x, \<sigma>) holds until x is added to free, so every heap update and the
  step adding x to free are steps of Add-to-free(x) with invA(x, \<sigma>), as
  Theorem 6 requires.\<close>

theorem AddToFree_sat: "coll_sat A_pre (AddToFree :: ('a::finite,'i::finite) ccom) A_guar A_post"
proof -
  have L: "coll_sat A_pre (Seq cleared_reset (While A_test A_body) :: ('a,'i) ccom) A_guar
             (seq_post A_reset_post A_loop_post)"
    by (rule rule_seq[OF A_reset_sat A_loop_sat]) (auto simp: A_reset_post_def A_P0_def split_beta)
  have L': "coll_sat A_pre (Seq cleared_reset (While A_test A_body) :: ('a,'i) ccom) A_guar
              (\<lambda>k0 k. x (fst k) = x (fst k0) \<and> A_J k \<and> (\<forall>j. hp (snd k) (x (fst k), j) = None))"
  proof (rule rule_weaken[OF L])
    fix k0 k :: "('a,'i) cconf" assume "seq_post A_reset_post A_loop_post k0 k"
    then obtain k1 where 1: "A_reset_post k0 k1" and 2: "A_loop_post k1 k" unfolding seq_post_def by blast
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    note R1 = 1[unfolded k0 k1 A_reset_post_def prod.case]
    note R2 = 2[unfolded k1 k A_loop_post_def prod.case]
    have e1: "x l1 = x l0" by (rule R1[THEN conjunct2, THEN conjunct1])
    have e2: "x l = x l1" by (rule R2[THEN conjunct1])
    have J: "A_J (l,\<sigma>)" by (rule R2[THEN conjunct2, THEN conjunct1])
    have N: "\<forall>j. hp \<sigma> (x l, j) = None" by (rule R2[THEN conjunct2, THEN conjunct2])
    from e1 e2 J N k0 k show "x (fst k) = x (fst k0) \<and> A_J k \<and> (\<forall>j. hp (snd k) (x (fst k), j) = None)"
      by simp
  qed simp_all
  have M: "coll_sat A_pre (Seq (Seq cleared_reset (While A_test A_body)) mark_x :: ('a,'i) ccom) A_guar
             A_mark_post"
    unfolding mark_x_def
  proof (rule rule_seq_basic[OF L'])
    fix k0 k k' :: "('a,'i) cconf"
    assume Q: "x (fst k) = x (fst k0) \<and> A_J k \<and> (\<forall>j. hp (snd k) (x (fst k), j) = None)" and E: "envC k k'"
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from E k k' have l': "l' = hC l \<sigma>'" and E': "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
      by (simp_all add: rely_C_def)
    note QQ = Q[unfolded k fst_conv snd_conv]
    have a: "x l = x (fst k0)" by (rule QQ[THEN conjunct1])
    have J: "A_J (l,\<sigma>)" by (rule QQ[THEN conjunct2, THEN conjunct1])
    have N: "\<forall>j. hp \<sigma> (x l, j) = None" by (rule QQ[THEN conjunct2, THEN conjunct2])
    from J have A: "invA (x l) \<sigma>" unfolding A_J_def by simp
    have "A_J (hC l \<sigma>', \<sigma>')" by (rule stableD[OF A_J_stable J]) (simp add: rely_C_def E')
    moreover have "\<forall>j. hp \<sigma>' (x l, j) = None" using N invA_edges_env[OF A E'] by simp
    ultimately show "x (fst k') = x (fst k0) \<and> A_J k' \<and> (\<forall>j. hp (snd k') (x (fst k'), j) = None)"
      using a k' l' by simp
  next
    fix k0 k k' :: "('a,'i) cconf"
    assume Q: "x (fst k) = x (fst k0) \<and> A_J k \<and> (\<forall>j. hp (snd k) (x (fst k), j) = None)"
      and St: "(\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l \<and> \<sigma>' = \<sigma>\<lparr>marked := marked \<sigma> \<union> {x l}\<rparr>) k k'"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from St k k' have l': "l' = l" and \<sigma>': "\<sigma>' = \<sigma>\<lparr>marked := marked \<sigma> \<union> {x l}\<rparr>" by simp_all
    note QQ = Q[unfolded k k0 fst_conv snd_conv]
    have a: "x l = x l0" by (rule QQ[THEN conjunct1])
    have J: "A_J (l,\<sigma>)" by (rule QQ[THEN conjunct2, THEN conjunct1])
    have N: "\<forall>j. hp \<sigma> (x l, j) = None" by (rule QQ[THEN conjunct2, THEN conjunct2])
    from J have inv: "inv_state \<sigma>" and IS: "inv_safe \<sigma>" and s0: "s l = {}" and A: "invA (x l) \<sigma>"
      unfolding A_J_def S_J_def by simp_all
    have GS: "guar_Sweep \<sigma> \<sigma>'" using \<sigma>' unfolding guar_Sweep_def by (auto simp: map_le_refl)
    have inv': "inv_state \<sigma>'" using inv_state_mark[OF inv, of "{x l}"] \<sigma>' by simp
    have G: "A_guar k k'" using GS inv' k k' l' \<sigma>' unfolding A_guar_def S_guar_def by auto
    have IS': "inv_safe \<sigma>'" by (rule lemma16_prog_inv_safe[OF GS IS])
    have A': "invA (x l) \<sigma>'" using A \<sigma>' unfolding invA_def by simp
    have "A_mark_post k0 (hupd hC k')"
      using a inv' IS' s0 A' N l' \<sigma>' k0 k' unfolding A_mark_post_def A_J_def S_J_def by simp
    with G show "A_guar k k' \<and> A_mark_post k0 (hupd hC k')" by blast
  next
    fix k0 k k' :: "('a,'i) cconf"
    assume Q: "A_mark_post k0 k" and E: "envC k k'"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from E k k' have l': "l' = hC l \<sigma>'" and E': "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
      by (simp_all add: rely_C_def)
    note QQ = Q[unfolded k0 k A_mark_post_def prod.case]
    have a: "x l = x l0" by (rule QQ[THEN conjunct1])
    have J: "A_J (l,\<sigma>)" by (rule QQ[THEN conjunct2, THEN conjunct1])
    have N: "\<forall>j. hp \<sigma> (x l, j) = None" by (rule QQ[THEN conjunct2, THEN conjunct2, THEN conjunct1])
    have xm: "x l \<in> marked \<sigma>" by (rule QQ[THEN conjunct2, THEN conjunct2, THEN conjunct2])
    from J have A: "invA (x l) \<sigma>" unfolding A_J_def by simp
    have "A_J (hC l \<sigma>', \<sigma>')" by (rule stableD[OF A_J_stable J]) (simp add: rely_C_def E')
    moreover have "\<forall>j. hp \<sigma>' (x l, j) = None" using N invA_edges_env[OF A E'] by simp
    moreover have "x l \<in> marked \<sigma>'" using xm envs_marked[OF E'] by blast
    ultimately show "A_mark_post k0 k'" using a k0 k' l' unfolding A_mark_post_def by simp
  qed
  have T: "coll_sat A_pre (Seq (Seq cleared_reset (While A_test A_body)) mark_x :: ('a,'i) ccom) A_guar
             (\<lambda>k0 k. A_mark_post k0 k \<and> A_trace k0 k)"
  proof (rule rule_trace_h[OF M])
    fix k :: "('a,'i) cconf" assume "A_pre k"
    then show "A_trace k k" by (cases k) (auto simp add: A_pre_def S_J_def A_trace_def hist_ok_refl)
  next
    fix k0 k k' :: "('a,'i) cconf" assume "A_trace k0 k" and "envC k k'"
    then show "A_trace k0 k'" by (rule A_trace_env)
  next
    fix k0 k k' :: "('a,'i) cconf" assume "A_trace k0 k" and "A_guar k k'"
    then show "A_trace k0 (hupd hC k')" by (rule A_trace_guar)
  qed
  show ?thesis
    unfolding AddToFree_def free_x_def
  proof (rule rule_seq_basic[OF T])
    fix k0 k k' :: "('a,'i) cconf"
    assume Q: "A_mark_post k0 k \<and> A_trace k0 k" and E: "envC k k'"
    show "A_mark_post k0 k' \<and> A_trace k0 k'"
    proof (intro conjI)
      obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
      obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
      obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
      from E k k' have l': "l' = hC l \<sigma>'" and E': "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
        by (simp_all add: rely_C_def)
      note QQ = Q[unfolded k0 k A_mark_post_def prod.case]
      have a: "x l = x l0" by (rule QQ[THEN conjunct1, THEN conjunct1])
      have J: "A_J (l,\<sigma>)" by (rule QQ[THEN conjunct1, THEN conjunct2, THEN conjunct1])
      have N: "\<forall>j. hp \<sigma> (x l, j) = None" by (rule QQ[THEN conjunct1, THEN conjunct2, THEN conjunct2, THEN conjunct1])
      have xm: "x l \<in> marked \<sigma>" by (rule QQ[THEN conjunct1, THEN conjunct2, THEN conjunct2, THEN conjunct2])
      from J have A: "invA (x l) \<sigma>" unfolding A_J_def by simp
      have "A_J (hC l \<sigma>', \<sigma>')" by (rule stableD[OF A_J_stable J]) (simp add: rely_C_def E')
      moreover have "\<forall>j. hp \<sigma>' (x l, j) = None" using N invA_edges_env[OF A E'] by simp
      moreover have "x l \<in> marked \<sigma>'" using xm envs_marked[OF E'] by blast
      ultimately show "A_mark_post k0 k'" using a k0 k' l' unfolding A_mark_post_def by simp
      from Q have "A_trace k0 k" by blast
      from A_trace_env[OF this E] show "A_trace k0 k'" .
    qed
  next
    fix k0 k k' :: "('a,'i) cconf"
    assume Q: "A_mark_post k0 k \<and> A_trace k0 k"
      and St: "(\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l \<and> \<sigma>' = \<sigma>\<lparr>free := free \<sigma> \<union> {x l}\<rparr>) k k'"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from St k k' have l': "l' = l" and \<sigma>': "\<sigma>' = \<sigma>\<lparr>free := free \<sigma> \<union> {x l}\<rparr>" by simp_all
    note QQ = Q[unfolded k0 k A_mark_post_def prod.case]
    have a: "x l = x l0" by (rule QQ[THEN conjunct1, THEN conjunct1])
    have J: "A_J (l,\<sigma>)" by (rule QQ[THEN conjunct1, THEN conjunct2, THEN conjunct1])
    have N: "\<forall>j. hp \<sigma> (x l, j) = None" by (rule QQ[THEN conjunct1, THEN conjunct2, THEN conjunct2, THEN conjunct1])
    have xm: "x l \<in> marked \<sigma>" by (rule QQ[THEN conjunct1, THEN conjunct2, THEN conjunct2, THEN conjunct2])
    from Q k0 k have c: "consid l = consid l0" and m0: "marked \<sigma>0 \<subseteq> marked \<sigma>"
      and m1: "marked \<sigma> \<subseteq> insert (x l0) (marked \<sigma>0)" and H: "hist_ok (l0,\<sigma>0) (l,\<sigma>)"
      unfolding A_trace_def by simp_all
    from J have inv: "inv_state \<sigma>" and IS: "inv_safe \<sigma>" and s0: "s l = {}" and A: "invA (x l) \<sigma>"
      unfolding A_J_def S_J_def by simp_all
    from A have xr: "x l \<notin> reach (roots \<sigma>) (hp \<sigma>)" unfolding invA_def by simp
    have inv': "inv_state \<sigma>'" using inv_state_add_free[OF inv xm N xr] \<sigma>' by simp
    have GS: "guar_Sweep \<sigma> \<sigma>'" using \<sigma>' unfolding guar_Sweep_def by (auto simp: map_le_refl)
    have GA: "guar_AddToFree (x l) \<sigma> \<sigma>'" using \<sigma>' unfolding guar_AddToFree_def by (auto simp: map_le_refl)
    have G: "A_guar k k'" using GS GA A inv' k k' l' \<sigma>' unfolding A_guar_def S_guar_def by auto
    have IS': "inv_safe \<sigma>'" using IS \<sigma>' unfolding inv_safe_def by simp
    have H': "hist_ok (l0,\<sigma>0) (hC l' \<sigma>', \<sigma>') \<and> free \<sigma>' \<in> pv (l0,\<sigma>0) (hC l' \<sigma>', \<sigma>')"
      using hist_ok_step[OF H, where l' = l' and \<sigma>' = \<sigma>'] l' by simp
    have xf: "x l0 \<in> free \<sigma>'" using \<sigma>' a by simp
    have "marked \<sigma>' = insert (x l0) (marked \<sigma>0)" using m0 m1 xm a \<sigma>' by auto
    then have "A_post k0 (hupd hC k')"
      using a c xf H' inv' IS' s0 l' \<sigma>' k0 k' unfolding A_post_def S_J_def by auto
    with G show "A_guar k k' \<and> A_post k0 (hupd hC k')" by blast
  next
    fix k0 k k' :: "('a,'i) cconf"
    assume Q: "A_post k0 k" and E: "envC k k'"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
    from E k k' have l': "l' = hC l \<sigma>'" and E': "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
      by (simp_all add: rely_C_def)
    from Q k0 k have a: "x l = x l0" "consid l = consid l0" "marked \<sigma> = insert (x l0) (marked \<sigma>0)"
      and F: "\<exists>f\<in>pv (l0,\<sigma>0) (l,\<sigma>). x l0 \<in> f" and H: "hist_ok (l0,\<sigma>0) (l,\<sigma>)" and J: "S_J (l,\<sigma>)"
      unfolding A_post_def by simp_all
    have m: "marked \<sigma>' = marked \<sigma>" by (rule S_J_marked[OF J E'])
    from hist_ok_env[OF H] E k k' have H': "hist_ok (l0,\<sigma>0) (l',\<sigma>')"
      and P: "pv (l0,\<sigma>0) (l,\<sigma>) \<subseteq> pv (l0,\<sigma>0) (l',\<sigma>')" by blast+
    have F': "\<exists>f\<in>pv (l0,\<sigma>0) (l',\<sigma>'). x l0 \<in> f" using F P by blast
    have J': "S_J (hC l \<sigma>', \<sigma>')" by (rule stableD[OF S_J_stable J]) (simp add: rely_C_def E')
    from a m F' H' J' l' k0 k' show "A_post k0 k'" unfolding A_post_def by simp
  qed
qed

subsection \<open>The body of Sweep (Algorithm 19, lines 3-6)\<close>

text \<open>Thesis: line 4, "if x \<notin> marked then Add-to-free(x)".  If x is unmarked,
  Add-to-free marks it and puts it in free (at some point); if x is marked,
  nothing happens and, since inv-safe holds, interference marks nothing.\<close>

definition S_if_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "S_if_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). x l = x l0 \<and> consid l = consid l0 \<and>
                   marked \<sigma>0 \<subseteq> marked \<sigma> \<and> marked \<sigma> \<subseteq> insert (x l0) (marked \<sigma>0) \<and>
                   (x l0 \<notin> marked \<sigma>0 \<longrightarrow> x l0 \<in> marked \<sigma> \<and> (\<exists>f\<in>pv (l0,\<sigma>0) (l,\<sigma>). x l0 \<in> f)) \<and>
                   hist_ok (l0,\<sigma>0) (l,\<sigma>) \<and> S_J (l,\<sigma>))"

lemma S_if_sat: "coll_sat S_J (IfThen S_test (AddToFree :: ('a::finite,'i::finite) ccom)) S_guar S_if_post"
proof (rule rule_if)
  show "coll_sat (\<lambda>k. S_J k \<and> S_test k) (AddToFree :: ('a,'i) ccom) S_guar S_if_post"
  proof (rule rule_weaken[OF AddToFree_sat])
    fix k :: "('a,'i) cconf" assume "S_J k \<and> S_test k"
    then show "A_pre k" by (cases k) (simp add: A_pre_def S_test_def)
  next
    fix k k' :: "('a,'i) cconf" assume "A_guar k k'"
    then show "S_guar k k'" by (cases k, cases k') (simp add: A_guar_def)
  next
    fix k0 k :: "('a,'i) cconf" assume P: "S_J k0 \<and> S_test k0" and Q: "A_post k0 k"
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from Q k0 k have a: "x l = x l0" "consid l = consid l0" and m: "marked \<sigma> = insert (x l0) (marked \<sigma>0)"
      and F: "\<exists>f\<in>pv (l0,\<sigma>0) (l,\<sigma>). x l0 \<in> f" and H: "hist_ok (l0,\<sigma>0) (l,\<sigma>)" and J: "S_J (l,\<sigma>)"
      unfolding A_post_def by simp_all
    from a m F H J k0 k show "S_if_post k0 k" unfolding S_if_post_def by auto
  qed
next
  fix k0 k :: "('a,'i) cconf"
  assume P: "S_J k0 \<and> \<not> S_test k0" and RS: "envC\<^sup>*\<^sup>* k0 k"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  from RS k0 k have RS': "envC\<^sup>*\<^sup>* (l0,\<sigma>0) (l,\<sigma>)" by simp
  from P k0 have J0: "S_J (l0,\<sigma>0)" and xm: "x l0 \<in> marked \<sigma>0" unfolding S_test_def by simp_all
  from J0 have inv0: "inv_state \<sigma>0" and IS0: "inv_safe \<sigma>0" and s0: "s l0 = {}" unfolding S_J_def by simp_all
  have st: "inv_state \<sigma>" "inv_safe \<sigma> \<and> marked \<sigma> = marked \<sigma>0"
    using envC_star_state(5)[OF RS'] envC_star_state(6)[OF RS'] inv0 IS0 by simp_all
  have H: "hist_ok (l0,\<sigma>0) (l,\<sigma>)" using envC_star_hist[OF RS'] .
  from envC_star_sel[OF RS'] st H xm s0 k0 k show "S_if_post k0 k" unfolding S_if_post_def S_J_def by auto
next
  show "stable hC (rely_C s) S_J" by (rule S_J_stable)
next
  fix k :: "('a,'i) cconf"
  show "S_test (hupd hC k) = S_test k" by (cases k) (simp add: S_test_def)
next
  fix k0 k0' k :: "('a,'i) cconf"
  assume J0: "S_J k0" and E: "envC k0 k0'" and Q: "S_if_post k0' k"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l0' \<sigma>0' where k0': "k0' = (l0',\<sigma>0')" by (cases k0')
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  from E k0 k0' have l0': "l0' = hC l0 \<sigma>0'" and E': "env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0"
    by (simp_all add: rely_C_def)
  have m0: "marked \<sigma>0' = marked \<sigma>0" by (rule S_J_marked[OF J0[unfolded k0] E'])
  have E0: "envC (l0,\<sigma>0) (l0',\<sigma>0')" using E k0 k0' by simp
  from Q k0' k l0' have a: "x l = x l0" "consid l = consid l0" "marked \<sigma>0' \<subseteq> marked \<sigma>"
      "marked \<sigma> \<subseteq> insert (x l0) (marked \<sigma>0')"
    and F: "x l0 \<notin> marked \<sigma>0' \<longrightarrow> x l0 \<in> marked \<sigma> \<and> (\<exists>f\<in>pv (l0',\<sigma>0') (l,\<sigma>). x l0 \<in> f)"
    and H: "hist_ok (l0',\<sigma>0') (l,\<sigma>)" and J: "S_J (l,\<sigma>)"
    unfolding S_if_post_def by simp_all
  from hist_ok_env_left[OF E0 H] have H0: "hist_ok (l0,\<sigma>0) (l,\<sigma>)"
    and P: "pv (l0',\<sigma>0') (l,\<sigma>) \<subseteq> pv (l0,\<sigma>0) (l,\<sigma>)" by blast+
  have F0: "x l0 \<notin> marked \<sigma>0 \<longrightarrow> x l0 \<in> marked \<sigma> \<and> (\<exists>f\<in>pv (l0,\<sigma>0) (l,\<sigma>). x l0 \<in> f)"
    using F P m0 by auto
  from a m0 F0 H0 J k0 k show "S_if_post k0 k" unfolding S_if_post_def by simp
qed

text \<open>Thesis: lines 3 and 6, let x \<in> (Addr - consid) and consid \<leftarrow> consid \<union> {x};
  line 1, consid \<leftarrow> {}.\<close>

definition S_pick_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "S_pick_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). (x l \<notin> consid l0 \<and> consid l = consid l0) \<and>
                     marked \<sigma> = marked \<sigma>0 \<and> hist_ok (l0,\<sigma>0) (l,\<sigma>) \<and> S_J (l,\<sigma>))"

definition S_add_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "S_add_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). (consid l = consid l0 \<union> {x l0} \<and> x l = x l0) \<and>
                    marked \<sigma> = marked \<sigma>0 \<and> hist_ok (l0,\<sigma>0) (l,\<sigma>) \<and> S_J (l,\<sigma>))"

definition S_reset_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "S_reset_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). consid l = {} \<and>
                      marked \<sigma> = marked \<sigma>0 \<and> hist_ok (l0,\<sigma>0) (l,\<sigma>) \<and> S_J (l,\<sigma>))"

lemma S_pick_sat: "coll_sat S_J pick_x S_guar S_pick_post"
proof -
  have "coll_sat S_J pick_x S_guar
          (\<lambda>(l0,\<sigma>0) (l,\<sigma>). (x l \<notin> consid l0 \<and> consid l = consid l0) \<and> marked \<sigma> = marked \<sigma>0 \<and>
                             hist_ok (l0,\<sigma>0) (l,\<sigma>) \<and> S_J (l,\<sigma>))"
    unfolding pick_x_def by (rule S_private_sat) auto
  then show ?thesis unfolding S_pick_post_def .
qed

lemma S_add_sat: "coll_sat S_J consid_add S_guar S_add_post"
proof -
  have "coll_sat S_J consid_add S_guar
          (\<lambda>(l0,\<sigma>0) (l,\<sigma>). (consid l = consid l0 \<union> {x l0} \<and> x l = x l0) \<and> marked \<sigma> = marked \<sigma>0 \<and>
                             hist_ok (l0,\<sigma>0) (l,\<sigma>) \<and> S_J (l,\<sigma>))"
    unfolding consid_add_def by (rule S_private_sat) auto
  then show ?thesis unfolding S_add_post_def .
qed

lemma S_reset_sat: "coll_sat S_J consid_reset S_guar S_reset_post"
proof -
  have "coll_sat S_J consid_reset S_guar
          (\<lambda>(l0,\<sigma>0) (l,\<sigma>). consid l = {} \<and> marked \<sigma> = marked \<sigma>0 \<and>
                             hist_ok (l0,\<sigma>0) (l,\<sigma>) \<and> S_J (l,\<sigma>))"
    unfolding consid_reset_def by (rule S_private_sat) auto
  then show ?thesis unfolding S_reset_post_def .
qed

subsection \<open>The Sweep loop\<close>

text \<open>Thesis: test, inv and so-far for the loop of Sweep (Section 4.8.3):
    testS  \<triangleq> consid \<noteq> Addr                                      (consid_test)
    invS   \<triangleq> consid \<subseteq> Addr                                      (S_inv)
    so-farS \<triangleq> consid \<subset> consid' \<and> marked \<subseteq> marked' \<and>
              (\<forall>x \<in> consid' \<cdot> x \<notin> marked \<Rightarrow> (\<exists>f \<in> free~ \<cdot> x \<in> f) \<and> x \<in> marked') \<and>
              (\<forall>x \<in> (Addr - consid') \<cdot> x \<notin> marked \<Rightarrow> x \<notin> marked')       (S_sofar)
  so-farS is so_farS of GC_Sweep, with free~ the possible values of free
  between the two states (pv).  S_inv states, instead of consid \<subseteq> Addr, S_J
  and the fact the thesis uses for the third conjunct: "any address x that
  was considered in a previous iteration was marked before it was added to
  free, and will remain marked at the start of this iteration", that is
  consid \<subseteq> marked.  S_sofar also records that the history variable only
  records, and inv-safe at the end (so that it holds despite interference).\<close>

definition S_inv :: "('a,'i) cconf \<Rightarrow> bool" where
  "S_inv = (\<lambda>(l,\<sigma>). S_J (l,\<sigma>) \<and> consid l \<subseteq> marked \<sigma>)"

definition S_sofar :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "S_sofar = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). so_farS (consid l0) \<sigma>0 (pv (l0,\<sigma>0) (l,\<sigma>)) (consid l) \<sigma> \<and>
                  hist_ok (l0,\<sigma>0) (l,\<sigma>) \<and> inv_safe \<sigma>)"

definition S_P0 :: "('a,'i) cconf \<Rightarrow> bool" where
  "S_P0 = (\<lambda>(l,\<sigma>). consid l = {} \<and> S_J (l,\<sigma>))"

text \<open>Mechanisation only: so-farS only gets weaker with more possible values,
  and depends on the start state only through marked.\<close>

lemma so_farS_mono:
  "so_farS c \<sigma> F c' \<sigma>' \<Longrightarrow> F \<subseteq> G \<Longrightarrow> so_farS c \<sigma> G c' \<sigma>'"
  unfolding so_farS_def by blast

lemma so_farS_start:
  "so_farS c \<sigma>0' F c' \<sigma> \<Longrightarrow> marked \<sigma>0' = marked \<sigma>0 \<Longrightarrow> so_farS c \<sigma>0 F c' \<sigma>"
  unfolding so_farS_def by simp

lemma so_farS_end:
  "so_farS c \<sigma>0 F c' \<sigma> \<Longrightarrow> marked \<sigma>' = marked \<sigma> \<Longrightarrow> so_farS c \<sigma>0 F c' \<sigma>'"
  unfolding so_farS_def by simp

lemma S_inv_stable: "stable hC (rely_C s) S_inv"
proof (rule stableC)
  fix l \<sigma> \<sigma>' assume I: "S_inv (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  from I have J: "S_J (l,\<sigma>)" and c: "consid l \<subseteq> marked \<sigma>" unfolding S_inv_def by simp_all
  have "S_J (hC l \<sigma>', \<sigma>')" by (rule stableD[OF S_J_stable J]) (simp add: rely_C_def E)
  moreover have "consid l \<subseteq> marked \<sigma>'" using c envs_marked[OF E] by blast
  ultimately show "S_inv (hC l \<sigma>', \<sigma>')" unfolding S_inv_def by simp
qed

text \<open>Thesis: so-farS holds despite interference: "consid is private to the
  Collector, and neither the Collector nor the Mutator remove elements from
  marked"; "since the Mutator can only mark reachable nodes, and they are all
  marked during Sweep, no environment steps change marked during this
  phase"; and the possible values of free only grow.\<close>

lemma S_sofar_tolerates: "tolerates hC (rely_C s) S_inv S_sofar"
proof (rule toleratesC)
  fix k0 l \<sigma> \<sigma>' assume Q: "S_sofar k0 (l,\<sigma>)" and E: "env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  from Q k0 have SF: "so_farS (consid l0) \<sigma>0 (pv (l0,\<sigma>0) (l,\<sigma>)) (consid l) \<sigma>"
    and H: "hist_ok (l0,\<sigma>0) (l,\<sigma>)" and IS: "inv_safe \<sigma>" unfolding S_sofar_def by simp_all
  from envs_inv_safe[OF E IS] have IS': "inv_safe \<sigma>'" and m: "marked \<sigma>' = marked \<sigma>" by blast+
  have Ek: "envC (l,\<sigma>) (hC l \<sigma>', \<sigma>')" using E by (simp add: rely_C_def)
  from hist_ok_env[OF H Ek] have H': "hist_ok (l0,\<sigma>0) (hC l \<sigma>', \<sigma>')"
    and P: "pv (l0,\<sigma>0) (l,\<sigma>) \<subseteq> pv (l0,\<sigma>0) (hC l \<sigma>', \<sigma>')" by blast+
  have "so_farS (consid l0) \<sigma>0 (pv (l0,\<sigma>0) (hC l \<sigma>', \<sigma>')) (consid l) \<sigma>'"
    by (rule so_farS_end[OF so_farS_mono[OF SF P] m])
  with H' IS' k0 show "S_sofar k0 (hC l \<sigma>', \<sigma>')" unfolding S_sofar_def by simp
next
  fix l0 \<sigma>0 \<sigma>0' k assume I: "S_inv (l0,\<sigma>0)" and E: "env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0"
    and Q: "S_sofar (hC l0 \<sigma>0', \<sigma>0') k"
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  from Q k have SF: "so_farS (consid l0) \<sigma>0' (pv (hC l0 \<sigma>0', \<sigma>0') (l,\<sigma>)) (consid l) \<sigma>"
    and H: "hist_ok (hC l0 \<sigma>0', \<sigma>0') (l,\<sigma>)" and IS: "inv_safe \<sigma>" unfolding S_sofar_def by simp_all
  from I have J: "S_J (l0,\<sigma>0)" unfolding S_inv_def by simp
  have m: "marked \<sigma>0' = marked \<sigma>0" by (rule S_J_marked[OF J E])
  have Ek: "envC (l0,\<sigma>0) (hC l0 \<sigma>0', \<sigma>0')" using E by (simp add: rely_C_def)
  from hist_ok_env_left[OF Ek H] have H0: "hist_ok (l0,\<sigma>0) (l,\<sigma>)"
    and P: "pv (hC l0 \<sigma>0', \<sigma>0') (l,\<sigma>) \<subseteq> pv (l0,\<sigma>0) (l,\<sigma>)" by blast+
  have "so_farS (consid l0) \<sigma>0 (pv (l0,\<sigma>0) (l,\<sigma>)) (consid l) \<sigma>"
    by (rule so_farS_start[OF so_farS_mono[OF SF P] m])
  with H0 IS k show "S_sofar (l0,\<sigma>0) k" unfolding S_sofar_def by simp
qed

text \<open>Thesis: Lemma 14, transitivity (lemma14_so_farS_trans): the possible
  values over two consecutive intervals are among those over the whole.\<close>

lemma S_sofar_trans:
  assumes "S_sofar k0 k1" and "S_sofar k1 k2"
  shows "S_sofar k0 k2"
proof -
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
  obtain l2 \<sigma>2 where k2: "k2 = (l2,\<sigma>2)" by (cases k2)
  from assms(1) k0 k1 have A: "so_farS (consid l0) \<sigma>0 (pv k0 k1) (consid l1) \<sigma>1"
    and H1: "hist_ok k0 k1" unfolding S_sofar_def by simp_all
  from assms(2) k1 k2 have B: "so_farS (consid l1) \<sigma>1 (pv k1 k2) (consid l2) \<sigma>2"
    and H2: "hist_ok k1 k2" and IS: "inv_safe \<sigma>2" unfolding S_sofar_def by simp_all
  from hist_ok_trans[OF H1 H2] have H: "hist_ok k0 k2" and P: "pv k0 k1 \<union> pv k1 k2 \<subseteq> pv k0 k2" by blast+
  have "so_farS (consid l0) \<sigma>0 (pv k0 k2) (consid l2) \<sigma>2"
    by (rule so_farS_mono[OF lemma14_so_farS_trans[OF A B] P])
  with H IS k0 k2 show ?thesis unfolding S_sofar_def by simp
qed

text \<open>Thesis: one iteration establishes so-farS and keeps invS.  For the third
  conjunct, "if x \<in> consid', then x \<notin> marked implies x \<notin> consid, so x was
  added to free in the current iteration"; for the fourth, only x is
  marked.\<close>

lemma S_body_sat:
  "coll_sat (\<lambda>k. S_inv k \<and> consid_test k) (S_body :: ('a::finite,'i::finite) ccom) S_guar
            (\<lambda>k0 k. S_inv k \<and> S_sofar k0 k)"
proof -
  have "coll_sat S_J (Seq (IfThen S_test AddToFree) consid_add :: ('a,'i) ccom) S_guar
          (seq_post S_if_post S_add_post)"
    by (rule rule_seq[OF S_if_sat S_add_sat]) (auto simp: S_if_post_def split_beta)
  then have V: "coll_sat S_J (S_body :: ('a,'i) ccom) S_guar
                  (seq_post S_pick_post (seq_post S_if_post S_add_post))"
    unfolding S_body_def by (rule rule_seq[OF S_pick_sat]) (auto simp: S_pick_post_def split_beta)
  have Q: "S_inv k \<and> S_sofar k0 k"
    if P: "S_inv k0 \<and> consid_test k0" and C: "seq_post S_pick_post (seq_post S_if_post S_add_post) k0 k"
    for k0 k :: "('a,'i) cconf"
  proof -
    from C obtain k1 k2 where 1: "S_pick_post k0 k1" and 2: "S_if_post k1 k2" and 3: "S_add_post k2 k"
      unfolding seq_post_def by blast
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
    obtain l2 \<sigma>2 where k2: "k2 = (l2,\<sigma>2)" by (cases k2)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from P k0 have c0: "consid l0 \<subseteq> marked \<sigma>0" unfolding S_inv_def by simp
    from 1 k0 k1 have a: "x l1 \<notin> consid l0" "consid l1 = consid l0" "marked \<sigma>1 = marked \<sigma>0"
      and H1: "hist_ok k0 k1" unfolding S_pick_post_def by simp_all
    from 2 k1 k2 have b: "x l2 = x l1" "consid l2 = consid l1" "marked \<sigma>1 \<subseteq> marked \<sigma>2"
        "marked \<sigma>2 \<subseteq> insert (x l1) (marked \<sigma>1)"
      and F: "x l1 \<notin> marked \<sigma>1 \<longrightarrow> x l1 \<in> marked \<sigma>2 \<and> (\<exists>f\<in>pv k1 k2. x l1 \<in> f)"
      and H2: "hist_ok k1 k2" unfolding S_if_post_def by simp_all
    from 3 k2 k have c: "consid l = consid l2 \<union> {x l2}" "marked \<sigma> = marked \<sigma>2"
      and H3: "hist_ok k2 k" and J: "S_J (l,\<sigma>)" unfolding S_add_post_def by simp_all
    from hist_ok_trans[OF H1 H2] have H12: "hist_ok k0 k2" and P12: "pv k1 k2 \<subseteq> pv k0 k2" by blast+
    from hist_ok_trans[OF H12 H3] have H: "hist_ok k0 k" and P2: "pv k0 k2 \<subseteq> pv k0 k" by blast+
    have cc: "consid l = consid l0 \<union> {x l1}" using a b c by simp
    have m01: "marked \<sigma>0 \<subseteq> marked \<sigma>" using a(3) b(3) c(2) by simp
    have xm: "x l1 \<in> marked \<sigma>"
    proof (cases "x l1 \<in> marked \<sigma>1")
      case True then show ?thesis using b(3) c(2) by auto
    next
      case False then show ?thesis using F c(2) by simp
    qed
    have "consid l0 \<subset> consid l" using cc a(1) by auto
    moreover have "\<forall>y\<in>consid l. y \<notin> marked \<sigma>0 \<longrightarrow> (\<exists>f\<in>pv k0 k. y \<in> f) \<and> y \<in> marked \<sigma>"
    proof (intro ballI impI)
      fix y assume y: "y \<in> consid l" and ym: "y \<notin> marked \<sigma>0"
      from y cc c0 ym have yx: "y = x l1" by auto
      with ym a(3) have "x l1 \<notin> marked \<sigma>1" by simp
      with F have "\<exists>f\<in>pv k1 k2. x l1 \<in> f" by blast
      with P12 P2 yx xm show "(\<exists>f\<in>pv k0 k. y \<in> f) \<and> y \<in> marked \<sigma>" by blast
    qed
    moreover have "\<forall>y\<in>UNIV - consid l. y \<notin> marked \<sigma>0 \<longrightarrow> y \<notin> marked \<sigma>"
    proof (intro ballI impI)
      fix y assume y: "y \<in> UNIV - consid l" and ym: "y \<notin> marked \<sigma>0"
      from y cc have yx: "y \<noteq> x l1" by auto
      have "marked \<sigma> \<subseteq> insert (x l1) (marked \<sigma>0)" using b(4) c(2) a(3) by simp
      with yx ym show "y \<notin> marked \<sigma>" by blast
    qed
    ultimately have SF: "so_farS (consid l0) \<sigma>0 (pv k0 k) (consid l) \<sigma>"
      using m01 unfolding so_farS_def by blast
    from J have IS: "inv_safe \<sigma>" unfolding S_J_def by simp
    have "consid l \<subseteq> marked \<sigma>" using cc c0 m01 xm by auto
    with J SF H IS k0 k show ?thesis unfolding S_inv_def S_sofar_def by simp
  qed
  show ?thesis by (rule rule_weaken[OF V _ _ Q]) (simp_all add: S_inv_def split_beta)
qed

text \<open>Thesis: the loop of Sweep, by the while rule with Lemma 14 and Theorem 5:
  when it exits, consid' = Addr, and with consid = {} at the start so-farS
  gives post-Sweep.  It is satisfied despite interference after the loop,
  since the possible values of free only grow.\<close>

definition S_loop_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "S_loop_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). post_Sweep \<sigma>0 (pv (l0,\<sigma>0) (l,\<sigma>)) \<sigma> \<and> hist_ok (l0,\<sigma>0) (l,\<sigma>))"

lemma post_Sweep_mono: "post_Sweep \<sigma>0 F \<sigma> \<Longrightarrow> F \<subseteq> G \<Longrightarrow> post_Sweep \<sigma>0 G \<sigma>'"
  unfolding post_Sweep_def by blast

lemma S_loop_sat:
  "coll_sat S_P0 (While consid_test (S_body :: ('a::finite,'i::finite) ccom)) S_guar S_loop_post"
proof (rule rule_while[where I = S_inv and sofar = S_sofar,
                       OF _ S_body_sat S_inv_stable _ S_sofar_trans S_sofar_tolerates])
  fix k :: "('a,'i) cconf" assume "S_P0 k"
  then show "S_inv k" by (cases k) (simp add: S_P0_def S_inv_def)
next
  fix k :: "('a,'i) cconf"
  show "consid_test (hupd hC k) = consid_test k" by (cases k) (simp add: consid_test_def)
next
  fix k0 k :: "('a,'i) cconf"
  assume P0: "S_P0 k0" and T: "\<not> consid_test k" and W: "S_sofar k0 k \<or> envC\<^sup>*\<^sup>* k0 k"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  from P0 k0 have c0: "consid l0 = {}" by (simp add: S_P0_def)
  from T k have c: "consid l = UNIV" by (simp add: consid_test_def)
  from W show "S_loop_post k0 k"
  proof
    assume "S_sofar k0 k"
    then have SF: "so_farS {} \<sigma>0 (pv k0 k) UNIV \<sigma>" and H: "hist_ok k0 k"
      using k0 k c0 c by (simp_all add: S_sofar_def)
    have "post_Sweep \<sigma>0 (pv k0 k) \<sigma>" by (rule theorem5_post_Sweep[OF SF])
    with H k0 k show ?thesis by (simp add: S_loop_post_def)
  next
    assume "envC\<^sup>*\<^sup>* k0 k"
    then have "envC\<^sup>*\<^sup>* (l0,\<sigma>0) (l,\<sigma>)" using k0 k by simp
    from envC_star_sel(1)[OF this] c0 c show ?thesis by simp
  qed
next
  fix k0 k k' :: "('a,'i) cconf"
  assume Q: "S_loop_post k0 k" and E: "envC k k'"
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  from Q k0 k have PS: "post_Sweep \<sigma>0 (pv k0 k) \<sigma>" and H: "hist_ok k0 k"
    unfolding S_loop_post_def by simp_all
  from hist_ok_env[OF H E] have H': "hist_ok k0 k'" and P: "pv k0 k \<subseteq> pv k0 k'" by blast+
  have "post_Sweep \<sigma>0 (pv k0 k') (snd k')" by (rule post_Sweep_mono[OF PS P])
  with H' k0 show "S_loop_post k0 k'" by (cases k') (simp add: S_loop_post_def)
qed

text \<open>Thesis: Sweep meets its specification (Section 4.8.3), "by Lemma 14 and
  Theorem 5", with pre condition inv-safe, reach(roots, hp) \<subseteq> marked (in
  S_J).  Every step of Sweep is taken in a state where S_J holds (Lemmas 15
  and 16), which is what the proof of safety (Section 4.8.4) uses.\<close>

definition S_post :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "S_post = (\<lambda>(l0,\<sigma>0) (l,\<sigma>). post_Sweep \<sigma>0 (pv (l0,\<sigma>0) (l,\<sigma>)) \<sigma> \<and> hist_ok (l0,\<sigma>0) (l,\<sigma>))"

theorem Sweep_sat:
  "coll_sat S_J (Sweep :: ('a::finite,'i::finite) ccom) (\<lambda>k k'. S_guar k k' \<and> S_J k)
            (\<lambda>k0 k. S_post k0 k \<and> S_J k)"
proof -
  have V: "coll_sat S_J (Sweep :: ('a,'i) ccom) S_guar (seq_post S_reset_post S_loop_post)"
    unfolding Sweep_def
    by (rule rule_seq[OF S_reset_sat S_loop_sat]) (auto simp: S_reset_post_def S_P0_def split_beta)
  have Q: "S_post k0 k" if "seq_post S_reset_post S_loop_post k0 k" for k0 k :: "('a,'i) cconf"
  proof -
    from that obtain k1 where 1: "S_reset_post k0 k1" and 2: "S_loop_post k1 k"
      unfolding seq_post_def by blast
    obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
    obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
    obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
    from 1 k0 k1 have m: "marked \<sigma>1 = marked \<sigma>0" and H1: "hist_ok k0 k1"
      unfolding S_reset_post_def by simp_all
    from 2 k1 k have PS: "post_Sweep \<sigma>1 (pv k1 k) \<sigma>" and H2: "hist_ok k1 k"
      unfolding S_loop_post_def by simp_all
    from hist_ok_trans[OF H1 H2] have H: "hist_ok k0 k" and P: "pv k1 k \<subseteq> pv k0 k" by blast+
    have "post_Sweep \<sigma>0 (pv k1 k) \<sigma>" using PS m unfolding post_Sweep_def by simp
    then have "post_Sweep \<sigma>0 (pv k0 k) \<sigma>" by (rule post_Sweep_mono[OF _ P])
    with H k0 k show ?thesis unfolding S_post_def by simp
  qed
  have V': "coll_sat S_J (Sweep :: ('a,'i) ccom) S_guar S_post"
    by (rule rule_weaken[OF V _ _ Q]) simp_all
  have IG: "S_J k'" if "S_J k" and "S_guar k k'" for k k' :: "('a,'i) cconf"
    using that by (cases k, cases k') (simp add: S_guar_J)
  show ?thesis by (rule rule_inv[OF V' _ S_J_stable IG]) simp
qed

end
