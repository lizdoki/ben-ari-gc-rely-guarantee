(*  GC_Invariant: Section 4.7 of the thesis -- the invariant invB.
      invB     -- at most one protected edge points to an unmarked node, and
                  that node has another parent reachable without that edge
      Lemma 1  -- an environment step preserves card (Bad) <= 1
      Lemma 2  -- an environment step preserves invB
      Lemma 3  -- a program step never increases Bad
      Lemma 4  -- a program step preserves invB
    A program step is a step satisfying step-Collector (GC_Collector_Steps).

    PART 2 of the mechanisation, for the Collector (folder 2a_Collector).
    GC_Collector_Steps says how this part is organised.

    HOW TO READ THE LABELS.  Each definition and theorem below has a text
    block saying how it relates to the thesis:
      "Thesis:"             it is that part of the thesis;
      "Beyond the thesis:"  the thesis states or argues it informally or not
                            at all; the label says which part of the thesis
                            it makes precise or supports;
      "Mechanisation only:" a helper needed only for the Isabelle proof.
    Section, lemma and theorem numbers are those of the thesis.  *)

theory GC_Invariant
  imports GC_Collector_Steps
begin

section \<open>The invariant invB (Section 4.7)\<close>

text \<open>Thesis: invB (Section 4.7).  Bad(s, \<sigma>) has at most one edge, and for
  that edge there is another edge to the same node whose source is
  reachable from a marked node in the heap with the bad edge deleted.\<close>

definition invB :: "('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "invB s \<sigma> \<longleftrightarrow>
     card (Bad s \<sigma>) \<le> 1 \<and>
     (\<forall>e\<in>Bad s \<sigma>. \<exists>e'\<in>dom (hp \<sigma>).
         fst e' \<in> reach (marked \<sigma>) ((hp \<sigma>)(e := None)) \<and> e' \<noteq> e \<and> hp \<sigma> e' = hp \<sigma> e)"

text \<open>Thesis: Section 4.7, before 4.7.1: the Collector starts with s = {}, so
  Bad(s, \<sigma>) = {} and invB holds trivially.\<close>

lemma invB_empty: "invB {} \<sigma>"
  unfolding invB_def Bad_def by simp

section \<open>Environment steps (Section 4.7.1)\<close>

text \<open>Thesis: Case 1 of Lemmas 1 and 2: when the heap does not change, the Bad set can
      only shrink, because marks are never removed by the environment.\<close>

lemma Bad_env_same_hp:
  assumes "hp \<sigma>' = hp \<sigma>" and "marked \<sigma> \<subseteq> marked \<sigma>'"
  shows "Bad s \<sigma>' \<subseteq> Bad s \<sigma>"
  unfolding Bad_def using assms by auto

text \<open>Thesis: Case 2 of Lemma 1: a heap update can add at most the changed edge.\<close>

lemma Bad_env_hp_change:
  assumes E: "\<forall>e'. e' \<noteq> e \<longrightarrow> hp \<sigma>' e' = hp \<sigma> e'" and M: "marked \<sigma>' = marked \<sigma>"
    and BE: "Bad s \<sigma> = {}"
  shows "Bad s \<sigma>' \<subseteq> {e}"
proof (rule subsetI)
  fix e' assume e'B: "e' \<in> Bad s \<sigma>'"
  show "e' \<in> {e}"
  proof (rule ccontr)
    assume "e' \<notin> {e}"
    then have ne: "e' \<noteq> e" by simp
    have he: "hp \<sigma>' e' = hp \<sigma> e'" by (rule E[rule_format, OF ne])
    from e'B have es: "e' \<in> s" and ex: "\<exists>b. hp \<sigma>' e' = Some b \<and> b \<notin> marked \<sigma>'"
      unfolding Bad_def by simp_all
    from ex obtain b where eb: "hp \<sigma>' e' = Some b" and bM: "b \<notin> marked \<sigma>'" by blast
    have "hp \<sigma> e' = Some b" using he eb by simp
    moreover have "b \<notin> marked \<sigma>" using bM M by simp
    ultimately have "e' \<in> Bad s \<sigma>" using es unfolding Bad_def by blast
    with BE show False by simp
  qed
qed

text \<open>Thesis: Lemma 1 (an environment step preserves cardinality):
    card Bad(s, \<sigma>) \<le> 1 \<and> rely-Collector(\<sigma>, \<sigma>') \<Rightarrow> card Bad(s', \<sigma>') \<le> 1.\<close>

theorem lemma1_env_card:
  fixes \<sigma> \<sigma>' :: "('a::finite,'i::finite) state"
  assumes "card (Bad s \<sigma>) \<le> 1" and R: "rely_Collector s \<sigma> \<sigma>'" and A: "atomic \<sigma> \<sigma>'"
  shows "card (Bad s \<sigma>') \<le> 1"
proof (cases "hp \<sigma>' = hp \<sigma>")
  case True
  have "Bad s \<sigma>' \<subseteq> Bad s \<sigma>" by (rule Bad_env_same_hp[OF True rely_marked_mono[OF R]])
  from card_mono[OF finite_Bad this] assms(1) show ?thesis by simp
next
  case False
  obtain e where
    E: "\<forall>e'. e' \<noteq> e \<longrightarrow> hp \<sigma>' e' = hp \<sigma> e'" and hne: "hp \<sigma>' e \<noteq> hp \<sigma> e"
    and M: "marked \<sigma>' = marked \<sigma>" and "free \<sigma>' = free \<sigma>"
    by (rule atomic_hp_change[OF A False])
  have BE: "Bad s \<sigma> = {}" using R hne M unfolding rely_Collector_def by blast
  have "Bad s \<sigma>' \<subseteq> {e}" by (rule Bad_env_hp_change[OF E M BE])
  from card_mono[OF _ this] show ?thesis by simp
qed

text \<open>Thesis: Case 2 of Lemma 2.  The thesis argues by cases on whether the old root
      path to \<open>b\<close> passes through the changed edge (Figure 4.20, cases 1, 2.1,
      2.2).  Mechanically, all cases are covered at once by @{thm reach_upd}:
      every node reachable from the roots in the old heap is reachable from
      the roots together with the old target \<open>c\<close> in the heap with the edge
      deleted, and \<open>c\<close> is marked.\<close>

lemma invB_witness_hp_change:
  fixes \<sigma> \<sigma>' :: "('a,'i) state"
  assumes inv: "inv_state \<sigma>" and R: "rely_Collector s \<sigma> \<sigma>'"
    and E: "\<forall>e'. e' \<noteq> e \<longrightarrow> hp \<sigma>' e' = hp \<sigma> e'" and hne: "hp \<sigma>' e \<noteq> hp \<sigma> e"
    and M: "marked \<sigma>' = marked \<sigma>"
    and eB: "e \<in> Bad s \<sigma>'"
  shows "\<exists>e'\<in>dom (hp \<sigma>'). fst e' \<in> reach (marked \<sigma>') ((hp \<sigma>')(e := None)) \<and> e' \<noteq> e \<and> hp \<sigma>' e' = hp \<sigma>' e"
proof -
  have BE: "Bad s \<sigma> = {}" using R hne M unfolding rely_Collector_def by blast
  from eB obtain b where es: "e \<in> s" and eb: "hp \<sigma>' e = Some b" and bM: "b \<notin> marked \<sigma>'"
    unfolding Bad_def by blast
  \<comment> \<open>the new target is reachable from the roots in the old heap\<close>
  have "b \<notin> garbage \<sigma>" using R hne eb unfolding rely_Collector_def by blast
  moreover have "b \<notin> free \<sigma>" using bM M inv_free_marked[OF inv] by blast
  ultimately have bR: "b \<in> reach (roots \<sigma>) (hp \<sigma>)" unfolding garbage_def by blast
  let ?d = "(hp \<sigma>)(e := None)"
  have del_eq: "(hp \<sigma>')(e := None) = ?d" by (rule fun_upd_same_del[OF E])
  \<comment> \<open>hence reachable from a marked node without using the changed edge\<close>
  have bRd: "b \<in> reach (marked \<sigma>) ?d"
  proof (cases "hp \<sigma> e")
    case None
    then have "?d = hp \<sigma>" by (simp add: fun_upd_idem_iff)
    then have "reach (marked \<sigma>) ?d = reach (marked \<sigma>) (hp \<sigma>)" by simp
    then show ?thesis using bR reach_mono[OF inv_roots_marked[OF inv], of "hp \<sigma>"] by blast
  next
    case (Some c)
    from BE have "e \<notin> Bad s \<sigma>" by simp
    then have cM: "c \<in> marked \<sigma>" using es Some unfolding Bad_def by auto
    have step1: "reach (roots \<sigma>) (hp \<sigma>) \<subseteq> reach (roots \<sigma> \<union> {c}) ?d"
      using reach_upd[of "roots \<sigma>" ?d e c] by (simp add: fun_upd_idem[of "hp \<sigma>" e "Some c", OF Some])
    have "roots \<sigma> \<union> {c} \<subseteq> marked \<sigma>" using inv_roots_marked[OF inv] cM by blast
    then have step2: "reach (roots \<sigma> \<union> {c}) ?d \<subseteq> reach (marked \<sigma>) ?d" by (rule reach_mono)
    from bR step1 step2 show ?thesis by blast
  qed
  have "b \<notin> marked \<sigma>" using bM M by simp
  from reach_last_edge[OF bRd this] obtain y i where
    yi: "?d (y,i) = Some b" and yR: "y \<in> reach (marked \<sigma>) ?d" by blast
  have ne: "(y,i) \<noteq> e" using yi by (auto split: if_splits)
  have "hp \<sigma>' (y,i) = Some b"
  proof -
    have "hp \<sigma> (y,i) = Some b" using yi ne by simp
    moreover have "hp \<sigma>' (y,i) = hp \<sigma> (y,i)" using E ne by simp
    ultimately show ?thesis by simp
  qed
  moreover have "y \<in> reach (marked \<sigma>') ((hp \<sigma>')(e := None))"
    using yR del_eq M by simp
  ultimately show ?thesis using ne eb by (intro bexI[where x="(y,i)"]) auto
qed

text \<open>Thesis: Lemma 2 (an environment step preserves the invariant):
    invB(s, \<sigma>) \<and> rely-Collector(\<sigma>, \<sigma>') \<Rightarrow> invB(s', \<sigma>').\<close>

theorem lemma2_env_invB:
  fixes \<sigma> \<sigma>' :: "('a::finite,'i::finite) state"
  assumes ES: "env_step s \<sigma> \<sigma>'" and IB: "invB s \<sigma>"
  shows "invB s \<sigma>'"
proof -
  from ES have inv: "inv_state \<sigma>" and R: "rely_Collector s \<sigma> \<sigma>'" and A: "atomic \<sigma> \<sigma>'"
    unfolding env_step_def by blast+
  have C: "card (Bad s \<sigma>') \<le> 1"
    using lemma1_env_card[OF _ R A] IB unfolding invB_def by blast
  have M: "marked \<sigma> \<subseteq> marked \<sigma>'" by (rule rely_marked_mono[OF R])
  have W: "\<forall>e\<in>Bad s \<sigma>'. \<exists>e'\<in>dom (hp \<sigma>').
             fst e' \<in> reach (marked \<sigma>') ((hp \<sigma>')(e := None)) \<and> e' \<noteq> e \<and> hp \<sigma>' e' = hp \<sigma>' e"
  proof (cases "hp \<sigma>' = hp \<sigma>")
    case True
    show ?thesis
    proof
      fix e assume "e \<in> Bad s \<sigma>'"
      with Bad_env_same_hp[OF True M] have "e \<in> Bad s \<sigma>" by auto
      with IB obtain e' where e'd: "e' \<in> dom (hp \<sigma>)"
        and e'R: "fst e' \<in> reach (marked \<sigma>) ((hp \<sigma>)(e := None))"
        and ne: "e' \<noteq> e" and eq: "hp \<sigma> e' = hp \<sigma> e"
        unfolding invB_def by blast
      have "e' \<in> dom (hp \<sigma>')" using e'd True by simp
      moreover have "fst e' \<in> reach (marked \<sigma>') ((hp \<sigma>')(e := None))"
      proof -
        have "reach (marked \<sigma>) ((hp \<sigma>)(e := None)) \<subseteq> reach (marked \<sigma>') ((hp \<sigma>')(e := None))"
          using reach_mono[OF M] True by simp
        with e'R show ?thesis by blast
      qed
      moreover have "hp \<sigma>' e' = hp \<sigma>' e" using eq True by simp
      ultimately show "\<exists>e'\<in>dom (hp \<sigma>'). fst e' \<in> reach (marked \<sigma>') ((hp \<sigma>')(e := None)) \<and> e' \<noteq> e \<and> hp \<sigma>' e' = hp \<sigma>' e"
        using ne by blast
    qed
  next
    case False
    obtain e0 where
      E: "\<forall>e'. e' \<noteq> e0 \<longrightarrow> hp \<sigma>' e' = hp \<sigma> e'" and hne: "hp \<sigma>' e0 \<noteq> hp \<sigma> e0"
      and MM: "marked \<sigma>' = marked \<sigma>" and "free \<sigma>' = free \<sigma>"
      by (rule atomic_hp_change[OF A False])
    have BE: "Bad s \<sigma> = {}" using R hne MM unfolding rely_Collector_def by blast
    show ?thesis
    proof
      fix e assume eB: "e \<in> Bad s \<sigma>'"
      with Bad_env_hp_change[OF E MM BE] have ee0: "e = e0" by auto
      with eB have "e0 \<in> Bad s \<sigma>'" by simp
      then have "\<exists>e'\<in>dom (hp \<sigma>'). fst e' \<in> reach (marked \<sigma>') ((hp \<sigma>')(e0 := None)) \<and> e' \<noteq> e0 \<and> hp \<sigma>' e' = hp \<sigma>' e0"
        by (rule invB_witness_hp_change[OF inv R E hne MM])
      then show "\<exists>e'\<in>dom (hp \<sigma>'). fst e' \<in> reach (marked \<sigma>') ((hp \<sigma>')(e := None)) \<and> e' \<noteq> e \<and> hp \<sigma>' e' = hp \<sigma>' e"
        using ee0 by simp
    qed
  qed
  from C W show ?thesis unfolding invB_def by blast
qed

section \<open>Program steps (Section 4.7.2)\<close>

text \<open>Thesis: Lemma 3 (a program step never increases the bad set):
    step-Collector(\<sigma>, \<sigma>') \<Rightarrow> Bad(s', \<sigma>') \<subseteq> Bad(s, \<sigma>).\<close>

theorem lemma3_prog_Bad:
  assumes "step_Collector s \<sigma> s' \<sigma>'"
  shows "Bad s' \<sigma>' \<subseteq> Bad s \<sigma>"
proof -
  consider (U) "guar_Unmark s \<sigma> s' \<sigma>'"
    | (St) "stutter s \<sigma> s' \<sigma>'"
    | (En) "guar_MarkEnd s \<sigma> s' \<sigma>'"
    | (K) x where "x \<in> marked \<sigma>" "guar_MarkKids x s \<sigma> s' \<sigma>'"
    | (Sw) "s' = {}"
    using assms unfolding step_Collector_def guar_Mark_def by blast
  then show ?thesis
  proof cases
    case U
    then show ?thesis unfolding guar_Unmark_def Bad_def by auto
  next
    case St
    then show ?thesis unfolding stutter_def Bad_def by auto
  next
    case En
    then show ?thesis unfolding guar_MarkEnd_def Bad_def by auto
  next
    case (K x)
    then have H: "hp \<sigma>' = hp \<sigma>" and M: "marked \<sigma> \<subseteq> marked \<sigma>'" and S: "s \<subseteq> s'"
      and N: "\<forall>e\<in>s' - s. e \<notin> dom (hp \<sigma>) \<or> (\<exists>b. hp \<sigma> e = Some b \<and> b \<in> marked \<sigma>')"
      unfolding guar_MarkKids_def by blast+
    show ?thesis
    proof
      fix e assume "e \<in> Bad s' \<sigma>'"
      then obtain b where es': "e \<in> s'" and eb: "hp \<sigma> e = Some b" and bM: "b \<notin> marked \<sigma>'"
        unfolding Bad_def H by blast
      have "e \<in> s"
      proof (rule ccontr)
        assume "e \<notin> s"
        with es' N have "e \<notin> dom (hp \<sigma>) \<or> (\<exists>b. hp \<sigma> e = Some b \<and> b \<in> marked \<sigma>')" by blast
        with eb bM show False by auto
      qed
      moreover have "b \<notin> marked \<sigma>" using bM M by blast
      ultimately show "e \<in> Bad s \<sigma>" using eb unfolding Bad_def by blast
    qed
  next
    case Sw
    then show ?thesis unfolding Bad_def by auto
  qed
qed

text \<open>Thesis: Lemma 4 (a program step preserves the invariant):
    invB(s, \<sigma>) \<and> step-Collector(\<sigma>, \<sigma>') \<Rightarrow> invB(s', \<sigma>').\<close>

theorem lemma4_prog_invB:
  fixes \<sigma> \<sigma>' :: "('a::finite,'i::finite) state"
  assumes G: "step_Collector s \<sigma> s' \<sigma>'" and IB: "invB s \<sigma>"
  shows "invB s' \<sigma>'"
proof -
  have sub: "Bad s' \<sigma>' \<subseteq> Bad s \<sigma>" by (rule lemma3_prog_Bad[OF G])
  have C: "card (Bad s' \<sigma>') \<le> 1"
    using card_mono[OF finite_Bad sub] IB unfolding invB_def by simp
  \<comment> \<open>In every phase the heap is either unchanged or the protected set is empty.\<close>
  have HM: "s' = {} \<or> (hp \<sigma>' = hp \<sigma> \<and> marked \<sigma> \<subseteq> marked \<sigma>')"
    using G unfolding step_Collector_def guar_Unmark_def guar_Mark_def stutter_def
      guar_MarkEnd_def guar_MarkKids_def by blast
  have W: "\<forall>e\<in>Bad s' \<sigma>'. \<exists>e'\<in>dom (hp \<sigma>').
             fst e' \<in> reach (marked \<sigma>') ((hp \<sigma>')(e := None)) \<and> e' \<noteq> e \<and> hp \<sigma>' e' = hp \<sigma>' e"
  proof
    fix e assume eB: "e \<in> Bad s' \<sigma>'"
    with HM have H: "hp \<sigma>' = hp \<sigma>" and M: "marked \<sigma> \<subseteq> marked \<sigma>'"
      unfolding Bad_def by auto
    from eB sub have "e \<in> Bad s \<sigma>" by auto
    with IB obtain e' where e'd: "e' \<in> dom (hp \<sigma>)"
      and e'R: "fst e' \<in> reach (marked \<sigma>) ((hp \<sigma>)(e := None))"
      and ne: "e' \<noteq> e" and eq: "hp \<sigma> e' = hp \<sigma> e"
      unfolding invB_def by blast
    have "e' \<in> dom (hp \<sigma>')" using e'd H by simp
    moreover have "fst e' \<in> reach (marked \<sigma>') ((hp \<sigma>')(e := None))"
    proof -
      have "reach (marked \<sigma>) ((hp \<sigma>)(e := None)) \<subseteq> reach (marked \<sigma>') ((hp \<sigma>')(e := None))"
        using reach_mono[OF M] H by simp
      with e'R show ?thesis by blast
    qed
    moreover have "hp \<sigma>' e' = hp \<sigma>' e" using eq H by simp
    ultimately show "\<exists>e'\<in>dom (hp \<sigma>'). fst e' \<in> reach (marked \<sigma>') ((hp \<sigma>')(e := None)) \<and> e' \<noteq> e \<and> hp \<sigma>' e' = hp \<sigma>' e"
      using ne by blast
  qed
  from C W show ?thesis unfolding invB_def by blast
qed

text \<open>Thesis: Both kinds of step preserve the invariant (the conclusion of Section 4.7).\<close>

corollary invB_step:
  fixes \<sigma> \<sigma>' :: "('a::finite,'i::finite) state"
  assumes "invB s \<sigma>"
    and "env_step s \<sigma> \<sigma>' \<and> s' = s \<or> step_Collector s \<sigma> s' \<sigma>'"
  shows "invB s' \<sigma>'"
  using assms lemma2_env_invB lemma4_prog_invB by blast

end
