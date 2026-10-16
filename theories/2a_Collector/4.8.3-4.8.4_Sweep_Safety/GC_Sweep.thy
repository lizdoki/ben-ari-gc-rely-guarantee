(*  GC_Sweep: Section 4.8.3 of the thesis -- the lemmas and theorems of
    Sweep.
      Lemma 14 / Theorem 5 -- so-far transitive and well-founded, post
                              condition
    Possible values of free over a segment of the execution are represented
    by a set of sets F (the values that free took); GC_Sweep_Sat supplies it
    from the history variable Fv (pv).  The proofs that Add-to-free and
    Sweep meet their specifications use the safety invariants of Section
    4.8.4, so they are in GC_Sweep_Sat, after GC_Safety.

    HOW TO READ THE LABELS.  Each definition and theorem below, or each group
    of them, has a text block saying how it relates to the thesis:
      "Thesis:"             it is that part of the thesis;
      "Beyond the thesis:"  the thesis states or argues it informally or not
                            at all; the label says which part of the thesis
                            it makes precise or supports;
      "Mechanisation only:" a helper needed only for the Isabelle proof.
    Section, lemma and theorem numbers are those of the thesis.  *)

theory GC_Sweep
  imports GC_Collector_Steps
begin

section \<open>Sweep (Section 4.8.3, Algorithm 9)\<close>

text \<open>Thesis: so-farS, the so-far relation of the Sweep loop (Section 4.8.3);
  F is the set of values free has taken (free~).\<close>

definition so_farS :: "'a set \<Rightarrow> ('a,'i) state \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "so_farS c \<sigma> F c' \<sigma>' \<longleftrightarrow> c \<subset> c' \<and> marked \<sigma> \<subseteq> marked \<sigma>' \<and>
     (\<forall>x \<in> c'. x \<notin> marked \<sigma> \<longrightarrow> (\<exists>f\<in>F. x \<in> f) \<and> x \<in> marked \<sigma>') \<and>
     (\<forall>x \<in> UNIV - c'. x \<notin> marked \<sigma> \<longrightarrow> x \<notin> marked \<sigma>')"

text \<open>Thesis: Lemma 14, first half: so-farS is transitive.\<close>

theorem lemma14_so_farS_trans:
  assumes "so_farS c \<sigma> F c' \<sigma>'" and "so_farS c' \<sigma>' F' c'' \<sigma>''"
  shows "so_farS c \<sigma> (F \<union> F') c'' \<sigma>''"
proof -
  note T1 = assms(1)[unfolded so_farS_def] and T2 = assms(2)[unfolded so_farS_def]
  have 1: "c \<subset> c'" "c' \<subset> c''" "marked \<sigma> \<subseteq> marked \<sigma>'" "marked \<sigma>' \<subseteq> marked \<sigma>''"
    by (rule T1[THEN conjunct1], rule T2[THEN conjunct1],
        rule T1[THEN conjunct2, THEN conjunct1], rule T2[THEN conjunct2, THEN conjunct1])
  have 2: "\<forall>x \<in> c'. x \<notin> marked \<sigma> \<longrightarrow> (\<exists>f\<in>F. x \<in> f) \<and> x \<in> marked \<sigma>'"
    by (rule T1[THEN conjunct2, THEN conjunct2, THEN conjunct1])
  have 3: "\<forall>x \<in> UNIV - c'. x \<notin> marked \<sigma> \<longrightarrow> x \<notin> marked \<sigma>'"
    by (rule T1[THEN conjunct2, THEN conjunct2, THEN conjunct2])
  have 4: "\<forall>x \<in> c''. x \<notin> marked \<sigma>' \<longrightarrow> (\<exists>f\<in>F'. x \<in> f) \<and> x \<in> marked \<sigma>''"
    by (rule T2[THEN conjunct2, THEN conjunct2, THEN conjunct1])
  have 5: "\<forall>x \<in> UNIV - c''. x \<notin> marked \<sigma>' \<longrightarrow> x \<notin> marked \<sigma>''"
    by (rule T2[THEN conjunct2, THEN conjunct2, THEN conjunct2])
  have cc: "c \<subset> c''" using 1(1) 1(2) by (rule psubset_trans)
  have M: "marked \<sigma> \<subseteq> marked \<sigma>''" using 1(3) 1(4) by blast
  have A: "\<forall>x \<in> c''. x \<notin> marked \<sigma> \<longrightarrow> (\<exists>f\<in>F \<union> F'. x \<in> f) \<and> x \<in> marked \<sigma>''"
  proof (intro ballI impI)
    fix x assume x: "x \<in> c''" and xM: "x \<notin> marked \<sigma>"
    show "(\<exists>f\<in>F \<union> F'. x \<in> f) \<and> x \<in> marked \<sigma>''"
    proof (cases "x \<in> c'")
      case True
      with xM 2 have "(\<exists>f\<in>F. x \<in> f) \<and> x \<in> marked \<sigma>'" by blast
      with 1(4) show ?thesis by blast
    next
      case False
      with xM 3 have "x \<notin> marked \<sigma>'" by blast
      with x 4 show ?thesis by blast
    qed
  qed
  have B: "\<forall>x \<in> UNIV - c''. x \<notin> marked \<sigma> \<longrightarrow> x \<notin> marked \<sigma>''"
  proof (intro ballI impI)
    fix x assume x: "x \<in> UNIV - c''" and xM: "x \<notin> marked \<sigma>"
    have "x \<notin> c'" using x 1(2) by blast
    with xM 3 have "x \<notin> marked \<sigma>'" by blast
    with x 5 show "x \<notin> marked \<sigma>''" by blast
  qed
  from cc M A B show ?thesis unfolding so_farS_def by blast
qed

text \<open>Thesis: Lemma 14, second half: so-farS is well-founded, as in Lemma 13.\<close>

theorem lemma14_so_farS_wf:
  "wf {((c',\<sigma>'),(c,\<sigma>)) | c \<sigma> c' \<sigma>'. so_farS c \<sigma> F c' (\<sigma>' :: ('a::finite,'i) state)}"
  by (rule wf_psubset_rel[where F = fst]) (auto simp: so_farS_def)

text \<open>Thesis: post-Sweep (Section 4.8.3): every node unmarked at the start was
  in free at some point (in some f \<in> free~).\<close>

definition post_Sweep :: "('a,'i) state \<Rightarrow> 'a set set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "post_Sweep \<sigma> F \<sigma>' \<longleftrightarrow> (\<forall>x \<in> UNIV - marked \<sigma>. \<exists>f\<in>F. x \<in> f)"

text \<open>Thesis: Theorem 5 (Sweep post condition):
    consid' = Addr \<and> so-farS(\<sigma>, \<sigma>') \<Rightarrow> post-Sweep(\<sigma>, \<sigma>').\<close>

theorem theorem5_post_Sweep:
  assumes "so_farS {} \<sigma> F UNIV \<sigma>'"
  shows "post_Sweep \<sigma> F \<sigma>'"
  using assms unfolding so_farS_def post_Sweep_def by auto

end
