(*  GC_Collector_Post: Section 4.8.5 of the thesis -- the Collector's post
    condition.
      Sublemma 1 -- after Unmark, nothing reachable from the old free or
                    reachable region is old garbage
      Lemma 20   -- upper bound of the region reachable from marked nodes
      Theorem 7  -- post-Collector: all garbage present at the start of a
                    cycle is freed during it

    HOW TO READ THE LABELS.  Each definition and theorem below, or each group
    of them, has a text block saying how it relates to the thesis:
      "Thesis:"             it is that part of the thesis;
      "Beyond the thesis:"  the thesis states or argues it informally or not
                            at all; the label says which part of the thesis
                            it makes precise or supports;
      "Mechanisation only:" a helper needed only for the Isabelle proof.
    Section, lemma and theorem numbers are those of the thesis.  *)

theory GC_Collector_Post
  imports GC_Safety GC_Unmark
begin

section \<open>The Collector's post condition (Section 4.8.5)\<close>

text \<open>Thesis: Sublemma 1 (used by Lemma 20), single-step form: an environment step
      never creates a pointer from the free or reachable region into (old)
      garbage.\<close>

lemma sublemma1_step:
  assumes inv: "inv_state \<sigma>" and R: "rely_Collector s \<sigma> \<sigma>'"
    and x: "x \<in> free \<sigma> \<union> reach (roots \<sigma>) (hp \<sigma>)" and hb: "hp \<sigma>' (x,i) = Some b"
  shows "b \<notin> garbage \<sigma>"
proof (cases "hp \<sigma>' (x,i) = hp \<sigma> (x,i)")
  case True
  with hb have h: "hp \<sigma> (x,i) = Some b" by simp
  from x show ?thesis
  proof
    assume "x \<in> free \<sigma>"
    with h inv have False unfolding inv_state_def by (auto simp: domIff)
    then show ?thesis ..
  next
    assume "x \<in> reach (roots \<sigma>) (hp \<sigma>)"
    from this h have "b \<in> reach (roots \<sigma>) (hp \<sigma>)" by (rule reach_step)
    then show ?thesis unfolding garbage_def by blast
  qed
next
  case False
  then show ?thesis using R hb unfolding rely_Collector_def by blast
qed

text \<open>Thesis: Sublemma 1: with \<sigma> and \<sigma>' the initial and final states of Unmark,
    reach(free \<union> reach(roots, hp), hp') \<subseteq> free \<union> reach(roots, hp).
  Here the property of Unmark used is no_new_ptr (GC_Unmark).\<close>

theorem sublemma1_closure:
  assumes "no_new_ptr \<sigma> \<sigma>'"
  shows "reach (free \<sigma> \<union> reach (roots \<sigma>) (hp \<sigma>)) (hp \<sigma>') \<subseteq> free \<sigma> \<union> reach (roots \<sigma>) (hp \<sigma>)"
proof (rule reach_closed[OF subset_refl])
  fix x i b assume xR: "x \<in> free \<sigma> \<union> reach (roots \<sigma>) (hp \<sigma>)" and hb: "hp \<sigma>' (x,i) = Some b"
  from assms xR have A: "\<forall>i b. hp \<sigma>' (x,i) = Some b \<longrightarrow> b \<in> free \<sigma> \<union> reach (roots \<sigma>) (hp \<sigma>)"
    unfolding no_new_ptr_def by (rule bspec)
  show "b \<in> free \<sigma> \<union> reach (roots \<sigma>) (hp \<sigma>)" by (rule A[rule_format, OF hb])
qed

text \<open>Thesis: Lemma 20 (upper bound of the region reachable from marked nodes):
    post-Unmark(\<sigma>, \<sigma>') \<Rightarrow> reach(marked', hp') \<subseteq> free \<union> reach(roots, hp),
  with what Unmark guarantees about pointers (no_new_ptr).\<close>

theorem lemma20_reach_marked_bound:
  assumes "post_Unmark \<sigma> \<sigma>'" and "no_new_ptr \<sigma> \<sigma>'"
  shows "reach (marked \<sigma>') (hp \<sigma>') \<subseteq> free \<sigma> \<union> reach (roots \<sigma>) (hp \<sigma>)"
proof -
  have "marked \<sigma>' \<subseteq> free \<sigma> \<union> reach (roots \<sigma>) (hp \<sigma>)"
    using assms(1) unfolding post_Unmark_def garbage_def by blast
  then have "reach (marked \<sigma>') (hp \<sigma>') \<subseteq> reach (free \<sigma> \<union> reach (roots \<sigma>) (hp \<sigma>)) (hp \<sigma>')"
    by (rule reach_mono)
  with sublemma1_closure[OF assms(2)] show ?thesis by blast
qed

text \<open>Thesis: post-Collector (Section 4.4): garbage \<subseteq> \<Union>F, where F is the set of
  values free has taken during the cycle (free~).\<close>

definition post_Collector :: "('a,'i) state \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "post_Collector \<sigma> F \<longleftrightarrow> garbage \<sigma> \<subseteq> \<Union>F"

text \<open>Theorem 7.  \<open>\<sigma>U\<close>, \<open>\<sigma>M\<close>, \<open>\<sigma>S\<close> are the states at the start of Unmark, Mark and
      Sweep; \<open>F\<close> is the set of values taken by \<open>free\<close> during Sweep, and
      \<open>F \<subseteq> Fcycle\<close> for the values over the whole cycle.\<close>

theorem theorem7_post_Collector:
  assumes U: "post_Unmark \<sigma>U \<sigma>M" and NP: "no_new_ptr \<sigma>U \<sigma>M"
    and Mk: "post_Mark \<sigma>M sS \<sigma>S"
    and Sw: "post_Sweep \<sigma>S F \<sigma>U'"
    and FF: "F \<subseteq> Fcycle"
  shows "post_Collector \<sigma>U Fcycle"
proof -
  have 1: "reach (marked \<sigma>M) (hp \<sigma>M) \<subseteq> free \<sigma>U \<union> reach (roots \<sigma>U) (hp \<sigma>U)"
    by (rule lemma20_reach_marked_bound[OF U NP])
  have 2: "marked \<sigma>S \<subseteq> reach (marked \<sigma>M) (hp \<sigma>M)" using Mk unfolding post_Mark_def by blast
  have "garbage \<sigma>U \<inter> marked \<sigma>S = {}" using 1 2 unfolding garbage_def by blast
  then have "garbage \<sigma>U \<subseteq> UNIV - marked \<sigma>S" by blast
  with Sw have "\<forall>x\<in>garbage \<sigma>U. \<exists>f\<in>F. x \<in> f" unfolding post_Sweep_def by blast
  with FF show ?thesis unfolding post_Collector_def by blast
qed

end
