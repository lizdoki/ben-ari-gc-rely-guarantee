(*  GC_Safety: Section 4.8.4 of the thesis -- safety.
      Lemma 15 / Lemma 16 -- the safety invariant inv-safe is preserved by
                             environment steps and by steps of Sweep
      Lemma 17 / Lemma 18 -- the Add-to-free invariant invA is preserved by
                             environment steps and by steps of Add-to-free
                             that do not change free
      Theorem 6           -- safety: a program step only frees garbage
      Lemma 19            -- a program step does not change any pointer out of
                             a reachable node, nor reachability
      Corollary 2         -- every program step satisfies guar-Collector, and
                             guar-Collector is transitive

    HOW TO READ THE LABELS.  Each definition and theorem below, or each group
    of them, has a text block saying how it relates to the thesis:
      "Thesis:"             it is that part of the thesis;
      "Beyond the thesis:"  the thesis states or argues it informally or not
                            at all; the label says which part of the thesis
                            it makes precise or supports;
      "Mechanisation only:" a helper needed only for the Isabelle proof.
    Section, lemma and theorem numbers are those of the thesis.  *)

theory GC_Safety
  imports GC_Mark GC_Unmark GC_Sweep
begin

section \<open>The safety invariant (Section 4.8.4)\<close>

text \<open>Thesis: inv-safe (Section 4.8.4): reach(roots, hp) \<subseteq> marked.\<close>

definition inv_safe :: "('a,'i) state \<Rightarrow> bool" where
  "inv_safe \<sigma> \<longleftrightarrow> reach (roots \<sigma>) (hp \<sigma>) \<subseteq> marked \<sigma>"

text \<open>Thesis: Lemma 15 (an environment step preserves the safety invariant):
    inv-safe(\<sigma>) \<and> rely-Collector(\<sigma>, \<sigma>') \<Rightarrow> inv-safe(\<sigma>').\<close>

theorem lemma15_env_inv_safe:
  assumes inv: "inv_state \<sigma>" and R: "rely_Collector s \<sigma> \<sigma>'" and "inv_safe \<sigma>"
  shows "inv_safe \<sigma>'"
proof -
  have "reach (roots \<sigma>') (hp \<sigma>') \<subseteq> reach (roots \<sigma>) (hp \<sigma>) \<union> free \<sigma>"
    using R unfolding rely_Collector_def by blast
  then show ?thesis
    using assms(3) inv_free_marked[OF inv] rely_marked_mono[OF R] unfolding inv_safe_def by blast
qed

text \<open>Thesis: Lemma 16 (a program step preserves the safety invariant):
    inv-safe(\<sigma>) \<and> guar-Sweep(\<sigma>, \<sigma>') \<Rightarrow> inv-safe(\<sigma>').\<close>

theorem lemma16_prog_inv_safe:
  assumes "guar_Sweep \<sigma> \<sigma>'" and "inv_safe \<sigma>"
  shows "inv_safe \<sigma>'"
proof -
  from assms(1) have R: "roots \<sigma>' = roots \<sigma>" and H: "hp \<sigma>' \<subseteq>\<^sub>m hp \<sigma>"
    and M: "marked \<sigma> \<subseteq> marked \<sigma>'" unfolding guar_Sweep_def by blast+
  have "reach (roots \<sigma>') (hp \<sigma>') \<subseteq> reach (roots \<sigma>) (hp \<sigma>)" using reach_map_le[OF H] R by simp
  with assms(2) M show ?thesis unfolding inv_safe_def by blast
qed

section \<open>The Add-to-free invariant (Section 4.8.4)\<close>

text \<open>Thesis: invA (defined in GC_Collector_Steps) holds in the first state of Add-to-free(x):
      by pre-Add-to-free, \<open>x \<notin> marked\<close>, and by inv-safe and the state
      invariant, \<open>reach(roots,hp) \<subseteq> marked\<close> and \<open>free \<subseteq> marked\<close>.\<close>

lemma invA_init:
  assumes "inv_state \<sigma>" and "inv_safe \<sigma>" and "x \<notin> marked \<sigma>"
  shows "invA x \<sigma>"
  using assms(2,3) inv_free_marked[OF assms(1)] unfolding inv_safe_def invA_def by blast

text \<open>Thesis: Lemma 17 (an environment step preserves the Add-to-free invariant):
    invA(x, \<sigma>) \<and> rely-Collector(\<sigma>, \<sigma>') \<Rightarrow> invA(x, \<sigma>').\<close>

theorem lemma17_env_invA:
  assumes R: "rely_Collector s \<sigma> \<sigma>'" and A: "invA x \<sigma>"
  shows "invA x \<sigma>'"
proof -
  from R have "reach (roots \<sigma>') (hp \<sigma>') \<subseteq> reach (roots \<sigma>) (hp \<sigma>) \<union> free \<sigma>"
    and "free \<sigma>' \<subseteq> free \<sigma>" unfolding rely_Collector_def by blast+
  with A show ?thesis unfolding invA_def by blast
qed

text \<open>Thesis: Lemma 18 (a program step of Add-to-free that does not change free
  preserves the Add-to-free invariant):
    invA(x, \<sigma>) \<and> guar-Add-to-free(\<sigma>, \<sigma>') \<and> free' = free \<Rightarrow> invA(x, \<sigma>').\<close>

theorem lemma18_prog_invA:
  assumes G: "guar_AddToFree x \<sigma> \<sigma>'" and F: "free \<sigma>' = free \<sigma>" and A: "invA x \<sigma>"
  shows "invA x \<sigma>'"
proof -
  from G have R: "roots \<sigma>' = roots \<sigma>" and H: "hp \<sigma>' \<subseteq>\<^sub>m hp \<sigma>"
    unfolding guar_AddToFree_def by blast+
  have "reach (roots \<sigma>') (hp \<sigma>') \<subseteq> reach (roots \<sigma>) (hp \<sigma>)" using reach_map_le[OF H] R by simp
  with A F show ?thesis unfolding invA_def by blast
qed

section \<open>Safety (Section 4.8.4)\<close>

text \<open>Thesis: Theorem 6.  A single program step only adds garbage to \<open>free\<close>.\<close>

theorem theorem6_safety:
  assumes S: "step_Collector s \<sigma> s' \<sigma>'"
  shows "free \<sigma>' - free \<sigma> \<subseteq> garbage \<sigma>"
proof -
  from step_Collector_cases[OF S] consider (Same) "free \<sigma>' = free \<sigma>"
    | (Add) x where "guar_AddToFree x \<sigma> \<sigma>'" "invA x \<sigma>"
    by blast
  then show ?thesis
  proof cases
    case Same
    then show ?thesis by simp
  next
    case (Add x)
    from Add(1) have "free \<sigma>' - free \<sigma> \<subseteq> {x}" unfolding guar_AddToFree_def by blast
    moreover from Add(2) have "x \<in> garbage \<sigma>" unfolding invA_def garbage_def by blast
    ultimately show ?thesis by blast
  qed
qed

text \<open>Thesis: Lemma 19.  A single program step does not change any pointer out of a
      reachable node (Add-to-free(x) removes only pointers of \<open>x\<close>, and \<open>x\<close> is
      unreachable by invA), nor which nodes are reachable.\<close>

theorem lemma19_edges_unchanged:
  assumes S: "step_Collector s \<sigma> s' \<sigma>'" and eR: "fst e \<in> reach (roots \<sigma>) (hp \<sigma>)"
  shows "hp \<sigma>' e = hp \<sigma> e"
proof -
  from step_Collector_cases[OF S] consider (Same) "hp \<sigma>' = hp \<sigma>"
    | (Add) x where "guar_AddToFree x \<sigma> \<sigma>'" "invA x \<sigma>"
    by blast
  then show ?thesis
  proof cases
    case Same
    then show ?thesis by simp
  next
    case (Add x)
    from Add(1) have H: "hp \<sigma>' \<subseteq>\<^sub>m hp \<sigma>" and D: "dom (hp \<sigma>) - dom (hp \<sigma>') \<subseteq> {x} \<times> UNIV"
      unfolding guar_AddToFree_def by blast+
    have "fst e \<noteq> x" using eR Add(2) unfolding invA_def by blast
    then have nx: "e \<notin> {x} \<times> UNIV" by (auto simp: mem_Times_iff)
    show ?thesis
    proof (cases "e \<in> dom (hp \<sigma>)")
      case True
      with D nx have "e \<in> dom (hp \<sigma>')" by blast
      with H show ?thesis unfolding map_le_def by blast
    next
      case False
      moreover have "e \<notin> dom (hp \<sigma>')" using False map_le_implies_dom_le[OF H] by blast
      ultimately show ?thesis by (simp add: domIff)
    qed
  qed
qed

text \<open>Thesis: Lemma 19 as stated in the thesis (a program step does not change
  reachability): step-Collector(\<sigma>, \<sigma>') \<Rightarrow> reach(roots, hp') = reach(roots, hp).\<close>

theorem lemma19_reach_unchanged:
  assumes S: "step_Collector s \<sigma> s' \<sigma>'"
  shows "reach (roots \<sigma>') (hp \<sigma>') = reach (roots \<sigma>) (hp \<sigma>)"
proof -
  from step_Collector_cases[OF S] consider (Same) "hp \<sigma>' = hp \<sigma>" "roots \<sigma>' = roots \<sigma>"
    | (Add) x where "guar_AddToFree x \<sigma> \<sigma>'" "invA x \<sigma>"
    by blast
  then show ?thesis
  proof cases
    case Same
    then show ?thesis by simp
  next
    case (Add x)
    from Add(1) have R: "roots \<sigma>' = roots \<sigma>" and H: "hp \<sigma>' \<subseteq>\<^sub>m hp \<sigma>"
      and D: "dom (hp \<sigma>) - dom (hp \<sigma>') \<subseteq> {x} \<times> UNIV" unfolding guar_AddToFree_def by blast+
    from Add(2) have xR: "x \<notin> reach (roots \<sigma>) (hp \<sigma>)" unfolding invA_def by blast
    have DU: "\<forall>e \<in> dom (hp \<sigma>) - dom (hp \<sigma>'). fst e \<notin> reach (roots \<sigma>) (hp \<sigma>)"
    proof
      fix e assume "e \<in> dom (hp \<sigma>) - dom (hp \<sigma>')"
      with D have "e \<in> {x} \<times> UNIV" by blast
      then have "fst e = x" by (auto simp: mem_Times_iff)
      with xR show "fst e \<notin> reach (roots \<sigma>) (hp \<sigma>)" by simp
    qed
    from reach_map_le_unreach[OF H DU] R show ?thesis by simp
  qed
qed

text \<open>Beyond the thesis: heaps that agree on the pointers out of the nodes
      reachable in one of them have the same reachable nodes.  With the last
      conjunct of guar-Collector, this gives reach(roots, hp') = reach(roots, hp).\<close>

lemma agree_reach:
  assumes E: "\<forall>e. fst e \<in> reach R h \<longrightarrow> h' e = h e"
  shows "reach R h' = reach R h"
proof
  show "reach R h' \<subseteq> reach R h"
  proof (rule reach_closed)
    show "R \<subseteq> reach R h" by (rule reach_refl)
  next
    fix y i b assume yR: "y \<in> reach R h" and yb: "h' (y,i) = Some b"
    have "h' (y,i) = h (y,i)" using E yR by simp
    with yb have "h (y,i) = Some b" by simp
    with yR show "b \<in> reach R h" by (rule reach_step)
  qed
next
  show "reach R h \<subseteq> reach R h'"
  proof -
    have "reach R h \<subseteq> reach R h \<inter> reach R h'"
    proof (rule reach_closed)
      show "R \<subseteq> reach R h \<inter> reach R h'"
        using reach_refl[of R h] reach_refl[of R h'] by simp
    next
      fix y i b assume yR: "y \<in> reach R h \<inter> reach R h'" and yb: "h (y,i) = Some b"
      from yR have y1: "y \<in> reach R h" and y2: "y \<in> reach R h'" by blast+
      have "h' (y,i) = h (y,i)" using E y1 by simp
      with yb have yb': "h' (y,i) = Some b" by simp
      from y1 yb have "b \<in> reach R h" by (rule reach_step)
      moreover from y2 yb' have "b \<in> reach R h'" by (rule reach_step)
      ultimately show "b \<in> reach R h \<inter> reach R h'" by blast
    qed
    then show ?thesis by blast
  qed
qed

text \<open>Beyond the thesis: guar-Collector keeps reach(roots, hp).  This is the
  conjunct reach(roots, hp') = reach(roots, hp) that the last conjunct of
  guar-Collector replaces (Section 4.4); it follows by agree_reach.\<close>

lemma guar_Collector_reach:
  assumes G: "guar_Collector \<sigma> \<sigma>'"
  shows "reach (roots \<sigma>') (hp \<sigma>') = reach (roots \<sigma>) (hp \<sigma>)"
proof -
  from G have R: "roots \<sigma>' = roots \<sigma>"
    and E: "\<forall>e. fst e \<in> reach (roots \<sigma>) (hp \<sigma>) \<longrightarrow> hp \<sigma>' e = hp \<sigma> e"
    unfolding guar_Collector_def by blast+
  from agree_reach[OF E] R show ?thesis by simp
qed

text \<open>Thesis: Corollary 2.  Every program step satisfies the guarantee of the
      Collector's specification, and that guarantee is transitive, so it holds
      over any sequence of consecutive program steps.\<close>

theorem corollary2_step_guar:
  fixes \<sigma> \<sigma>' :: "('a,'i) state"
  assumes S: "step_Collector s \<sigma> s' \<sigma>'"
  shows "guar_Collector \<sigma> \<sigma>'"
proof -
  from step_Collector_cases[OF S] have F: "free \<sigma> \<subseteq> free \<sigma>'" and R: "roots \<sigma>' = roots \<sigma>"
    unfolding guar_AddToFree_def by blast+
  have E: "\<forall>e. fst e \<in> reach (roots \<sigma>) (hp \<sigma>) \<longrightarrow> hp \<sigma>' e = hp \<sigma> e"
  proof (intro allI impI)
    fix e :: "'a \<times> 'i" assume "fst e \<in> reach (roots \<sigma>) (hp \<sigma>)"
    then show "hp \<sigma>' e = hp \<sigma> e" by (rule lemma19_edges_unchanged[OF S])
  qed
  show ?thesis unfolding guar_Collector_def
    using F R E theorem6_safety[OF S] by blast
qed

text \<open>Thesis: Corollary 2, second half: guar-Collector holds over consecutive
  steps transitively.\<close>

theorem corollary2_guar_trans:
  fixes \<sigma> \<sigma>' \<sigma>'' :: "('a,'i) state"
  assumes G1: "guar_Collector \<sigma> \<sigma>'" and G2: "guar_Collector \<sigma>' \<sigma>''"
  shows "guar_Collector \<sigma> \<sigma>''"
proof -
  from G1 have R1: "roots \<sigma>' = roots \<sigma>" and F1: "free \<sigma> \<subseteq> free \<sigma>'"
    and N1: "free \<sigma>' - free \<sigma> \<subseteq> garbage \<sigma>"
    and E1: "\<forall>e. fst e \<in> reach (roots \<sigma>) (hp \<sigma>) \<longrightarrow> hp \<sigma>' e = hp \<sigma> e"
    unfolding guar_Collector_def by blast+
  from G2 have R2: "roots \<sigma>'' = roots \<sigma>'" and F2: "free \<sigma>' \<subseteq> free \<sigma>''"
    and N2: "free \<sigma>'' - free \<sigma>' \<subseteq> garbage \<sigma>'"
    and E2: "\<forall>e. fst e \<in> reach (roots \<sigma>') (hp \<sigma>') \<longrightarrow> hp \<sigma>'' e = hp \<sigma>' e"
    unfolding guar_Collector_def by blast+
  have RE1: "reach (roots \<sigma>') (hp \<sigma>') = reach (roots \<sigma>) (hp \<sigma>)" by (rule guar_Collector_reach[OF G1])
  have N: "free \<sigma>'' - free \<sigma> \<subseteq> garbage \<sigma>"
  proof
    fix y assume y: "y \<in> free \<sigma>'' - free \<sigma>"
    show "y \<in> garbage \<sigma>"
    proof (cases "y \<in> free \<sigma>'")
      case True
      with y N1 show ?thesis by blast
    next
      case False
      with y N2 have "y \<notin> free \<sigma>' \<union> reach (roots \<sigma>') (hp \<sigma>')" unfolding garbage_def by blast
      then have "y \<notin> free \<sigma>' \<union> reach (roots \<sigma>) (hp \<sigma>)" unfolding RE1 .
      with F1 show ?thesis unfolding garbage_def by blast
    qed
  qed
  have R: "roots \<sigma>'' = roots \<sigma>" by (rule trans[OF R2 R1])
  have F: "free \<sigma> \<subseteq> free \<sigma>''" using F1 F2 by blast
  have E: "\<forall>e. fst e \<in> reach (roots \<sigma>) (hp \<sigma>) \<longrightarrow> hp \<sigma>'' e = hp \<sigma> e"
  proof (intro allI impI)
    fix e :: "'a \<times> 'i" assume eR: "fst e \<in> reach (roots \<sigma>) (hp \<sigma>)"
    then have "fst e \<in> reach (roots \<sigma>') (hp \<sigma>')" using RE1 by simp
    with E2 have "hp \<sigma>'' e = hp \<sigma>' e" by blast
    also have "\<dots> = hp \<sigma> e" using E1 eR by blast
    finally show "hp \<sigma>'' e = hp \<sigma> e" .
  qed
  from R F N E show ?thesis unfolding guar_Collector_def by blast
qed

text \<open>Mechanisation only: guar-Collector is reflexive.\<close>

lemma guar_Collector_refl: "guar_Collector \<sigma> \<sigma>"
  unfolding guar_Collector_def by simp

end
