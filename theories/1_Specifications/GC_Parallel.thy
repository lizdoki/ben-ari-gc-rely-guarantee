(*  GC_Parallel: Collector \<parallel> Mutator is correct, for any Collector and any
    Mutator that meet their specifications (Section 4.5.5).

    This is the top-level argument of Chapter 4 (Part 1 of the
    mechanisation).  It uses only the specifications (GC_Collector_Spec,
    GC_Mutator_Spec), not the code:
      - the Mutator's obligation towards the Collector, the implication
        displayed in Section 4.5.5 (section_455_obligation);
      - the side conditions of the parallel rule, with consistent(s, \<sigma>) as
        the coupling predicate (initially, side_C, side_M);
      - the parallel rule (rg_parallel, RG_Semantics), applied to any process
        C1 meeting the Collector's specification and any process C2 meeting
        the Mutator's (Collector_par_Mutator_abstract).
    Part 2 (GC_Collector, GC_Mutator) then proves that the code of Appendix C
    and of Algorithm 12 meets the two specifications, and Part 3 (GC_System)
    applies this theorem to it.

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
      consistent(s, \<sigma>) (Section 4.5.5)                  consistent
      the implication of 4.5.5: Mutator steps          section_455_obligation,
        satisfy rely-Collector, keep consistency         side_M
      item 2 at the end of 4.5.5: Collector steps      collector_keeps_
        preserve consistency (Lemma 3)                   consistent, side_C
      item 1 at the end of 4.5.5: holds initially      initially
      Collector \<parallel> Mutator is correct, for any         Collector_par_Mutator_
        Collector and Mutator meeting the specs          abstract
      every Collector step satisfies guar-Collector,   collector_step,
        so frees only garbage (Theorem 6)                collector_safe
      every Mutator step satisfies guar-Mutator        mutator_step
        and rely-Collector
      consistent(s, \<sigma>) and both post conditions      invariants
        hold throughout                                                     *)

theory GC_Parallel
  imports GC_Collector_Spec GC_Mutator_Spec
begin

section \<open>The Mutator's obligation towards the Collector (Section 4.5.5)\<close>

text \<open>Thesis: consistent(s, \<sigma>) \<triangleq> Bad(s, \<sigma>) \<subseteq> new-risk (Section 4.5.5),
  relating the Collector's private s to the Mutator's private new-risk N.\<close>

definition consistent :: "('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> bool" where
  "consistent s \<sigma> N \<longleftrightarrow> Bad s \<sigma> \<subseteq> N"

text \<open>Mechanisation only: if Bad is empty and one edge changes, only that edge
  can be bad afterwards.  Used in the heap-update cases below.\<close>

lemma Bad_upd_edge:
  assumes "Bad s \<sigma> = {}" and "\<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)(e := v)\<rparr>"
  shows "Bad s \<sigma>' \<subseteq> {e}"
  using assms unfolding Bad_def by (auto split: if_splits)

text \<open>Thesis: the implication displayed in Section 4.5.5, for every s:
    consistent(s, \<sigma>) \<and> guar-Mutator(\<sigma>, \<sigma>')
       \<Rightarrow> rely-Collector(\<sigma>, \<sigma>') \<and> consistent(s, \<sigma>'),
  together with Assumption 1 for the step and inv-\<Sigma> (env_step bundles the
  three).  It mentions only the shared state, s and new-risk.  The thesis
  argues it informally; the proof here has one case per atomic step.  In the
  heap-update cases, conjuncts (3), (4.1), (4.2) and (4.3) of rely-Collector
  are shown one by one, and (1), (2) and "roots unchanged" are closed by simp
  at the qed.\<close>

theorem section_455_obligation:
  fixes \<sigma> \<sigma>' :: "('a,'i) state"
  assumes C: "consistent s \<sigma> N" and G: "guar_Mutator N \<sigma> N' \<sigma>'"
  shows "env_step s \<sigma> \<sigma>' \<and> consistent s \<sigma>' N'"
proof -
  from G have inv: "inv_state \<sigma>" and inv': "inv_state \<sigma>'"
    and ex0: "(\<sigma>' = \<sigma> \<and> N' = N) \<or>
              (\<exists>a i b. g_Redirect_hp a i b N \<sigma> N' \<sigma>' \<or> g_Redirect_mk a i b N \<sigma> N' \<sigma>' \<or>
                    g_Malloc_hp a i b N \<sigma> N' \<sigma>' \<or> g_Malloc_fr a i b N \<sigma> N' \<sigma>' \<or> g_Zap a i N \<sigma> N' \<sigma>')"
    unfolding guar_Mutator_def by simp_all
  show ?thesis using ex0
  proof
    assume "\<sigma>' = \<sigma> \<and> N' = N"
    then have s': "\<sigma>' = \<sigma>" and n': "N' = N" by simp_all
    have "rely_Collector s \<sigma> \<sigma>'" using s' rely_Collector_refl by simp
    moreover have "atomic \<sigma> \<sigma>'" using s' unfolding atomic_def by simp
    moreover have "consistent s \<sigma>' N'" using C s' n' by simp
    ultimately show ?thesis using inv inv' unfolding env_step_def by blast
  next
  assume ex: "\<exists>a i b. g_Redirect_hp a i b N \<sigma> N' \<sigma>' \<or> g_Redirect_mk a i b N \<sigma> N' \<sigma>' \<or>
                    g_Malloc_hp a i b N \<sigma> N' \<sigma>' \<or> g_Malloc_fr a i b N \<sigma> N' \<sigma>' \<or> g_Zap a i N \<sigma> N' \<sigma>'"
  from ex obtain a i b where
    gcase: "g_Redirect_hp a i b N \<sigma> N' \<sigma>' \<or> g_Redirect_mk a i b N \<sigma> N' \<sigma>' \<or>
            g_Malloc_hp a i b N \<sigma> N' \<sigma>' \<or> g_Malloc_fr a i b N \<sigma> N' \<sigma>' \<or> g_Zap a i N \<sigma> N' \<sigma>'"
    by blast
  have RAC: "rely_Collector s \<sigma> \<sigma>' \<and> atomic \<sigma> \<sigma>' \<and> consistent s \<sigma>' N'"
    using gcase
  proof (elim disjE)
    assume g: "g_Redirect_hp a i b N \<sigma> N' \<sigma>'"
    then have aR: "a \<in> reach (roots \<sigma>) (hp \<sigma>)" and bR: "b \<in> reach (roots \<sigma>) (hp \<sigma>)"
      and disj: "free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}" and nr0: "N = {}"
      and s': "\<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((a,i) \<mapsto> b)\<rparr>"
      and nr': "N' = (if b \<in> marked \<sigma> then {} else {(a,i)})"
      unfolding g_Redirect_hp_def by simp_all
    have BE: "Bad s \<sigma> = {}" using C nr0 unfolding consistent_def by simp
    let ?h = "(hp \<sigma>)((a,i) \<mapsto> b)"
    have Rsub: "reach (roots \<sigma>) ?h \<subseteq> reach (roots \<sigma>) (hp \<sigma>)" by (rule reach_redirect_subset[OF bR])
    have rely: "rely_Collector s \<sigma> \<sigma>'"
      unfolding rely_Collector_def
    proof (intro conjI)
      show "reach (roots \<sigma>') (hp \<sigma>') - reach (roots \<sigma>) (hp \<sigma>) \<subseteq> free \<sigma>"
        using Rsub s' by auto
    next
      show "\<forall>e. hp \<sigma>' e \<noteq> hp \<sigma> e \<longrightarrow>
              fst e \<notin> garbage \<sigma> \<and> (\<forall>b'. hp \<sigma>' e = Some b' \<longrightarrow> b' \<notin> garbage \<sigma>)"
      proof (intro allI impI)
        fix e assume "hp \<sigma>' e \<noteq> hp \<sigma> e"
        then have "e = (a,i)" using s' by (auto split: if_splits)
        then show "fst e \<notin> garbage \<sigma> \<and> (\<forall>b'. hp \<sigma>' e = Some b' \<longrightarrow> b' \<notin> garbage \<sigma>)"
          using s' aR bR unfolding garbage_def by auto
      qed
    next
      show "\<forall>e. hp \<sigma>' e \<noteq> hp \<sigma> e \<and> marked \<sigma>' = marked \<sigma> \<longrightarrow> Bad s \<sigma> = {}"
        using BE by blast
    next
      show "\<forall>e. hp \<sigma>' e \<noteq> hp \<sigma> e \<and> free \<sigma>' = free \<sigma> \<longrightarrow> free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}"
        using disj by blast
    qed (use s' in simp_all)
    have atom: "atomic \<sigma> \<sigma>'"
      unfolding atomic_def using s' by (auto intro!: exI[where x="(a,i)"])
    have cons': "consistent s \<sigma>' N'"
    proof -
      have "Bad s \<sigma>' \<subseteq> {(a,i)}" by (rule Bad_upd_edge[OF BE s'])
      moreover have "b \<in> marked \<sigma> \<Longrightarrow> (a,i) \<notin> Bad s \<sigma>'" using s' unfolding Bad_def by auto
      ultimately show ?thesis using nr' unfolding consistent_def by auto
    qed
    from rely atom cons' show ?thesis by blast
  next
    assume g: "g_Redirect_mk a i b N \<sigma> N' \<sigma>'"
    then have hab: "hp \<sigma> (a,i) = Some b" and bR: "b \<in> reach (roots \<sigma>) (hp \<sigma>)"
      and nrs: "N \<subseteq> {(a,i)}" and s': "\<sigma>' = \<sigma>\<lparr>marked := marked \<sigma> \<union> {b}\<rparr>"
      and nr': "N' = {}"
      unfolding g_Redirect_mk_def by simp_all
    have rely: "rely_Collector s \<sigma> \<sigma>'"
      unfolding rely_Collector_def using s' bR by auto
    have atom: "atomic \<sigma> \<sigma>'"
    proof (cases "b \<in> marked \<sigma>")
      case True then show ?thesis using s' unfolding atomic_def by (simp add: insert_absorb)
    next
      case False
      then have "(marked \<sigma> - marked \<sigma>') \<union> (marked \<sigma>' - marked \<sigma>) = {b}" using s' by auto
      then show ?thesis using s' unfolding atomic_def by simp
    qed
    have cons': "consistent s \<sigma>' N'"
    proof -
      have "Bad s \<sigma>' = {}"
      proof (rule ccontr)
        assume "Bad s \<sigma>' \<noteq> {}"
        then obtain e c where es: "e \<in> s" and ec: "hp \<sigma> e = Some c" and cM: "c \<notin> marked \<sigma> \<union> {b}"
          using s' unfolding Bad_def by auto
        then have "e \<in> Bad s \<sigma>" unfolding Bad_def by auto
        with C have "e \<in> N" unfolding consistent_def by blast
        with nrs have "e = (a,i)" by blast
        with ec hab cM show False by auto
      qed
      then show ?thesis using nr' unfolding consistent_def by simp
    qed
    from rely atom cons' show ?thesis by blast
  next
    assume g: "g_Malloc_hp a i b N \<sigma> N' \<sigma>'"
    then have aR: "a \<in> reach (roots \<sigma>) (hp \<sigma>)" and bf: "b \<in> free \<sigma>"
      and disj: "free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}" and nr0: "N = {}"
      and s': "\<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((a,i) \<mapsto> b)\<rparr>" and nr': "N' = {}"
      unfolding g_Malloc_hp_def by simp_all
    have BE: "Bad s \<sigma> = {}" using C nr0 unfolding consistent_def by simp
    let ?h = "(hp \<sigma>)((a,i) \<mapsto> b)"
    have bleaf: "\<forall>j. hp \<sigma> (b,j) = None" using inv bf unfolding inv_state_def by (auto simp: domIff)
    have Rsub: "reach (roots \<sigma>) ?h \<subseteq> reach (roots \<sigma>) (hp \<sigma>) \<union> {b}"
      by (rule reach_redirect_leaf_subset[OF bleaf])
    have bM: "b \<in> marked \<sigma>" using inv bf unfolding inv_state_def by blast
    have rely: "rely_Collector s \<sigma> \<sigma>'"
      unfolding rely_Collector_def
    proof (intro conjI)
      show "reach (roots \<sigma>') (hp \<sigma>') - reach (roots \<sigma>) (hp \<sigma>) \<subseteq> free \<sigma>"
        using Rsub s' bf by auto
    next
      show "\<forall>e. hp \<sigma>' e \<noteq> hp \<sigma> e \<longrightarrow>
              fst e \<notin> garbage \<sigma> \<and> (\<forall>b'. hp \<sigma>' e = Some b' \<longrightarrow> b' \<notin> garbage \<sigma>)"
      proof (intro allI impI)
        fix e assume "hp \<sigma>' e \<noteq> hp \<sigma> e"
        then have "e = (a,i)" using s' by (auto split: if_splits)
        then show "fst e \<notin> garbage \<sigma> \<and> (\<forall>b'. hp \<sigma>' e = Some b' \<longrightarrow> b' \<notin> garbage \<sigma>)"
          using s' aR bf unfolding garbage_def by auto
      qed
    next
      show "\<forall>e. hp \<sigma>' e \<noteq> hp \<sigma> e \<and> marked \<sigma>' = marked \<sigma> \<longrightarrow> Bad s \<sigma> = {}"
        using BE by blast
    next
      show "\<forall>e. hp \<sigma>' e \<noteq> hp \<sigma> e \<and> free \<sigma>' = free \<sigma> \<longrightarrow> free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}"
        using disj by blast
    qed (use s' in simp_all)
    have atom: "atomic \<sigma> \<sigma>'"
      unfolding atomic_def using s' by (auto intro!: exI[where x="(a,i)"])
    have cons': "consistent s \<sigma>' N'"
    proof -
      have "Bad s \<sigma>' \<subseteq> {(a,i)}" by (rule Bad_upd_edge[OF BE s'])
      moreover have "(a,i) \<notin> Bad s \<sigma>'" using s' bM unfolding Bad_def by auto
      ultimately have "Bad s \<sigma>' = {}" by blast
      then show ?thesis unfolding consistent_def by simp
    qed
    from rely atom cons' show ?thesis by blast
  next
    assume g: "g_Malloc_fr a i b N \<sigma> N' \<sigma>'"
    then have bf: "b \<in> free \<sigma>" and nr0: "N = {}"
      and s': "\<sigma>' = \<sigma>\<lparr>free := free \<sigma> - {b}\<rparr>" and nr': "N' = {}"
      unfolding g_Malloc_fr_def by simp_all
    have rely: "rely_Collector s \<sigma> \<sigma>'"
      unfolding rely_Collector_def using s' by auto
    have atom: "atomic \<sigma> \<sigma>'"
    proof -
      have "(free \<sigma> - free \<sigma>') \<union> (free \<sigma>' - free \<sigma>) = {b}" using s' bf by auto
      then show ?thesis using s' unfolding atomic_def by simp
    qed
    have cons': "consistent s \<sigma>' N'"
      using C nr0 nr' s' unfolding consistent_def Bad_def by simp
    from rely atom cons' show ?thesis by blast
  next
    assume g: "g_Zap a i N \<sigma> N' \<sigma>'"
    then have aR: "a \<in> reach (roots \<sigma>) (hp \<sigma>)"
      and disj: "free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}" and nr0: "N = {}"
      and s': "\<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((a,i) := None)\<rparr>" and nr': "N' = {}"
      unfolding g_Zap_def by simp_all
    have BE: "Bad s \<sigma> = {}" using C nr0 unfolding consistent_def by simp
    let ?h = "(hp \<sigma>)((a,i) := None)"
    have Rsub: "reach (roots \<sigma>) ?h \<subseteq> reach (roots \<sigma>) (hp \<sigma>)" by (rule reach_del)
    have rely: "rely_Collector s \<sigma> \<sigma>'"
      unfolding rely_Collector_def
    proof (intro conjI)
      show "reach (roots \<sigma>') (hp \<sigma>') - reach (roots \<sigma>) (hp \<sigma>) \<subseteq> free \<sigma>"
        using Rsub s' by auto
    next
      show "\<forall>e. hp \<sigma>' e \<noteq> hp \<sigma> e \<longrightarrow>
              fst e \<notin> garbage \<sigma> \<and> (\<forall>b'. hp \<sigma>' e = Some b' \<longrightarrow> b' \<notin> garbage \<sigma>)"
      proof (intro allI impI)
        fix e assume "hp \<sigma>' e \<noteq> hp \<sigma> e"
        then have "e = (a,i)" using s' by (auto split: if_splits)
        then show "fst e \<notin> garbage \<sigma> \<and> (\<forall>b'. hp \<sigma>' e = Some b' \<longrightarrow> b' \<notin> garbage \<sigma>)"
          using s' aR unfolding garbage_def by auto
      qed
    next
      show "\<forall>e. hp \<sigma>' e \<noteq> hp \<sigma> e \<and> marked \<sigma>' = marked \<sigma> \<longrightarrow> Bad s \<sigma> = {}"
        using BE by blast
    next
      show "\<forall>e. hp \<sigma>' e \<noteq> hp \<sigma> e \<and> free \<sigma>' = free \<sigma> \<longrightarrow> free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}"
        using disj by blast
    qed (use s' in simp_all)
    have atom: "atomic \<sigma> \<sigma>'"
      unfolding atomic_def using s' by (auto intro!: exI[where x="(a,i)"])
    have cons': "consistent s \<sigma>' N'"
    proof -
      have "Bad s \<sigma>' \<subseteq> {(a,i)}" by (rule Bad_upd_edge[OF BE s'])
      moreover have "(a,i) \<notin> Bad s \<sigma>'" using s' unfolding Bad_def by auto
      ultimately have "Bad s \<sigma>' = {}" by blast
      then show ?thesis unfolding consistent_def by simp
    qed
    from rely atom cons' show ?thesis by blast
  qed
  from RAC inv inv' show ?thesis unfolding env_step_def by blast
  qed
qed

section \<open>How the two specifications fit together (Section 4.5.5)\<close>

text \<open>Thesis: item 2 at the end of Section 4.5.5: a Collector step keeps
  consistent(s, \<sigma>), since it does not increase Bad (Lemma 3) and cannot
  change new-risk.\<close>

lemma collector_keeps_consistent:
  assumes "consistent s \<sigma> N" and "Bad s' \<sigma>' \<subseteq> Bad s \<sigma>"
  shows "consistent s' \<sigma>' N"
  using assms unfolding consistent_def by blast

section \<open>Parallel composition of any two processes meeting the specifications\<close>

text \<open>Beyond the thesis: consistent(s, \<sigma>) between two processes with abstract
  private state, used as the coupling predicate J of rg_parallel.\<close>

definition coupling :: "('l \<Rightarrow> ('a \<times> 'i) set) \<Rightarrow> ('m \<Rightarrow> ('a \<times> 'i) set) \<Rightarrow>
                        'l \<Rightarrow> 'm \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "coupling s_of nr_of l m \<sigma> \<longleftrightarrow> consistent (s_of l) \<sigma> (nr_of m)"

text \<open>Beyond the thesis: Collector \<parallel> Mutator runs on its own, so the composed
  system has no environment: its rely condition is false.\<close>

definition no_env :: "'l \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "no_env l \<sigma> \<sigma>' \<longleftrightarrow> False"

text \<open>Beyond the thesis: the composition argument, for any two processes that
  meet the specifications.  C1 is any process meeting the Collector's
  specification and C2 any process meeting the Mutator's, each with any
  private state.  All that is assumed is what the specifications say:
    collector_spec    {P1, rely-Collector} C1 {guar-Collector, Q1}
    mutator_spec      {P2, guar-Collector} C2 {guar-Mutator, Q2}
    collector_starts  the Collector's pre condition gives s = {}
    h1_s, h2_nr       history variables (such as the possible values of free)
                      are separate from s and new-risk
  GC_System applies it to the Collector of Appendix C and the Mutator of
  Algorithm 12.\<close>

locale gc_parallel =
  fixes C1 :: "('l, ('a,'i) state) rg_prog"
    and h1 :: "('l, ('a,'i) state) rg_hist"
    and s_of :: "'l \<Rightarrow> ('a \<times> 'i) set"
    and P1 :: "('l, ('a,'i) state) rg_conf \<Rightarrow> bool"
    and Q1 :: "('l, ('a,'i) state) rg_conf \<Rightarrow> ('l, ('a,'i) state) rg_conf \<Rightarrow> bool"
    and C2 :: "('m, ('a,'i) state) rg_prog"
    and h2 :: "('m, ('a,'i) state) rg_hist"
    and nr_of :: "'m \<Rightarrow> ('a \<times> 'i) set"
    and P2 :: "('m, ('a,'i) state) rg_conf \<Rightarrow> bool"
    and Q2 :: "('m, ('a,'i) state) rg_conf \<Rightarrow> ('m, ('a,'i) state) rg_conf \<Rightarrow> bool"
  assumes collector_spec: "rg_sat C1 h1 P1 (rely_C s_of) (guar_C s_of) Q1"
    and mutator_spec: "rg_sat C2 h2 P2 rely_M (guar_M nr_of) Q2"
    and collector_starts: "\<And>c. P1 c \<Longrightarrow> s_of (fst c) = {}"
    and h1_s: "\<And>l \<sigma>. s_of (h1 l \<sigma>) = s_of l"
    and h2_nr: "\<And>m \<sigma>. nr_of (h2 m \<sigma>) = nr_of m"
begin

text \<open>Thesis: item 1 at the end of Section 4.5.5: consistent(s, \<sigma>) holds
  initially, since the Collector starts with s = {}.\<close>

lemma initially:
  assumes "P1 (l,\<sigma>)"
  shows "coupling s_of nr_of l m \<sigma>"
proof -
  have "s_of l = {}" using collector_starts[OF assms] by simp
  then show ?thesis unfolding coupling_def consistent_def Bad_def by simp
qed

text \<open>Thesis: the side condition "the Collector's guarantee implies the Mutator's
  rely condition", with consistency preserved: guar-Collector is the
  Mutator's rely condition (Section 4.6), and item 2 at the end of Section
  4.5.5.\<close>

lemma side_C:
  assumes J: "coupling s_of nr_of l m \<sigma>" and G: "guar_C s_of (l,\<sigma>) (l',\<sigma>')"
  shows "rely_M m \<sigma> \<sigma>' \<and> coupling s_of nr_of (h1 l' \<sigma>') (h2 m \<sigma>') \<sigma>'"
proof -
  from G have GC: "guar_Collector \<sigma> \<sigma>'" and inv': "inv_state \<sigma>'"
    and B: "Bad (s_of l') \<sigma>' \<subseteq> Bad (s_of l) \<sigma>" unfolding guar_C_def by simp_all
  have R: "rely_M m \<sigma> \<sigma>'" unfolding rely_M_def using GC inv' by simp
  from J have C: "consistent (s_of l) \<sigma> (nr_of m)" unfolding coupling_def .
  have C': "consistent (s_of l') \<sigma>' (nr_of m)" by (rule collector_keeps_consistent[OF C B])
  have "coupling s_of nr_of (h1 l' \<sigma>') (h2 m \<sigma>') \<sigma>'" by (simp add: coupling_def h1_s h2_nr C')
  with R show ?thesis by blast
qed

text \<open>Thesis: the side condition "the Mutator's guarantee implies the
  Collector's rely condition", with consistency preserved: the implication of
  Section 4.5.5.\<close>

lemma side_M:
  assumes J: "coupling s_of nr_of l m \<sigma>" and G: "guar_M nr_of (m,\<sigma>) (m',\<sigma>')"
  shows "rely_C s_of l \<sigma> \<sigma>' \<and> coupling s_of nr_of (h1 l \<sigma>') (h2 m' \<sigma>') \<sigma>'"
proof -
  from J have C: "consistent (s_of l) \<sigma> (nr_of m)" unfolding coupling_def .
  from G have G': "guar_Mutator (nr_of m) \<sigma> (nr_of m') \<sigma>'" unfolding guar_M_def by simp
  from section_455_obligation[OF C G'] have E: "env_step (s_of l) \<sigma> \<sigma>'"
    and C': "consistent (s_of l) \<sigma>' (nr_of m')" by blast+
  have R: "rely_C s_of l \<sigma> \<sigma>'" unfolding rely_C_def by (rule E)
  have "coupling s_of nr_of (h1 l \<sigma>') (h2 m' \<sigma>') \<sigma>'" by (simp add: coupling_def h1_s h2_nr C')
  with R show ?thesis by blast
qed

text \<open>Mechanisation only: the side condition for the composed system's own
  environment, trivial since there is none.\<close>

lemma side_env:
  assumes "coupling s_of nr_of l m \<sigma>" and "no_env (l,m) \<sigma> \<sigma>'"
  shows "rely_C s_of l \<sigma> \<sigma>' \<and> rely_M m \<sigma> \<sigma>' \<and> coupling s_of nr_of (h1 l \<sigma>') (h2 m \<sigma>') \<sigma>'"
  using assms(2) unfolding no_env_def by simp

text \<open>Thesis: the parallel rule applied to the two specifications, with the
  obligations of Section 4.5.5 as side conditions:
    {P1 \<and> P2 \<and> J, false} C1 \<parallel> C2 {guar_C \<or> guar_M, Q1 \<and> Q2 \<and> J}
  with J = consistent(s, \<sigma>).  The thesis sets this argument out in Section
  4.5.5 and leaves formalising it as future work; this carries it out.\<close>

theorem parallel:
  "rg_sat (par C1 C2) (hpar h1 h2) (par_pre P1 P2 (coupling s_of nr_of)) no_env
          (par_guar (guar_C s_of) (guar_M nr_of)) (par_post Q1 Q2 (coupling s_of nr_of))"
proof (rule rg_parallel[OF collector_spec mutator_spec])
  fix l1 l2 \<sigma> l1' \<sigma>'
  assume "coupling s_of nr_of l1 l2 \<sigma>" and "guar_C s_of (l1,\<sigma>) (l1',\<sigma>')"
  then show "rely_M l2 \<sigma> \<sigma>' \<and> coupling s_of nr_of (h1 l1' \<sigma>') (h2 l2 \<sigma>') \<sigma>'"
    by (rule side_C)
next
  fix l1 l2 \<sigma> l2' \<sigma>'
  assume "coupling s_of nr_of l1 l2 \<sigma>" and "guar_M nr_of (l2,\<sigma>) (l2',\<sigma>')"
  then show "rely_C s_of l1 \<sigma> \<sigma>' \<and> coupling s_of nr_of (h1 l1 \<sigma>') (h2 l2' \<sigma>') \<sigma>'"
    by (rule side_M)
next
  fix l1 l2 \<sigma> \<sigma>'
  assume "coupling s_of nr_of l1 l2 \<sigma>" and "no_env (l1,l2) \<sigma> \<sigma>'"
  then show "rely_C s_of l1 \<sigma> \<sigma>' \<and> rely_M l2 \<sigma> \<sigma>' \<and> coupling s_of nr_of (h1 l1 \<sigma>') (h2 l2 \<sigma>') \<sigma>'"
    by (rule side_env)
qed

text \<open>Beyond the thesis: the soundness argument of the parallel rule for C1 and
  C2: every interleaving is, seen from either process, a computation of that
  process whose environment steps satisfy its rely condition, and
  consistent(s, \<sigma>) holds throughout.\<close>

lemma project:
  assumes P: "par_pre P1 P2 (coupling s_of nr_of) c0"
    and R: "rg_reach (par C1 C2) no_env (hpar h1 h2) c0 (l,m) \<sigma>"
  shows "rg_reach C1 (rely_C s_of) h1 (fst (fst c0), snd c0) l \<sigma> \<and>
         rg_reach C2 rely_M h2 (snd (fst c0), snd c0) m \<sigma> \<and> coupling s_of nr_of l m \<sigma>"
proof -
  have "rg_reach C1 (rely_C s_of) h1 (fst (fst c0), snd c0) (fst (l,m)) \<sigma> \<and>
        rg_reach C2 rely_M h2 (snd (fst c0), snd c0) (snd (l,m)) \<sigma> \<and>
        coupling s_of nr_of (fst (l,m)) (snd (l,m)) \<sigma>"
  proof (rule par_project[OF collector_spec mutator_spec _ _ _ P R])
    fix la ma sa la' sa'
    assume "coupling s_of nr_of la ma sa" and "guar_C s_of (la,sa) (la',sa')"
    then show "rely_M ma sa sa' \<and> coupling s_of nr_of (h1 la' sa') (h2 ma sa') sa'"
      by (rule side_C)
  next
    fix la ma sa ma' sa'
    assume "coupling s_of nr_of la ma sa" and "guar_M nr_of (ma,sa) (ma',sa')"
    then show "rely_C s_of la sa sa' \<and> coupling s_of nr_of (h1 la sa') (h2 ma' sa') sa'"
      by (rule side_M)
  next
    fix la ma sa sa'
    assume "coupling s_of nr_of la ma sa" and "no_env (la,ma) sa sa'"
    then show "rely_C s_of la sa sa' \<and> rely_M ma sa sa' \<and> coupling s_of nr_of (h1 la sa') (h2 ma sa') sa'"
      by (rule side_env)
  qed
  then show ?thesis by simp
qed

text \<open>Thesis: Corollary 2 and Theorem 6 for any Collector, in any interleaving
  with any Mutator: every Collector step satisfies guar-Collector, so it only
  adds garbage to free.\<close>

theorem collector_step:
  assumes P: "par_pre P1 P2 (coupling s_of nr_of) c0"
    and R: "rg_reach (par C1 C2) no_env (hpar h1 h2) c0 (l,m) \<sigma>"
    and S: "C1 (l,\<sigma>) (l',\<sigma>')"
  shows "guar_C s_of (l,\<sigma>) (l',\<sigma>')"
proof -
  from project[OF P R] have Rc: "rg_reach C1 (rely_C s_of) h1 (fst (fst c0), snd c0) l \<sigma>" by blast
  from P have P1: "P1 (fst (fst c0), snd c0)" unfolding par_pre_def by simp
  show ?thesis by (rule rg_satD_guar[OF collector_spec P1 Rc S])
qed

corollary collector_safe:
  assumes P: "par_pre P1 P2 (coupling s_of nr_of) c0"
    and R: "rg_reach (par C1 C2) no_env (hpar h1 h2) c0 (l,m) \<sigma>"
    and S: "C1 (l,\<sigma>) (l',\<sigma>')"
  shows "free \<sigma>' - free \<sigma> \<subseteq> garbage \<sigma>" and "guar_Collector \<sigma> \<sigma>'"
proof -
  have G: "guar_C s_of (l,\<sigma>) (l',\<sigma>')" by (rule collector_step[OF P R S])
  then show "guar_Collector \<sigma> \<sigma>'" unfolding guar_C_def by simp
  from G have "guar_Collector \<sigma> \<sigma>'" unfolding guar_C_def by simp
  then show "free \<sigma>' - free \<sigma> \<subseteq> garbage \<sigma>" unfolding guar_Collector_def by blast
qed

text \<open>Thesis: the relationship Section 4.5.5 requires, for any Mutator, in any
  interleaving with any Collector: every Mutator step satisfies guar-Mutator
  and hence rely-Collector for the Collector's current s.\<close>

theorem mutator_step:
  assumes P: "par_pre P1 P2 (coupling s_of nr_of) c0"
    and R: "rg_reach (par C1 C2) no_env (hpar h1 h2) c0 (l,m) \<sigma>"
    and S: "C2 (m,\<sigma>) (m',\<sigma>')"
  shows "guar_Mutator (nr_of m) \<sigma> (nr_of m') \<sigma>'" and "rely_Collector (s_of l) \<sigma> \<sigma>'"
proof -
  from project[OF P R] have Rm: "rg_reach C2 rely_M h2 (snd (fst c0), snd c0) m \<sigma>"
    and J: "coupling s_of nr_of l m \<sigma>" by blast+
  from P have P2: "P2 (snd (fst c0), snd c0)" unfolding par_pre_def by simp
  have "guar_M nr_of (m,\<sigma>) (m',\<sigma>')" by (rule rg_satD_guar[OF mutator_spec P2 Rm S])
  then show G: "guar_Mutator (nr_of m) \<sigma> (nr_of m') \<sigma>'" unfolding guar_M_def by simp
  from J have C: "consistent (s_of l) \<sigma> (nr_of m)" unfolding coupling_def .
  from section_455_obligation[OF C G] have "env_step (s_of l) \<sigma> \<sigma>'" by blast
  then show "rely_Collector (s_of l) \<sigma> \<sigma>'" unfolding env_step_def by blast
qed

text \<open>Beyond the thesis: in every state of every interleaving, consistent(s, \<sigma>)
  holds and so do both processes' post conditions (for the Collector,
  including post-Collector once its cycle is done).\<close>

theorem invariants:
  assumes P: "par_pre P1 P2 (coupling s_of nr_of) c0"
    and R: "rg_reach (par C1 C2) no_env (hpar h1 h2) c0 (l,m) \<sigma>"
  shows "coupling s_of nr_of l m \<sigma> \<and> Q1 (fst (fst c0), snd c0) (l,\<sigma>) \<and>
         Q2 (snd (fst c0), snd c0) (m,\<sigma>)"
proof -
  have "par_post Q1 Q2 (coupling s_of nr_of) c0 ((l,m),\<sigma>)" by (rule rg_satD_post[OF parallel P R])
  then show ?thesis unfolding par_post_def by simp
qed

end

section \<open>Collector \<parallel> Mutator is correct (Section 4.5.5)\<close>

text \<open>Thesis: "the Collector meets its specification, the Mutator meets its
  specification, and so Collector \<parallel> Mutator is correct", for any Collector
  C1 and any Mutator C2, by the parallel rule (Section 2.2) with the
  obligations of Section 4.5.5 as side conditions and consistent(s, \<sigma>) as
  the coupling predicate:
    {pre-Collector \<and> pre-Mutator \<and> consistent, false}
        C1 \<parallel> C2
    {guar-Collector \<or> guar-Mutator, post-Collector \<and> post-Mutator \<and> consistent}.
  The assumptions are the two specifications: C1 meets the Collector's
  (rely-Collector, guar-Collector, starting with s = {}), and C2 meets the
  Mutator's (rely guar-Collector, guar guar-Mutator).  Q1 and Q2 are the two
  post conditions, whatever they are.  The last two assumptions say that
  history variables, such as the Collector's record of the possible values
  of free, are separate from s and new-risk.  The composed system has no
  environment, so its rely condition is false (no_env).\<close>

theorem Collector_par_Mutator_abstract:
  assumes Collector_meets_spec: "rg_sat C1 h1 P1 (rely_C s_of) (guar_C s_of) Q1"
    and Mutator_meets_spec: "rg_sat C2 h2 P2 rely_M (guar_M nr_of) Q2"
    and Collector_starts: "\<And>c. P1 c \<Longrightarrow> s_of (fst c) = {}"
    and h1_s: "\<And>l \<sigma>. s_of (h1 l \<sigma>) = s_of l"
    and h2_nr: "\<And>m \<sigma>. nr_of (h2 m \<sigma>) = nr_of m"
  shows "rg_sat (par C1 C2) (hpar h1 h2) (par_pre P1 P2 (coupling s_of nr_of)) no_env
                (par_guar (guar_C s_of) (guar_M nr_of)) (par_post Q1 Q2 (coupling s_of nr_of))"
proof -
  interpret gc_parallel C1 h1 s_of P1 Q1 C2 h2 nr_of P2 Q2
    using assms by (rule gc_parallel.intro)
  show ?thesis by (rule parallel)
qed

end
