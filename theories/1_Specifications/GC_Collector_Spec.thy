(*  GC_Collector_Spec: the Collector's rely and guarantee conditions
    (Sections 4.4, 4.4.1, 4.5.3 and 4.5.4).

    PART 1 of the mechanisation: the specifications, and why any Collector
    and Mutator meeting them are correct in parallel.  This theory and
    GC_Mutator_Spec state the two specifications, one for each process: what
    the process assumes about the other (its rely condition) and what it
    promises (its guarantee condition).  They say nothing about code.
    GC_Parallel then proves that any two processes meeting them run correctly
    in parallel.  Part 2 proves that the actual code meets them: the
    Collector's in the folder 2a_Collector, the Mutator's in 2b_Mutator.

    HOW TO READ THE LABELS.  Each definition and theorem below has a text
    block saying how it relates to the thesis:
      "Thesis:"             it is that part of the thesis;
      "Beyond the thesis:"  the thesis states or argues it informally or not
                            at all; the label says which part of the thesis
                            it makes precise or supports;
      "Mechanisation only:" a helper needed only for the Isabelle proof.
    Section, lemma and theorem numbers are those of the thesis.

      thesis                                        Isabelle
      ------------------------------------------    ------------------------
      the Bad set, Definition 6 (Section 4.5.3)     Bad, BadA
      rely-Collector (Section 4.5.4)                rely_Collector
      Assumption 1 (Section 4.4.1)                  atomic
      an environment step, as the Collector         env_step
        sees it
      guar-Collector (Section 4.4)                  guar_Collector
      the Collector's specification (Section 4.4)   rely_C, guar_C           *)

theory GC_Collector_Spec
  imports GC_Defs RG_Semantics
begin

section \<open>The protected set and the Bad set (Section 4.5.3, Definition 6)\<close>

text \<open>Thesis: Definition 6.  s is the Collector's private set of protected
  edges (Section 4.5.3).  It is passed as an explicit parameter rather than
  stored in the shared state, which is the point of Section 4.5.5: the
  Mutator never sees it.  Bad(s, \<sigma>) is the set of protected edges whose
  target is unmarked, and BadA(s, \<sigma>) the set of their targets.\<close>

definition Bad :: "('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> ('a \<times> 'i) set" where
  "Bad s \<sigma> = {e \<in> s. \<exists>b. hp \<sigma> e = Some b \<and> b \<notin> marked \<sigma>}"

definition BadA :: "('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> 'a set" where
  "BadA s \<sigma> = {b. \<exists>e\<in>Bad s \<sigma>. hp \<sigma> e = Some b}"

text \<open>Mechanisation only: elementary facts about Bad and BadA.\<close>

lemma Bad_subset: "Bad s \<sigma> \<subseteq> s"
  unfolding Bad_def by auto

lemma finite_Bad:
  fixes \<sigma> :: "('a::finite,'i::finite) state"
  shows "finite (Bad s \<sigma>)"
  by (rule finite_subset[OF subset_UNIV finite_UNIV])

lemma BadA_unmarked: "b \<in> BadA s \<sigma> \<Longrightarrow> b \<notin> marked \<sigma>"
  unfolding BadA_def Bad_def by auto

section \<open>The rely condition of the Collector (Section 4.5.4)\<close>

text \<open>Thesis: rely-Collector (Section 4.5.4), with its conjuncts in the order
  of the thesis: (1), (2), (3), (4.1), (4.2), (4.3).  roots is constant
  (Section 4.2.2), which is recorded here explicitly.  Conjunct (4.1): a heap
  update may not change a pointer out of garbage, and its new target must
  not be garbage.  The relation is reflexive and transitive
  (rely_Collector_refl, rely_Collector_trans below).\<close>

definition rely_Collector :: "('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "rely_Collector s \<sigma> \<sigma>' \<longleftrightarrow>
     roots \<sigma>' = roots \<sigma> \<and>
     marked \<sigma> \<subseteq> marked \<sigma>' \<and> free \<sigma>' \<subseteq> free \<sigma> \<and>
     marked \<sigma>' - marked \<sigma> \<subseteq> reach (roots \<sigma>) (hp \<sigma>) \<and>
     reach (roots \<sigma>') (hp \<sigma>') - reach (roots \<sigma>) (hp \<sigma>) \<subseteq> free \<sigma> \<and>
     (\<forall>e. hp \<sigma>' e \<noteq> hp \<sigma> e \<longrightarrow>
            fst e \<notin> garbage \<sigma> \<and> (\<forall>b. hp \<sigma>' e = Some b \<longrightarrow> b \<notin> garbage \<sigma>)) \<and>
     (\<forall>e. hp \<sigma>' e \<noteq> hp \<sigma> e \<and> marked \<sigma>' = marked \<sigma> \<longrightarrow> Bad s \<sigma> = {}) \<and>
     (\<forall>e. hp \<sigma>' e \<noteq> hp \<sigma> e \<and> free \<sigma>' = free \<sigma> \<longrightarrow> free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {})"

section \<open>Assumption 1: step atomicity (Section 4.4.1)\<close>

text \<open>Thesis: Assumption 1 (Section 4.4.1).  An atomic step changes at most one
  of hp, marked and free, and only by one pointer, one marked node or one
  free node.\<close>

definition atomic :: "('a,'i) state \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "atomic \<sigma> \<sigma>' \<longleftrightarrow>
     (hp \<sigma>' \<noteq> hp \<sigma> \<longrightarrow> marked \<sigma>' = marked \<sigma> \<and> free \<sigma>' = free \<sigma> \<and>
                          (\<exists>e. \<forall>e'. e' \<noteq> e \<longrightarrow> hp \<sigma>' e' = hp \<sigma> e')) \<and>
     (marked \<sigma>' \<noteq> marked \<sigma> \<longrightarrow> hp \<sigma>' = hp \<sigma> \<and> free \<sigma>' = free \<sigma> \<and>
                          card ((marked \<sigma> - marked \<sigma>') \<union> (marked \<sigma>' - marked \<sigma>)) = 1) \<and>
     (free \<sigma>' \<noteq> free \<sigma> \<longrightarrow> hp \<sigma>' = hp \<sigma> \<and> marked \<sigma>' = marked \<sigma> \<and>
                          card ((free \<sigma> - free \<sigma>') \<union> (free \<sigma>' - free \<sigma>)) = 1)"

text \<open>Thesis: an environment step, as the Collector sees it: rely-Collector,
  with Assumption 1, and inv-\<Sigma> in both states (the thesis assumes inv-\<Sigma>
  of every state, Section 4.4.2).\<close>

definition env_step :: "('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "env_step s \<sigma> \<sigma>' \<longleftrightarrow> inv_state \<sigma> \<and> inv_state \<sigma>' \<and> rely_Collector s \<sigma> \<sigma>' \<and> atomic \<sigma> \<sigma>'"

section \<open>The guarantee condition of the Collector (Section 4.4)\<close>

text \<open>Thesis: guar-Collector (Section 4.4), which is also the rely condition of
  the Mutator (Section 4.6).  Its last conjunct is
  (reach(roots, hp) \<times> Index) \<lhd> hp' = (reach(roots, hp) \<times> Index) \<lhd> hp, that
  is, no pointer out of a reachable node changes.  It implies
  reach(roots, hp') = reach(roots, hp) by Sublemma 1 (sublemma1_agree_reach,
  GC_Safety).\<close>

definition guar_Collector :: "('a,'i) state \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "guar_Collector \<sigma> \<sigma>' \<longleftrightarrow> roots \<sigma>' = roots \<sigma> \<and>
     free \<sigma> \<subseteq> free \<sigma>' \<and> free \<sigma>' - free \<sigma> \<subseteq> garbage \<sigma> \<and>
     (\<forall>e. fst e \<in> reach (roots \<sigma>) (hp \<sigma>) \<longrightarrow> hp \<sigma>' e = hp \<sigma> e)"

section \<open>Elementary consequences\<close>

text \<open>Mechanisation only: facts about rely-Collector and inv-\<Sigma> used
  throughout.\<close>

lemma rely_marked_mono: "rely_Collector s \<sigma> \<sigma>' \<Longrightarrow> marked \<sigma> \<subseteq> marked \<sigma>'"
  unfolding rely_Collector_def by blast

lemma rely_roots: "rely_Collector s \<sigma> \<sigma>' \<Longrightarrow> roots \<sigma>' = roots \<sigma>"
  unfolding rely_Collector_def by blast

lemma rely_free_anti: "rely_Collector s \<sigma> \<sigma>' \<Longrightarrow> free \<sigma>' \<subseteq> free \<sigma>"
  unfolding rely_Collector_def by blast

lemma inv_free_marked: "inv_state \<sigma> \<Longrightarrow> free \<sigma> \<subseteq> marked \<sigma>"
  unfolding inv_state_def by blast

lemma inv_roots_marked: "inv_state \<sigma> \<Longrightarrow> roots \<sigma> \<subseteq> marked \<sigma>"
  unfolding inv_state_def by blast

lemma inv_reach_roots_marked: "inv_state \<sigma> \<Longrightarrow> reach (roots \<sigma>) (hp \<sigma>) \<subseteq> reach (marked \<sigma>) (hp \<sigma>)"
  by (rule reach_mono[OF inv_roots_marked])

text \<open>Mechanisation only: garbage never shrinks over an environment step.\<close>

lemma rely_garbage_mono:
  assumes "rely_Collector s \<sigma> \<sigma>'"
  shows "garbage \<sigma> \<subseteq> garbage \<sigma>'"
proof -
  from assms have "reach (roots \<sigma>') (hp \<sigma>') - reach (roots \<sigma>) (hp \<sigma>) \<subseteq> free \<sigma>"
    and "free \<sigma>' \<subseteq> free \<sigma>" unfolding rely_Collector_def by blast+
  then show ?thesis unfolding garbage_def by blast
qed

text \<open>Mechanisation only: if the heap changes in an atomic step, exactly one
  edge changes, and marked and free do not change.\<close>

lemma atomic_hp_change:
  assumes "atomic \<sigma> \<sigma>'" and "hp \<sigma>' \<noteq> hp \<sigma>"
  obtains e where "\<forall>e'. e' \<noteq> e \<longrightarrow> hp \<sigma>' e' = hp \<sigma> e'" and "hp \<sigma>' e \<noteq> hp \<sigma> e"
    and "marked \<sigma>' = marked \<sigma>" and "free \<sigma>' = free \<sigma>"
proof -
  from assms obtain e where E: "\<forall>e'. e' \<noteq> e \<longrightarrow> hp \<sigma>' e' = hp \<sigma> e'"
    and M: "marked \<sigma>' = marked \<sigma>" and F: "free \<sigma>' = free \<sigma>"
    unfolding atomic_def by blast
  have hne: "hp \<sigma>' e \<noteq> hp \<sigma> e"
  proof
    assume "hp \<sigma>' e = hp \<sigma> e"
    with E have "\<forall>e'. hp \<sigma>' e' = hp \<sigma> e'" by auto
    then have "hp \<sigma>' = hp \<sigma>" by (simp add: fun_eq_iff)
    with assms(2) show False by simp
  qed
  show thesis by (rule that[OF E hne M F])
qed

section \<open>The rely condition is reflexive and transitive\<close>

text \<open>Beyond the thesis (supports Section 2.2): Section 2.2 requires rely and
  guarantee conditions to be reflexive and transitive.  Transitivity of
  rely-Collector uses the state invariant (free \<subseteq> marked) in the first
  state.  With (4.1) in the form a \<in> reach(roots, hp) it would fail: a free
  node that a Malloc makes reachable can have one of its pointers set by a
  later step, and that node was not reachable in the first state of the
  sequence.\<close>

lemma rely_Collector_refl: "rely_Collector s \<sigma> \<sigma>"
  unfolding rely_Collector_def by auto

lemma rely_Collector_trans:
  assumes inv: "inv_state \<sigma>" and R1: "rely_Collector s \<sigma> \<sigma>'" and R2: "rely_Collector s \<sigma>' \<sigma>''"
  shows "rely_Collector s \<sigma> \<sigma>''"
proof -
  from R1 have r1: "roots \<sigma>' = roots \<sigma>" and m1: "marked \<sigma> \<subseteq> marked \<sigma>'" and f1: "free \<sigma>' \<subseteq> free \<sigma>"
    and mr1: "marked \<sigma>' - marked \<sigma> \<subseteq> reach (roots \<sigma>) (hp \<sigma>)"
    and rr1: "reach (roots \<sigma>') (hp \<sigma>') - reach (roots \<sigma>) (hp \<sigma>) \<subseteq> free \<sigma>"
    and h1: "\<forall>e. hp \<sigma>' e \<noteq> hp \<sigma> e \<longrightarrow> fst e \<notin> garbage \<sigma> \<and> (\<forall>b. hp \<sigma>' e = Some b \<longrightarrow> b \<notin> garbage \<sigma>)"
    and b1: "\<forall>e. hp \<sigma>' e \<noteq> hp \<sigma> e \<and> marked \<sigma>' = marked \<sigma> \<longrightarrow> Bad s \<sigma> = {}"
    and d1: "\<forall>e. hp \<sigma>' e \<noteq> hp \<sigma> e \<and> free \<sigma>' = free \<sigma> \<longrightarrow> free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}"
    unfolding rely_Collector_def by blast+
  from R2 have r2: "roots \<sigma>'' = roots \<sigma>'" and m2: "marked \<sigma>' \<subseteq> marked \<sigma>''" and f2: "free \<sigma>'' \<subseteq> free \<sigma>'"
    and mr2: "marked \<sigma>'' - marked \<sigma>' \<subseteq> reach (roots \<sigma>') (hp \<sigma>')"
    and rr2: "reach (roots \<sigma>'') (hp \<sigma>'') - reach (roots \<sigma>') (hp \<sigma>') \<subseteq> free \<sigma>'"
    and h2: "\<forall>e. hp \<sigma>'' e \<noteq> hp \<sigma>' e \<longrightarrow> fst e \<notin> garbage \<sigma>' \<and> (\<forall>b. hp \<sigma>'' e = Some b \<longrightarrow> b \<notin> garbage \<sigma>')"
    and b2: "\<forall>e. hp \<sigma>'' e \<noteq> hp \<sigma>' e \<and> marked \<sigma>'' = marked \<sigma>' \<longrightarrow> Bad s \<sigma>' = {}"
    and d2: "\<forall>e. hp \<sigma>'' e \<noteq> hp \<sigma>' e \<and> free \<sigma>'' = free \<sigma>' \<longrightarrow> free \<sigma>' \<inter> reach (roots \<sigma>') (hp \<sigma>') = {}"
    unfolding rely_Collector_def by blast+
  have G: "garbage \<sigma> \<subseteq> garbage \<sigma>'" by (rule rely_garbage_mono[OF R1])
  have FM: "free \<sigma> \<subseteq> marked \<sigma>" by (rule inv_free_marked[OF inv])
  have c0: "roots \<sigma>'' = roots \<sigma>" by (rule trans[OF r2 r1])
  have c1: "marked \<sigma> \<subseteq> marked \<sigma>''" using m1 m2 by blast
  have c2: "free \<sigma>'' \<subseteq> free \<sigma>" using f1 f2 by blast
  \<comment> \<open>(3): a node marked in the second step was reachable in \<sigma>', hence reachable
      in \<sigma> or free in \<sigma>; free nodes are already marked.\<close>
  have c3: "marked \<sigma>'' - marked \<sigma> \<subseteq> reach (roots \<sigma>) (hp \<sigma>)"
  proof
    fix y assume y: "y \<in> marked \<sigma>'' - marked \<sigma>"
    show "y \<in> reach (roots \<sigma>) (hp \<sigma>)"
    proof (cases "y \<in> marked \<sigma>'")
      case True
      with y mr1 show ?thesis by blast
    next
      case False
      with y mr2 have "y \<in> reach (roots \<sigma>') (hp \<sigma>')" by blast
      with rr1 have "y \<in> reach (roots \<sigma>) (hp \<sigma>) \<or> y \<in> free \<sigma>" by blast
      with y FM show ?thesis by blast
    qed
  qed
  have c4: "reach (roots \<sigma>'') (hp \<sigma>'') - reach (roots \<sigma>) (hp \<sigma>) \<subseteq> free \<sigma>"
    using rr1 rr2 f1 by blast
  \<comment> \<open>(4.1): garbage only grows, so "not garbage in \<sigma>'" implies "not garbage in \<sigma>".\<close>
  have c5: "\<forall>e. hp \<sigma>'' e \<noteq> hp \<sigma> e \<longrightarrow> fst e \<notin> garbage \<sigma> \<and> (\<forall>b. hp \<sigma>'' e = Some b \<longrightarrow> b \<notin> garbage \<sigma>)"
  proof (intro allI impI)
    fix e assume ne: "hp \<sigma>'' e \<noteq> hp \<sigma> e"
    show "fst e \<notin> garbage \<sigma> \<and> (\<forall>b. hp \<sigma>'' e = Some b \<longrightarrow> b \<notin> garbage \<sigma>)"
    proof (cases "hp \<sigma>' e = hp \<sigma> e")
      case True
      with ne have "hp \<sigma>'' e \<noteq> hp \<sigma>' e" by simp
      with h2 have "fst e \<notin> garbage \<sigma>'" and "\<forall>b. hp \<sigma>'' e = Some b \<longrightarrow> b \<notin> garbage \<sigma>'"
        by blast+
      with G show ?thesis by blast
    next
      case False
      with h1 have A: "fst e \<notin> garbage \<sigma>" and B: "\<forall>b. hp \<sigma>' e = Some b \<longrightarrow> b \<notin> garbage \<sigma>"
        by blast+
      show ?thesis
      proof (cases "hp \<sigma>'' e = hp \<sigma>' e")
        case True
        with A B show ?thesis by auto
      next
        case False
        with h2 have "\<forall>b. hp \<sigma>'' e = Some b \<longrightarrow> b \<notin> garbage \<sigma>'" by blast
        with A G show ?thesis by blast
      qed
    qed
  qed
  \<comment> \<open>(4.2): if marked is unchanged overall it is unchanged in both steps; the
      heap changed in the first step or, if not, \<open>Bad s \<sigma> = Bad s \<sigma>'\<close>.\<close>
  have c6: "\<forall>e. hp \<sigma>'' e \<noteq> hp \<sigma> e \<and> marked \<sigma>'' = marked \<sigma> \<longrightarrow> Bad s \<sigma> = {}"
  proof (intro allI impI)
    fix e assume a: "hp \<sigma>'' e \<noteq> hp \<sigma> e \<and> marked \<sigma>'' = marked \<sigma>"
    then have M: "marked \<sigma>'' = marked \<sigma>" by blast
    have M1: "marked \<sigma>' = marked \<sigma>"
    proof (rule subset_antisym)
      show "marked \<sigma>' \<subseteq> marked \<sigma>" using m2 unfolding M .
      show "marked \<sigma> \<subseteq> marked \<sigma>'" by (rule m1)
    qed
    have M2: "marked \<sigma>'' = marked \<sigma>'" using M M1 by simp
    show "Bad s \<sigma> = {}"
    proof (cases "hp \<sigma>' = hp \<sigma>")
      case True
      with a have "hp \<sigma>'' e \<noteq> hp \<sigma>' e" by simp
      with b2 M2 have "Bad s \<sigma>' = {}" by blast
      moreover have "Bad s \<sigma>' = Bad s \<sigma>" using True M1 unfolding Bad_def by simp
      ultimately show ?thesis by simp
    next
      case False
      then obtain e' where "hp \<sigma>' e' \<noteq> hp \<sigma> e'" by (auto simp: fun_eq_iff)
      with b1 M1 show ?thesis by blast
    qed
  qed
  \<comment> \<open>(4.3): the same argument with \<open>free\<close> in place of \<open>marked\<close>.\<close>
  have c7: "\<forall>e. hp \<sigma>'' e \<noteq> hp \<sigma> e \<and> free \<sigma>'' = free \<sigma> \<longrightarrow> free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}"
  proof (intro allI impI)
    fix e assume a: "hp \<sigma>'' e \<noteq> hp \<sigma> e \<and> free \<sigma>'' = free \<sigma>"
    then have F: "free \<sigma>'' = free \<sigma>" by blast
    have F1: "free \<sigma>' = free \<sigma>"
    proof (rule subset_antisym)
      show "free \<sigma>' \<subseteq> free \<sigma>" by (rule f1)
      show "free \<sigma> \<subseteq> free \<sigma>'" using f2 unfolding F .
    qed
    have F2: "free \<sigma>'' = free \<sigma>'" using F F1 by simp
    show "free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}"
    proof (cases "hp \<sigma>' = hp \<sigma>")
      case True
      with a have "hp \<sigma>'' e \<noteq> hp \<sigma>' e" by simp
      with d2 F2 have D: "free \<sigma>' \<inter> reach (roots \<sigma>') (hp \<sigma>') = {}" by blast
      have EQ: "free \<sigma>' \<inter> reach (roots \<sigma>') (hp \<sigma>') = free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>)"
        using True F1 r1 by simp
      from D show ?thesis unfolding EQ .
    next
      case False
      then obtain e' where "hp \<sigma>' e' \<noteq> hp \<sigma> e'" by (auto simp: fun_eq_iff)
      with d1 F1 show ?thesis by blast
    qed
  qed
  from c0 c1 c2 c3 c4 c5 c6 c7 show ?thesis unfolding rely_Collector_def by blast
qed

section \<open>The Collector's specification (Sections 4.4 and 4.5.4)\<close>

text \<open>Thesis: the Collector's specification (Section 4.4):
    pre  s = {}
    rely rely-Collector
    guar guar-Collector
    post garbage \<subseteq> \<Union>free~                                   (post-Collector)
  Below are its rely and guarantee conditions.  A Collector's private state
  is abstract here (type 'l), and s_of reads the protected set s from it.
  The pre condition s = {} is an assumption of the composition
  (GC_Parallel).  The post condition is about the Collector's own record of
  the possible values of free, so it is left open there and given for the
  code in GC_Collector.\<close>

text \<open>Thesis: the Collector's rely condition, rely-Collector (Section 4.5.4), for
  its protected set s, with Assumption 1 (Section 4.4.1) and inv-\<Sigma> in both
  states (env_step, above).  s_of reads s from the Collector's private
  state.\<close>

definition rely_C :: "('l \<Rightarrow> ('a \<times> 'i) set) \<Rightarrow> ('l, ('a,'i) state) rg_rely" where
  "rely_C s_of l \<sigma> \<sigma>' \<longleftrightarrow> env_step (s_of l) \<sigma> \<sigma>'"

text \<open>Thesis: the Collector's guarantee, guar-Collector (Section 4.4), with two
  more conjuncts.  inv-\<Sigma> holds after the step (the thesis assumes it of
  every state).  Bad(s', \<sigma>') \<subseteq> Bad(s, \<sigma>) is Lemma 3, about the Collector's
  own s; it is here because the composition needs it (item 2 at the end of
  Section 4.5.5).  The Mutator relies only on the first conjunct.\<close>

definition guar_C :: "('l \<Rightarrow> ('a \<times> 'i) set) \<Rightarrow> ('l, ('a,'i) state) rg_conf \<Rightarrow>
                      ('l, ('a,'i) state) rg_conf \<Rightarrow> bool" where
  "guar_C s_of c c' \<longleftrightarrow> guar_Collector (snd c) (snd c') \<and> inv_state (snd c') \<and>
                         Bad (s_of (fst c')) (snd c') \<subseteq> Bad (s_of (fst c)) (snd c)"

end
