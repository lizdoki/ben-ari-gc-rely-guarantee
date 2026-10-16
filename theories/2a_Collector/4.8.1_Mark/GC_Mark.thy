(*  GC_Mark: Section 4.8.1 of the thesis -- the lemmas and theorems of the Mark
    phase.
      Lemma 5  / Theorem 1  -- Mark-kids: so-far transitive and well-founded,
                               post condition
      Lemma 6  / Lemma 7    -- Propagate: so-far transitive and well-founded,
                               first conjunct
      Lemma 8               -- closed marking covers the reachable region
      Theorem 2             -- Propagate marks all reachable nodes
      Lemma 9               -- reach(marked) never grows during Mark
      Lemmas 10-12, Corollary 1, Theorem 3 -- the Mark loop (Lemma 10:
                               so-far transitive and well-founded)
    The so-far relations are relations between the private variables and
    the shared state at the start and at the end of an iteration.
    GC_Mark_Sat uses these results to prove that Mark-kids, Propagate and
    Mark meet their specifications.

    HOW TO READ THE LABELS.  Each definition and theorem below, or each group
    of them, has a text block saying how it relates to the thesis:
      "Thesis:"             it is that part of the thesis;
      "Beyond the thesis:"  the thesis states or argues it informally or not
                            at all; the label says which part of the thesis
                            it makes precise or supports;
      "Mechanisation only:" a helper needed only for the Isabelle proof.
    Section, lemma and theorem numbers are those of the thesis.  *)

theory GC_Mark
  imports GC_Invariant
begin

section \<open>Mark-kids (Section 4.8.1, Algorithm 6)\<close>

text \<open>Thesis: so-farM-k, the so-far relation of the Mark-kids loop (Section
  4.8.1): checked \<subset> checked' \<and> s' = s \<union> {(x, i) | i \<in> checked' - checked}.\<close>

definition so_farMk :: "'a \<Rightarrow> 'i set \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> 'i set \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> bool" where
  "so_farMk x ch s ch' s' \<longleftrightarrow> ch \<subset> ch' \<and> s' = s \<union> {(x,i) | i. i \<in> ch' - ch}"

text \<open>Thesis: Lemma 5, first half: so-farM-k is transitive.\<close>

theorem lemma5_so_farMk_trans:
  assumes "so_farMk x ch s ch' s'" and "so_farMk x ch' s' ch'' s''"
  shows "so_farMk x ch s ch'' s''"
proof -
  from assms have 1: "ch \<subset> ch'" "ch' \<subset> ch''" and 2: "s' = s \<union> {(x,i) | i. i \<in> ch' - ch}"
    and 3: "s'' = s' \<union> {(x,i) | i. i \<in> ch'' - ch'}" unfolding so_farMk_def by blast+
  have "ch \<subset> ch''" using 1 by (rule psubset_trans)
  moreover have "s'' = s \<union> {(x,i) | i. i \<in> ch'' - ch}" using 1 2 3 by auto
  ultimately show ?thesis unfolding so_farMk_def by blast
qed

text \<open>Thesis: Lemma 5, second half: so-farM-k is well-founded.  checked grows
  strictly in every iteration and is bounded by Index, which is finite, so
  the loop terminates.\<close>

theorem lemma5_so_farMk_wf:
  "wf {((ch',s'),(ch,s)) | ch s ch' s'. so_farMk x ch s ch' (s' :: ('a \<times> 'i::finite) set)}"
  by (rule wf_psubset_rel[where F = fst]) (auto simp: so_farMk_def)

text \<open>Thesis: post-Mark-kids (Section 4.8.1, Appendix C):
    s' = s \<union> {(x, i) | i \<in> Index} \<and> kids(x, hp') \<subseteq> marked' \<union> BadA(s', \<sigma>').\<close>

definition post_MarkKids :: "'a \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "post_MarkKids x s s' \<sigma>' \<longleftrightarrow> s' = s \<union> {(x,i) | i. True} \<and> kids x (hp \<sigma>') \<subseteq> marked \<sigma>' \<union> BadA s' \<sigma>'"

text \<open>Thesis: Theorem 1 (Mark-kids post condition):
    checked' = Index \<and> so-farM-k(\<sigma>, \<sigma>') \<Rightarrow> post-Mark-kids(\<sigma>, \<sigma>').\<close>

theorem theorem1_post_MarkKids:
  assumes "so_farMk x {} s UNIV s'"
  shows "post_MarkKids x s s' \<sigma>'"
proof -
  have S: "s' = s \<union> {(x,i) | i. True}" using assms unfolding so_farMk_def by simp
  have "kids x (hp \<sigma>') \<subseteq> marked \<sigma>' \<union> BadA s' \<sigma>'"
  proof
    fix b assume "b \<in> kids x (hp \<sigma>')"
    then obtain i where hb: "hp \<sigma>' (x,i) = Some b" unfolding kids_def by blast
    have "(x,i) \<in> s'" using S by blast
    show "b \<in> marked \<sigma>' \<union> BadA s' \<sigma>'"
    proof (cases "b \<in> marked \<sigma>'")
      case True then show ?thesis by simp
    next
      case False
      with \<open>(x,i) \<in> s'\<close> hb have "(x,i) \<in> Bad s' \<sigma>'" unfolding Bad_def by blast
      with hb show ?thesis unfolding BadA_def by blast
    qed
  qed
  with S show ?thesis unfolding post_MarkKids_def by blast
qed

section \<open>Propagate (Section 4.8.1, Algorithm 5)\<close>

text \<open>Thesis: so-farP, the so-far relation of the Propagate loop (Section 4.8.1).\<close>

definition so_farP :: "'a set \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "so_farP c s \<sigma> c' s' \<sigma>' \<longleftrightarrow> c \<subset> c' \<and> marked \<sigma> \<subseteq> marked \<sigma>' \<and> s \<subseteq> s' \<and>
     (\<forall>x \<in> marked \<sigma> \<inter> (c' - c). \<forall>i. (x,i) \<in> s')"

text \<open>Thesis: Lemma 6, first half: so-farP is transitive.\<close>

theorem lemma6_so_farP_trans:
  assumes "so_farP c s \<sigma> c' s' \<sigma>'" and "so_farP c' s' \<sigma>' c'' s'' \<sigma>''"
  shows "so_farP c s \<sigma> c'' s'' \<sigma>''"
proof -
  note T1 = assms(1)[unfolded so_farP_def] and T2 = assms(2)[unfolded so_farP_def]
  have 1: "c \<subset> c'" "c' \<subset> c''" "marked \<sigma> \<subseteq> marked \<sigma>'" "marked \<sigma>' \<subseteq> marked \<sigma>''"
    "s \<subseteq> s'" "s' \<subseteq> s''"
    by (rule T1[THEN conjunct1], rule T2[THEN conjunct1],
        rule T1[THEN conjunct2, THEN conjunct1], rule T2[THEN conjunct2, THEN conjunct1],
        rule T1[THEN conjunct2, THEN conjunct2, THEN conjunct1],
        rule T2[THEN conjunct2, THEN conjunct2, THEN conjunct1])
  have 2: "\<forall>x \<in> marked \<sigma> \<inter> (c' - c). \<forall>i. (x,i) \<in> s'"
    by (rule T1[THEN conjunct2, THEN conjunct2, THEN conjunct2])
  have 3: "\<forall>x \<in> marked \<sigma>' \<inter> (c'' - c'). \<forall>i. (x,i) \<in> s''"
    by (rule T2[THEN conjunct2, THEN conjunct2, THEN conjunct2])
  have cc: "c \<subset> c''" using 1(1) 1(2) by (rule psubset_trans)
  have "\<forall>x \<in> marked \<sigma> \<inter> (c'' - c). \<forall>i. (x,i) \<in> s''"
  proof (intro ballI allI)
    fix x i assume x: "x \<in> marked \<sigma> \<inter> (c'' - c)"
    show "(x,i) \<in> s''"
    proof (cases "x \<in> c'")
      case True
      with x 2 have "(x,i) \<in> s'" by blast
      with 1(6) show ?thesis by blast
    next
      case False
      with x 1(3) 3 show ?thesis by blast
    qed
  qed
  with cc 1 show ?thesis unfolding so_farP_def by blast
qed

text \<open>Thesis: Lemma 6, second half: so-farP is well-founded.  consid grows
  strictly in every iteration and is bounded by Addr, which is finite.\<close>

theorem lemma6_so_farP_wf:
  "wf {((c',s',\<sigma>'),(c,s,\<sigma>)) | c s \<sigma> c' s' \<sigma>'. so_farP c s \<sigma> c' s' (\<sigma>' :: ('a::finite,'i) state)}"
  by (rule wf_psubset_rel[where F = fst]) (auto simp: so_farP_def)

text \<open>Thesis: Lemma 7 (first conjunct of Propagate post condition):
    consid' = Addr \<and> so-farP(\<sigma>, \<sigma>') \<Rightarrow> post-Propagate\<and>1(\<sigma>, \<sigma>').\<close>

theorem lemma7_post_Propagate1:
  assumes "so_farP {} s \<sigma> UNIV s' \<sigma>'"
  shows "\<forall>x\<in>marked \<sigma>. kids x (hp \<sigma>') \<subseteq> marked \<sigma>' \<union> BadA s' \<sigma>'"
proof (intro ballI subsetI)
  fix x b assume xM: "x \<in> marked \<sigma>" and "b \<in> kids x (hp \<sigma>')"
  then obtain i where hb: "hp \<sigma>' (x,i) = Some b" unfolding kids_def by blast
  have "(x,i) \<in> s'" using assms xM unfolding so_farP_def by auto
  show "b \<in> marked \<sigma>' \<union> BadA s' \<sigma>'"
  proof (cases "b \<in> marked \<sigma>'")
    case True then show ?thesis by simp
  next
    case False
    with \<open>(x,i) \<in> s'\<close> hb have "(x,i) \<in> Bad s' \<sigma>'" unfolding Bad_def by blast
    with hb show ?thesis unfolding BadA_def by blast
  qed
qed

text \<open>Thesis: Lemma 8: \<forall>x \<in> marked \<cdot> kids(x, hp) \<subseteq> marked \<Rightarrow> reach(roots, hp) \<subseteq> marked.\<close>

theorem lemma8_kids_marked:
  assumes "roots \<sigma> \<subseteq> marked \<sigma>" and "\<forall>x\<in>marked \<sigma>. kids x (hp \<sigma>) \<subseteq> marked \<sigma>"
  shows "reach (roots \<sigma>) (hp \<sigma>) \<subseteq> marked \<sigma>"
proof (rule reach_closed[OF assms(1)])
  fix x i b assume "x \<in> marked \<sigma>" and "hp \<sigma> (x,i) = Some b"
  then have "b \<in> kids x (hp \<sigma>)" unfolding kids_def by blast
  with \<open>x \<in> marked \<sigma>\<close> assms(2) show "b \<in> marked \<sigma>" by blast
qed

text \<open>Thesis: Theorem 2, relational core.  The thesis walks backwards along the
      witness path until it meets a marked node; here the same argument is
      phrased as a closure property: because every edge leaving a marked node
      is protected, and only one protected edge may be bad, the set of marked
      nodes is closed under the child relation of the heap with the bad edge
      deleted.  The witness's source is reachable from a marked node in that
      heap, hence marked, hence its edge is a second bad edge.\<close>

theorem theorem2_core:
  fixes \<sigma> :: "('a::finite,'i::finite) state"
  assumes inv: "inv_state \<sigma>" and IB: "invB s \<sigma>"
    and SP: "\<forall>x\<in>marked \<sigma>. \<forall>i. (x,i) \<in> s"
  shows "reach (roots \<sigma>) (hp \<sigma>) \<subseteq> marked \<sigma>"
proof (rule lemma8_kids_marked[OF inv_roots_marked[OF inv]])
  show "\<forall>x\<in>marked \<sigma>. kids x (hp \<sigma>) \<subseteq> marked \<sigma>"
  proof (rule ccontr)
    assume "\<not> (\<forall>x\<in>marked \<sigma>. kids x (hp \<sigma>) \<subseteq> marked \<sigma>)"
    then obtain x i b where xM: "x \<in> marked \<sigma>" and hb: "hp \<sigma> (x,i) = Some b"
      and bM: "b \<notin> marked \<sigma>" unfolding kids_def by blast
    have xiB: "(x,i) \<in> Bad s \<sigma>" using SP xM hb bM unfolding Bad_def by blast
    have C1: "card (Bad s \<sigma>) \<le> 1" using IB unfolding invB_def by blast
    have uniq: "\<And>y j c. y \<in> marked \<sigma> \<Longrightarrow> hp \<sigma> (y,j) = Some c \<Longrightarrow> c \<notin> marked \<sigma> \<Longrightarrow> (y,j) = (x,i)"
    proof -
      fix y j c assume "y \<in> marked \<sigma>" "hp \<sigma> (y,j) = Some c" "c \<notin> marked \<sigma>"
      then have "(y,j) \<in> Bad s \<sigma>" using SP unfolding Bad_def by blast
      then show "(y,j) = (x,i)" by (rule card_le1_unique[OF finite_Bad C1 _ xiB])
    qed
    let ?d = "(hp \<sigma>)((x,i) := None)"
    have closed: "reach (marked \<sigma>) ?d \<subseteq> marked \<sigma>"
    proof (rule reach_closed[OF subset_refl])
      fix y j c assume yM: "y \<in> marked \<sigma>" and yc: "?d (y,j) = Some c"
      from yc have ne: "(y,j) \<noteq> (x,i)" by (auto split: if_splits)
      with yc have hc: "hp \<sigma> (y,j) = Some c" by (auto split: if_splits)
      show "c \<in> marked \<sigma>"
      proof (rule ccontr)
        assume "c \<notin> marked \<sigma>"
        from uniq[OF yM hc this] ne show False by simp
      qed
    qed
    from IB xiB obtain e' where e'R: "fst e' \<in> reach (marked \<sigma>) ?d"
      and ne: "e' \<noteq> (x,i)" and eq: "hp \<sigma> e' = hp \<sigma> (x,i)"
      unfolding invB_def by blast
    have yM: "fst e' \<in> marked \<sigma>" using e'R closed by blast
    have hc: "hp \<sigma> (fst e', snd e') = Some b" using eq hb by simp
    from yM hc bM have "(fst e', snd e') = (x,i)" by (rule uniq)
    with ne show False by simp
  qed
qed

text \<open>Thesis: post-Propagate (Section 4.8.1, Appendix C).\<close>

definition post_Propagate :: "('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "post_Propagate s \<sigma> s' \<sigma>' \<longleftrightarrow>
     (\<forall>x\<in>marked \<sigma>. kids x (hp \<sigma>') \<subseteq> marked \<sigma>' \<union> BadA s' \<sigma>') \<and>
     (marked \<sigma>' = marked \<sigma> \<longrightarrow> reach (roots \<sigma>') (hp \<sigma>') \<subseteq> marked \<sigma>')"

text \<open>Thesis: Theorem 2 (Propagate post condition):
    consid' = Addr \<and> so-farP(\<sigma>, \<sigma>') \<Rightarrow> post-Propagate(\<sigma>, \<sigma>').\<close>

theorem theorem2_post_Propagate:
  fixes \<sigma> \<sigma>' :: "('a::finite,'i::finite) state"
  assumes SF: "so_farP {} s \<sigma> UNIV s' \<sigma>'" and inv: "inv_state \<sigma>'" and IB: "invB s' \<sigma>'"
  shows "post_Propagate s \<sigma> s' \<sigma>'"
proof -
  have "marked \<sigma>' = marked \<sigma> \<Longrightarrow> reach (roots \<sigma>') (hp \<sigma>') \<subseteq> marked \<sigma>'"
  proof (rule theorem2_core[OF inv IB])
    assume "marked \<sigma>' = marked \<sigma>"
    then show "\<forall>x\<in>marked \<sigma>'. \<forall>i. (x,i) \<in> s'" using SF unfolding so_farP_def by auto
  qed
  with lemma7_post_Propagate1[OF SF] show ?thesis unfolding post_Propagate_def by blast
qed

section \<open>Mark (Section 4.8.1, Algorithm 7)\<close>

text \<open>Thesis: Lemma 9: any step during Mark does not increase the region
  reachable from marked: (guar-Mark(\<sigma>, \<sigma>') \<or> rely-Collector(\<sigma>, \<sigma>'))
  \<Rightarrow> reach(marked', hp') \<subseteq> reach(marked, hp).\<close>

theorem lemma9_reach_marked_mono:
  assumes inv: "inv_state \<sigma>"
    and step: "guar_Mark s \<sigma> s' \<sigma>' \<or> env_step s \<sigma> \<sigma>'"
  shows "reach (marked \<sigma>') (hp \<sigma>') \<subseteq> reach (marked \<sigma>) (hp \<sigma>)"
proof (rule reach_closed)
  show "marked \<sigma>' \<subseteq> reach (marked \<sigma>) (hp \<sigma>)"
  proof
    fix y assume yM: "y \<in> marked \<sigma>'"
    show "y \<in> reach (marked \<sigma>) (hp \<sigma>)"
    proof (cases "y \<in> marked \<sigma>")
      case True then show ?thesis by (rule reachI)
    next
      case False
      from step show ?thesis
      proof
        assume "guar_Mark s \<sigma> s' \<sigma>'"
        then consider (St) "stutter s \<sigma> s' \<sigma>'" | (En) "guar_MarkEnd s \<sigma> s' \<sigma>'"
          | (K) x where "x \<in> marked \<sigma>" "guar_MarkKids x s \<sigma> s' \<sigma>'"
          unfolding guar_Mark_def by blast
        then show ?thesis
        proof cases
          case St with yM False show ?thesis unfolding stutter_def by simp
        next
          case En with yM False show ?thesis unfolding guar_MarkEnd_def by simp
        next
          case (K x)
          then have "y \<in> kids x (hp \<sigma>)" using yM False unfolding guar_MarkKids_def by blast
          then obtain i where "hp \<sigma> (x,i) = Some y" unfolding kids_def by blast
          with K(1) show ?thesis by (rule reach_step[OF reachI])
        qed
      next
        assume "env_step s \<sigma> \<sigma>'"
        then have "y \<in> reach (roots \<sigma>) (hp \<sigma>)"
          using yM False unfolding env_step_def rely_Collector_def by blast
        then show ?thesis using inv_reach_roots_marked[OF inv] by blast
      qed
    qed
  qed
next
  fix x i b assume xR: "x \<in> reach (marked \<sigma>) (hp \<sigma>)" and hb: "hp \<sigma>' (x,i) = Some b"
  show "b \<in> reach (marked \<sigma>) (hp \<sigma>)"
  proof (cases "hp \<sigma>' (x,i) = hp \<sigma> (x,i)")
    case True
    then have "hp \<sigma> (x,i) = Some b" using hb by simp
    from xR this show ?thesis by (rule reach_step)
  next
    case False
    have "hp \<sigma>' = hp \<sigma> \<or> env_step s \<sigma> \<sigma>'"
      using step unfolding guar_Mark_def stutter_def guar_MarkEnd_def guar_MarkKids_def by blast
    with False have "env_step s \<sigma> \<sigma>'" by auto
    then have "b \<notin> garbage \<sigma>" using False hb unfolding env_step_def rely_Collector_def by blast
    then have "b \<in> free \<sigma> \<union> reach (roots \<sigma>) (hp \<sigma>)" unfolding garbage_def by blast
    then show ?thesis
      using inv_free_marked[OF inv] inv_reach_roots_marked[OF inv] reachI[of b "marked \<sigma>" "hp \<sigma>"] by blast
  qed
qed

text \<open>Thesis: so-farM, the so-far relation of the Mark loop (Section 4.8.1).\<close>

definition so_farM :: "nat \<Rightarrow> ('a,'i) state \<Rightarrow> nat \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "so_farM mc \<sigma> mc' \<sigma>' \<longleftrightarrow>
     ((card (marked \<sigma>) < card (marked \<sigma>') \<and> mc' < card (marked \<sigma>')) \<or>
      (reach (roots \<sigma>') (hp \<sigma>') \<subseteq> marked \<sigma>' \<and> mc' = card (marked \<sigma>'))) \<and>
     marked \<sigma> \<subseteq> marked \<sigma>' \<and>
     reach (marked \<sigma>') (hp \<sigma>') \<subseteq> reach (marked \<sigma>) (hp \<sigma>)"

text \<open>Thesis: Lemma 10, first half: so-farM is transitive.\<close>

theorem lemma10_so_farM_trans:
  fixes \<sigma> \<sigma>' \<sigma>'' :: "('a::finite,'i) state"
  assumes "so_farM mc \<sigma> mc' \<sigma>'" and "so_farM mc' \<sigma>' mc'' \<sigma>''"
  shows "so_farM mc \<sigma> mc'' \<sigma>''"
proof -
  have F: "finite (marked \<sigma>')" by (rule finite_subset[OF subset_UNIV finite_UNIV])
  note T1 = assms(1)[unfolded so_farM_def] and T2 = assms(2)[unfolded so_farM_def]
  have M1: "marked \<sigma> \<subseteq> marked \<sigma>'" by (rule T1[THEN conjunct2, THEN conjunct1])
  have M2: "marked \<sigma>' \<subseteq> marked \<sigma>''" by (rule T2[THEN conjunct2, THEN conjunct1])
  have R1: "reach (marked \<sigma>') (hp \<sigma>') \<subseteq> reach (marked \<sigma>) (hp \<sigma>)"
    by (rule T1[THEN conjunct2, THEN conjunct2])
  have R2: "reach (marked \<sigma>'') (hp \<sigma>'') \<subseteq> reach (marked \<sigma>') (hp \<sigma>')"
    by (rule T2[THEN conjunct2, THEN conjunct2])
  have D2: "(card (marked \<sigma>') < card (marked \<sigma>'') \<and> mc'' < card (marked \<sigma>'')) \<or>
             (reach (roots \<sigma>'') (hp \<sigma>'') \<subseteq> marked \<sigma>'' \<and> mc'' = card (marked \<sigma>''))"
    by (rule T2[THEN conjunct1])
  have "card (marked \<sigma>) \<le> card (marked \<sigma>')" by (rule card_mono[OF F M1])
  with D2 have "(card (marked \<sigma>) < card (marked \<sigma>'') \<and> mc'' < card (marked \<sigma>'')) \<or>
                (reach (roots \<sigma>'') (hp \<sigma>'') \<subseteq> marked \<sigma>'' \<and> mc'' = card (marked \<sigma>''))" by auto
  moreover have "marked \<sigma> \<subseteq> marked \<sigma>''" using M1 M2 by blast
  moreover have "reach (marked \<sigma>'') (hp \<sigma>'') \<subseteq> reach (marked \<sigma>) (hp \<sigma>)" using R1 R2 by blast
  ultimately show ?thesis unfolding so_farM_def by blast
qed

text \<open>Thesis: Lemma 10, second half: so-farM is well-founded, for iterations that
  start where testM holds (card marked \<noteq> mc).  In every iteration card
  marked either strictly increases, which it can do only finitely often since
  card marked \<le> card Addr, or stays the same, and then mc' = card marked', so
  testM is false at the start of the next iteration.  The measure is
  2 (card Addr - card marked) + (1 if testM holds, 0 if not).\<close>

theorem lemma10_so_farM_wf:
  "wf {((mc',\<sigma>'),(mc,\<sigma>)) | mc \<sigma> mc' \<sigma>'.
         card (marked \<sigma>) \<noteq> mc \<and> so_farM mc \<sigma> mc' (\<sigma>' :: ('a::finite,'i) state)}"
proof -
  define f :: "nat \<times> ('a,'i) state \<Rightarrow> nat" where
    "f = (\<lambda>(mc,\<sigma>). 2 * (card (UNIV :: 'a set) - card (marked \<sigma>)) +
                    (if mc = card (marked \<sigma>) then 0 else 1))"
  have "{((mc',\<sigma>'),(mc,\<sigma>)) | mc \<sigma> mc' \<sigma>'. card (marked \<sigma>) \<noteq> mc \<and> so_farM mc \<sigma> mc' \<sigma>'}
          \<subseteq> measure f"
  proof (rule subsetI)
    fix p :: "(nat \<times> ('a,'i) state) \<times> (nat \<times> ('a,'i) state)"
    assume "p \<in> {((mc',\<sigma>'),(mc,\<sigma>)) | mc \<sigma> mc' \<sigma>'. card (marked \<sigma>) \<noteq> mc \<and> so_farM mc \<sigma> mc' \<sigma>'}"
    then obtain mc \<sigma> mc' \<sigma>' where p: "p = ((mc',\<sigma>'),(mc,\<sigma>))" and T: "card (marked \<sigma>) \<noteq> mc"
      and S: "so_farM mc \<sigma> mc' \<sigma>'" by blast
    have N: "card (marked \<sigma>') \<le> card (UNIV :: 'a set)" by (rule card_mono) simp_all
    have M0: "marked \<sigma> \<subseteq> marked \<sigma>'" using S unfolding so_farM_def by blast
    have M: "card (marked \<sigma>) \<le> card (marked \<sigma>')" by (rule card_mono[OF _ M0]) simp
    have D: "card (marked \<sigma>) < card (marked \<sigma>') \<or> mc' = card (marked \<sigma>')"
      using S unfolding so_farM_def by blast
    have fT: "f (mc,\<sigma>) = 2 * (card (UNIV :: 'a set) - card (marked \<sigma>)) + 1"
      using T unfolding f_def by auto
    from D have "f (mc',\<sigma>') < f (mc,\<sigma>)"
    proof
      assume L: "card (marked \<sigma>) < card (marked \<sigma>')"
      have "f (mc',\<sigma>') \<le> 2 * (card (UNIV :: 'a set) - card (marked \<sigma>')) + 1"
        unfolding f_def by simp
      also have "\<dots> < 2 * (card (UNIV :: 'a set) - card (marked \<sigma>)) + 1" using L N by arith
      also have "\<dots> = f (mc,\<sigma>)" by (rule fT[symmetric])
      finally show ?thesis .
    next
      assume E: "mc' = card (marked \<sigma>')"
      have "f (mc',\<sigma>') = 2 * (card (UNIV :: 'a set) - card (marked \<sigma>'))"
        using E unfolding f_def by simp
      also have "\<dots> \<le> 2 * (card (UNIV :: 'a set) - card (marked \<sigma>))" using M by arith
      also have "\<dots> < f (mc,\<sigma>)" using fT by simp
      finally show ?thesis .
    qed
    with p show "p \<in> measure f" by simp
  qed
  then show ?thesis by (rule wf_subset[OF wf_measure])
qed

text \<open>Thesis: Lemma 11 (first conjunct of Mark post condition):
    card marked' = mc' \<and> so-farM(\<sigma>, \<sigma>') \<Rightarrow> reach(roots, hp') \<subseteq> marked'.\<close>

theorem lemma11_post_Mark1:
  assumes "card (marked \<sigma>') = mc'" and "so_farM mc \<sigma> mc' \<sigma>'"
  shows "reach (roots \<sigma>') (hp \<sigma>') \<subseteq> marked \<sigma>'"
  using assms unfolding so_farM_def by auto

text \<open>Thesis: Lemma 12 (second conjunct of Mark post condition):
    so-farM(\<sigma>, \<sigma>') \<Rightarrow> marked' \<subseteq> reach(marked, hp).
  The thesis also assumes card marked' = mc', which the proof does not need.\<close>

theorem lemma12_post_Mark2:
  assumes "so_farM mc \<sigma> mc' \<sigma>'"
  shows "marked \<sigma>' \<subseteq> reach (marked \<sigma>) (hp \<sigma>)"
  using assms reach_refl[of "marked \<sigma>'" "hp \<sigma>'"] unfolding so_farM_def by blast

text \<open>Thesis: post-Mark (Section 4.8.1, Appendix C):
    reach(roots, hp') \<subseteq> marked' \<and> marked' \<subseteq> reach(marked, hp) \<and> s' = {}.\<close>

definition post_Mark :: "('a,'i) state \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "post_Mark \<sigma> s' \<sigma>' \<longleftrightarrow> reach (roots \<sigma>') (hp \<sigma>') \<subseteq> marked \<sigma>' \<and>
                          marked \<sigma>' \<subseteq> reach (marked \<sigma>) (hp \<sigma>) \<and> s' = {}"

text \<open>Thesis: Corollary 1 (upper bound for garbage):
    post-Mark(\<sigma>, \<sigma>') \<Rightarrow> (garbage \<inter> marked') \<subseteq> (garbage \<inter> reach(marked, hp)).\<close>

theorem corollary1_garbage_bound:
  assumes "post_Mark \<sigma> s' \<sigma>'"
  shows "garbage \<sigma> \<inter> marked \<sigma>' \<subseteq> garbage \<sigma> \<inter> reach (marked \<sigma>) (hp \<sigma>)"
  using assms unfolding post_Mark_def by blast

text \<open>Thesis: The final step of Mark (\<open>endM\<close> in the thesis) resets \<open>s\<close> and changes
      nothing else.\<close>

definition endM :: "('a,'i) state \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "endM \<sigma>' s'' \<sigma>'' \<longleftrightarrow> hp \<sigma>'' = hp \<sigma>' \<and> roots \<sigma>'' = roots \<sigma>' \<and> free \<sigma>'' = free \<sigma>' \<and>
                        marked \<sigma>'' = marked \<sigma>' \<and> s'' = {}"

text \<open>Thesis: Theorem 3 (Mark post condition):
    card marked' = mc' \<and> so-farM(\<sigma>, \<sigma>') \<and> endM(\<sigma>', \<sigma>'') \<Rightarrow> post-Mark(\<sigma>, \<sigma>'').\<close>

theorem theorem3_post_Mark:
  assumes "card (marked \<sigma>') = mc'" and "so_farM mc \<sigma> mc' \<sigma>'" and "endM \<sigma>' s'' \<sigma>''"
  shows "post_Mark \<sigma> s'' \<sigma>''"
  using lemma11_post_Mark1[OF assms(1,2)] lemma12_post_Mark2[OF assms(2)] assms(3)
  unfolding post_Mark_def endM_def by auto

end
