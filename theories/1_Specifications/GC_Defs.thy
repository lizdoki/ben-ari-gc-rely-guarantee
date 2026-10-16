(*  Mechanisation of
    "Concurrency Verification Using a Rely/Guarantee Approach"
    Liz Yevdokimov, ANU Honours thesis (revised October 2026), Chapter 4
    (Ben-Ari garbage collector).

    GC_Defs: the shared state and the basic definitions of Section 4.2,
    together with library-style facts about reachability that the later
    theories use.  Thesis Definition numbers are given in comments.        *)

theory GC_Defs
  imports Main
begin

section \<open>The address space, the heap and the shared state (Section 4.2)\<close>

text \<open>Addresses and indices are type variables; where cardinalities matter
      they carry the sort @{class finite}.  A heap is a partial map from edges
      to addresses; @{term "h (a,i) = None"} is the thesis's
      \<open>(a,i) \<notin> dom hp\<close> (the \<open>null\<close> convention).\<close>

type_synonym ('a,'i) heap = "('a \<times> 'i) \<rightharpoonup> 'a"

record ('a,'i) state =
  hp     :: "('a,'i) heap"
  roots  :: "'a set"
  free   :: "'a set"
  marked :: "'a set"

subsection \<open>Definitions 2--5: kids, child relation, paths, reachability\<close>

definition kids :: "'a \<Rightarrow> ('a,'i) heap \<Rightarrow> 'a set" where
  "kids a h = {b. \<exists>i. h (a,i) = Some b}"

definition child_rel :: "('a,'i) heap \<Rightarrow> ('a \<times> 'a) set" where
  "child_rel h = {(a,b). b \<in> kids a h}"

text \<open>Definition 5.  Paths (Definition 4) are represented by the reflexive
      transitive closure; Lemma 21 of the thesis (paths iff closure) is the
      library's characterisation of @{term "r\<^sup>*"}.\<close>

definition reach :: "'a set \<Rightarrow> ('a,'i) heap \<Rightarrow> 'a set" where
  "reach S h = {b. \<exists>a\<in>S. (a,b) \<in> (child_rel h)\<^sup>*}"

subsection \<open>Definition 1: garbage, and the state invariant (Section 4.4.2)\<close>

definition garbage :: "('a,'i) state \<Rightarrow> 'a set" where
  "garbage \<sigma> = UNIV - (free \<sigma> \<union> reach (roots \<sigma>) (hp \<sigma>))"

text \<open>The weakened invariant of Section 4.4.2 (at most one node may be both
      free and reachable while a Malloc is in progress).\<close>

definition inv_state :: "('a,'i) state \<Rightarrow> bool" where
  "inv_state \<sigma> \<longleftrightarrow>
     free \<sigma> \<union> roots \<sigma> \<subseteq> marked \<sigma> \<and>
     card (free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>)) \<le> 1 \<and>
     (\<forall>a\<in>free \<sigma>. \<forall>i. (a,i) \<notin> dom (hp \<sigma>))"

section \<open>Facts about reachability\<close>

lemma child_relI: "h (a,i) = Some b \<Longrightarrow> (a,b) \<in> child_rel h"
  unfolding child_rel_def kids_def by auto

lemma child_relE: "(a,b) \<in> child_rel h \<Longrightarrow> \<exists>i. h (a,i) = Some b"
  unfolding child_rel_def kids_def by auto

lemma reach_refl: "S \<subseteq> reach S h"
  unfolding reach_def by auto

lemma reachI: "a \<in> S \<Longrightarrow> a \<in> reach S h"
  unfolding reach_def by auto

lemma reach_mono: "S \<subseteq> T \<Longrightarrow> reach S h \<subseteq> reach T h"
  unfolding reach_def by auto

lemma reach_step: "a \<in> reach S h \<Longrightarrow> h (a,i) = Some b \<Longrightarrow> b \<in> reach S h"
  unfolding reach_def using child_relI[of h a i b] by (blast intro: rtrancl_into_rtrancl)

lemma reach_trans: "a \<in> reach S h \<Longrightarrow> b \<in> reach {a} h \<Longrightarrow> b \<in> reach S h"
  unfolding reach_def by (blast intro: rtrancl_trans)

text \<open>The induction principle we use throughout: a set closed under the
      child relation contains everything reachable from a subset of it.\<close>

lemma reach_closed:
  assumes ST: "S \<subseteq> T"
    and cl: "\<And>x i b. x \<in> T \<Longrightarrow> h (x,i) = Some b \<Longrightarrow> b \<in> T"
  shows "reach S h \<subseteq> T"
proof (rule subsetI)
  fix b assume "b \<in> reach S h"
  then have "\<exists>a\<in>S. (a,b) \<in> (child_rel h)\<^sup>*" unfolding reach_def by (rule CollectD)
  then obtain a where aS: "a \<in> S" and ab: "(a,b) \<in> (child_rel h)\<^sup>*" by blast
  from ST aS have aT: "a \<in> T" by (rule subsetD)
  from ab show "b \<in> T"
  proof (induct rule: rtrancl_induct)
    case base
    show ?case by (rule aT)
  next
    case (step y z)
    from child_relE[OF step(2)] obtain i where hz: "h (y,i) = Some z" by blast
    from step(3) hz show ?case by (rule cl)
  qed
qed

lemma reach_map_le:
  assumes "h' \<subseteq>\<^sub>m h"
  shows "reach S h' \<subseteq> reach S h"
proof (rule reach_closed)
  show "S \<subseteq> reach S h" by (rule reach_refl)
next
  fix x i b assume "x \<in> reach S h" and "h' (x,i) = Some b"
  then have "h (x,i) = Some b" using assms unfolding map_le_def by (metis domI)
  with \<open>x \<in> reach S h\<close> show "b \<in> reach S h" by (rule reach_step)
qed

lemma map_le_del: "h(e := None) \<subseteq>\<^sub>m h"
  unfolding map_le_def by auto

lemma reach_del: "reach S (h(e := None)) \<subseteq> reach S h"
  by (rule reach_map_le[OF map_le_del])

text \<open>The key fact behind Lemma 2 of the thesis (Figure 4.20): a path that
      uses an edge pointing at \<open>c\<close> can be replaced by a path from \<open>c\<close> that
      avoids the edge.\<close>

lemma reach_upd:
  "reach S (d(e \<mapsto> c)) \<subseteq> reach (S \<union> {c}) d"
proof (rule reach_closed)
  show "S \<subseteq> reach (S \<union> {c}) d" using reach_refl[of "S \<union> {c}" d] by blast
next
  fix x i b
  assume xR: "x \<in> reach (S \<union> {c}) d" and xe: "(d(e \<mapsto> c)) (x,i) = Some b"
  show "b \<in> reach (S \<union> {c}) d"
  proof (cases "(x,i) = e")
    case True
    with xe have "b = c" by simp
    then show ?thesis using reach_refl[of "S \<union> {c}" d] by blast
  next
    case False
    with xe have "d (x,i) = Some b" by simp
    with xR show ?thesis by (rule reach_step)
  qed
qed

text \<open>A reachable node outside the starting set has an incoming edge from a
      reachable node (the last edge of a path).\<close>

lemma reach_last_edge:
  assumes "b \<in> reach S h" and "b \<notin> S"
  shows "\<exists>y i. h (y,i) = Some b \<and> y \<in> reach S h"
proof -
  from assms(1) have "\<exists>a\<in>S. (a,b) \<in> (child_rel h)\<^sup>*" unfolding reach_def by (rule CollectD)
  then obtain a where aS: "a \<in> S" and ab: "(a,b) \<in> (child_rel h)\<^sup>*" by blast
  from aS assms(2) have "a \<noteq> b" by auto
  from rtranclE[OF ab] this obtain y where
    ay: "(a,y) \<in> (child_rel h)\<^sup>*" and yb: "(y,b) \<in> child_rel h" by blast
  from ay aS have "y \<in> reach S h" unfolding reach_def by blast
  moreover from child_relE[OF yb] obtain i where "h (y,i) = Some b" by blast
  ultimately show ?thesis by blast
qed

lemma reach_union: "reach (S \<union> T) h = reach S h \<union> reach T h"
  unfolding reach_def by blast

text \<open>A finer version of @{thm reach_upd}: a node reachable in the heap with
      the edge \<open>e \<mapsto> c\<close> is reachable without it, or the source of \<open>e\<close> is
      reachable without it and the node is reachable from \<open>c\<close>.\<close>

lemma reach_upd_split:
  assumes "x \<in> reach S (d(e \<mapsto> c))"
  shows "x \<in> reach S d \<or> (fst e \<in> reach S d \<and> x \<in> reach {c} (d(e \<mapsto> c)))"
proof -
  let ?h = "d(e \<mapsto> c)"
  from assms have "\<exists>a\<in>S. (a,x) \<in> (child_rel ?h)\<^sup>*" unfolding reach_def by (rule CollectD)
  then obtain a where aS: "a \<in> S" and ax: "(a,x) \<in> (child_rel ?h)\<^sup>*" by blast
  from ax show ?thesis
  proof (induct rule: rtrancl_induct)
    case base
    show ?case using reachI[OF aS, of d] by blast
  next
    case (step y z)
    from child_relE[OF step(2)] obtain k where yk: "?h (y,k) = Some z" by blast
    from step(3) show ?case
    proof
      assume yR: "y \<in> reach S d"
      show ?case
      proof (cases "(y,k) = e")
        case True
        with yk have "z = c" by simp
        moreover have "fst e \<in> reach S d" using True yR by auto
        ultimately show ?thesis using reachI[of c "{c}" ?h] by blast
      next
        case False
        with yk have "d (y,k) = Some z" by simp
        with yR have "z \<in> reach S d" by (rule reach_step)
        then show ?thesis by blast
      qed
    next
      assume A: "fst e \<in> reach S d \<and> y \<in> reach {c} ?h"
      then have yc: "y \<in> reach {c} ?h" by blast
      from yc yk have "z \<in> reach {c} ?h" by (rule reach_step)
      with A show ?case by blast
    qed
  qed
qed

text \<open>Changing an outgoing edge of a reachable node keeps the node reachable.\<close>

lemma reach_self_upd:
  assumes "a \<in> reach S h"
  shows "a \<in> reach S (h((a,i) := v))"
proof -
  let ?d = "h((a,i) := None)"
  have "a \<in> reach S ?d"
  proof (cases "h (a,i)")
    case None
    then have "?d = h" by (simp add: fun_upd_idem_iff)
    with assms show ?thesis by simp
  next
    case (Some c)
    have "a \<in> reach S (?d((a,i) \<mapsto> c))" using assms by (simp add: fun_upd_idem[of h "(a,i)" "Some c", OF Some])
    from reach_upd_split[OF this] show ?thesis by auto
  qed
  moreover have D: "?d \<subseteq>\<^sub>m h((a,i) := v)" unfolding map_le_def by auto
  ultimately show ?thesis using reach_map_le[OF D, of S] by blast
qed

text \<open>Removing edges whose sources are unreachable does not change reachability.\<close>

lemma reach_map_le_unreach:
  assumes "h' \<subseteq>\<^sub>m h" and "\<forall>e \<in> dom h - dom h'. fst e \<notin> reach S h"
  shows "reach S h' = reach S h"
proof
  show "reach S h' \<subseteq> reach S h" by (rule reach_map_le[OF assms(1)])
  show "reach S h \<subseteq> reach S h'"
  proof (rule reach_closed[OF reach_refl])
    fix y k b assume yR: "y \<in> reach S h'" and yk: "h (y,k) = Some b"
    have "(y,k) \<in> dom h'"
    proof (rule ccontr)
      assume "(y,k) \<notin> dom h'"
      with yk have yk': "(y,k) \<in> dom h - dom h'" by auto
      from assms(2) yk' have "fst (y,k) \<notin> reach S h" by (rule bspec)
      then have "y \<notin> reach S h" by simp
      with yR reach_map_le[OF assms(1), of S] show False by blast
    qed
    then have "h' (y,k) = Some b" using assms(1) yk unfolding map_le_def by auto
    with yR show "b \<in> reach S h'" by (rule reach_step)
  qed
qed

text \<open>Redirecting an edge to an already reachable node adds nothing.\<close>

lemma reach_redirect_subset:
  assumes "b \<in> reach S h"
  shows "reach S (h(e \<mapsto> b)) \<subseteq> reach S h"
proof -
  have "reach S (h(e \<mapsto> b)) \<subseteq> reach (S \<union> {b}) (h(e := None))"
    using reach_upd[of S "h(e := None)" e b] by simp
  also have "\<dots> \<subseteq> reach (S \<union> {b}) h" by (rule reach_map_le[OF map_le_del])
  also have "\<dots> = reach S h \<union> reach {b} h" by (rule reach_union)
  also have "\<dots> \<subseteq> reach S h" using reach_trans[OF assms] by blast
  finally show ?thesis .
qed

lemma reach_singleton_noedges:
  assumes "\<forall>i. h (b,i) = None"
  shows "reach {b} h = {b}"
proof
  show "reach {b} h \<subseteq> {b}"
  proof (rule reach_closed[OF subset_refl])
    fix x i c assume "x \<in> {b}" "h (x,i) = Some c"
    with assms show "c \<in> {b}" by simp
  qed
  show "{b} \<subseteq> reach {b} h" by (rule reach_refl)
qed

text \<open>Redirecting an edge to a node without outgoing edges adds at most that node.\<close>

lemma reach_redirect_leaf_subset:
  assumes "\<forall>i. h (b,i) = None"
  shows "reach S (h(e \<mapsto> b)) \<subseteq> reach S h \<union> {b}"
proof -
  have "reach S (h(e \<mapsto> b)) \<subseteq> reach (S \<union> {b}) (h(e := None))"
    using reach_upd[of S "h(e := None)" e b] by simp
  also have "\<dots> \<subseteq> reach (S \<union> {b}) h" by (rule reach_map_le[OF map_le_del])
  also have "\<dots> = reach S h \<union> reach {b} h" by (rule reach_union)
  also have "\<dots> = reach S h \<union> {b}" using reach_singleton_noedges[OF assms] by simp
  finally show ?thesis .
qed

section \<open>The state invariant under single updates\<close>

text \<open>Thesis: inv-\<Sigma> (Section 4.4.2) is kept by marking (Mark-kids line 4,
  Add-to-free line 3, the Mutator's marking step) and by deleting an edge
  (Add-to-free line 2, Zap).  The thesis takes these facts for granted, since
  only states satisfying inv-\<Sigma> exist.  Both processes use them.\<close>

lemma inv_state_mark:
  assumes "inv_state \<sigma>"
  shows "inv_state (\<sigma>\<lparr>marked := marked \<sigma> \<union> S\<rparr>)"
  using assms unfolding inv_state_def by auto

lemma inv_state_del:
  fixes \<sigma> :: "('a::finite,'i) state"
  assumes "inv_state \<sigma>"
  shows "inv_state (\<sigma>\<lparr>hp := (hp \<sigma>)(e := None)\<rparr>)"
proof -
  have F: "finite (free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>))" by (rule finite_subset[OF subset_UNIV finite_UNIV])
  have "free \<sigma> \<inter> reach (roots \<sigma>) ((hp \<sigma>)(e := None)) \<subseteq> free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>)"
    using reach_del[of "roots \<sigma>" "hp \<sigma>" e] by blast
  from card_mono[OF F this] assms show ?thesis unfolding inv_state_def by (auto simp: domIff)
qed

section \<open>Small set-theoretic helpers\<close>

lemma card_ge_2:
  assumes "finite A" "a \<in> A" "b \<in> A" "a \<noteq> b"
  shows "2 \<le> card A"
proof -
  have S: "{a,b} \<subseteq> A" using assms by auto
  have "card {a,b} \<le> card A" by (rule card_mono[OF assms(1) S])
  moreover have "card {a,b} = 2" using assms(4) by simp
  ultimately show ?thesis by linarith
qed

lemma card_le1_unique:
  assumes "finite A" "card A \<le> 1" "a \<in> A" "b \<in> A"
  shows "a = b"
proof (rule ccontr)
  assume "a \<noteq> b"
  with card_ge_2[OF assms(1) assms(3) assms(4)] have "2 \<le> card A" by blast
  with assms(2) show False by linarith
qed

lemma fun_upd_same_del:
  assumes "\<forall>e'. e' \<noteq> e \<longrightarrow> h' e' = h e'"
  shows "h'(e := None) = h(e := None)"
  using assms by (auto simp: fun_eq_iff)

text \<open>Mechanisation only: well-foundedness of a relation along which a finite set
  strictly grows (used for the so-far relations, Lemmas 5, 6, 13 and 14).\<close>

lemma card_compl_psubset:
  fixes c c' :: "'a::finite set"
  assumes "c \<subset> c'"
  shows "card (UNIV - c') < card (UNIV - c)"
proof (rule psubset_card_mono)
  show "finite (UNIV - c)" by simp
  from assms obtain y where y: "y \<in> c'" "y \<notin> c" by blast
  then show "UNIV - c' \<subset> UNIV - c" using assms by blast
qed

lemma wf_psubset_rel:
  fixes F :: "'b \<Rightarrow> 'a::finite set"
  assumes "\<And>p q. (p,q) \<in> r \<Longrightarrow> F q \<subset> F p"
  shows "wf r"
proof -
  have "r \<subseteq> measure (\<lambda>p. card (UNIV - F p))"
  proof (rule subsetI)
    fix pq assume pq_r: "pq \<in> r"
    obtain p q where pq: "pq = (p,q)" by (cases pq)
    from pq_r pq have "(p,q) \<in> r" by simp
    then have "F q \<subset> F p" by (rule assms)
    then have "card (UNIV - F p) < card (UNIV - F q)" by (rule card_compl_psubset)
    with pq show "pq \<in> measure (\<lambda>p. card (UNIV - F p))" by simp
  qed
  then show ?thesis by (rule wf_subset[OF wf_measure])
qed

end
