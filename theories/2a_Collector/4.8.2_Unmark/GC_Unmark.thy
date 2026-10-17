(*  GC_Unmark: Section 4.8.2 of the thesis -- the lemmas and theorems of
    Unmark.
      Lemma 13 / Theorem 4 -- so-far transitive and well-founded, post
                              condition
    Also, beyond the thesis, what Unmark guarantees about pointers, which
    Sublemma 2 (Section 4.8.5) uses (no_new_ptr).  GC_Unmark_Sat uses these
    results to prove that Unmark meets its specification.

    HOW TO READ THE LABELS.  Each definition and theorem below, or each group
    of them, has a text block saying how it relates to the thesis:
      "Thesis:"             it is that part of the thesis;
      "Beyond the thesis:"  the thesis states or argues it informally or not
                            at all; the label says which part of the thesis
                            it makes precise or supports;
      "Mechanisation only:" a helper needed only for the Isabelle proof.
    Section, lemma and theorem numbers are those of the thesis.  *)

theory GC_Unmark
  imports GC_Collector_Steps
begin

section \<open>Unmark (Section 4.8.2, Algorithm 8)\<close>

text \<open>Thesis: so-farU, the so-far relation of the Unmark loop (Section 4.8.2).\<close>

definition so_farU :: "'a set \<Rightarrow> ('a,'i) state \<Rightarrow> 'a set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "so_farU c \<sigma> c' \<sigma>' \<longleftrightarrow> c \<subset> c' \<and> garbage \<sigma> \<subseteq> garbage \<sigma>' \<and>
     marked \<sigma>' \<inter> garbage \<sigma> \<subseteq> marked \<sigma> \<inter> garbage \<sigma> \<and>
     (\<forall>x \<in> garbage \<sigma> \<inter> (c' - c). x \<notin> marked \<sigma>')"

text \<open>Thesis: Lemma 13, first half: so-farU is transitive.\<close>

theorem lemma13_so_farU_trans:
  assumes "so_farU c \<sigma> c' \<sigma>'" and "so_farU c' \<sigma>' c'' \<sigma>''"
  shows "so_farU c \<sigma> c'' \<sigma>''"
proof -
  from assms have 1: "c \<subset> c'" "c' \<subset> c''" "garbage \<sigma> \<subseteq> garbage \<sigma>'" "garbage \<sigma>' \<subseteq> garbage \<sigma>''"
    "marked \<sigma>' \<inter> garbage \<sigma> \<subseteq> marked \<sigma> \<inter> garbage \<sigma>"
    "marked \<sigma>'' \<inter> garbage \<sigma>' \<subseteq> marked \<sigma>' \<inter> garbage \<sigma>'"
    and 2: "\<forall>x \<in> garbage \<sigma> \<inter> (c' - c). x \<notin> marked \<sigma>'"
    and 3: "\<forall>x \<in> garbage \<sigma>' \<inter> (c'' - c'). x \<notin> marked \<sigma>''"
    unfolding so_farU_def by blast+
  have cc: "c \<subset> c''" using 1(1) 1(2) by (rule psubset_trans)
  have G: "garbage \<sigma> \<subseteq> garbage \<sigma>''" using 1(3) 1(4) by blast
  have MG: "marked \<sigma>'' \<inter> garbage \<sigma> \<subseteq> marked \<sigma> \<inter> garbage \<sigma>" using 1(3) 1(5) 1(6) by blast
  have "\<forall>x \<in> garbage \<sigma> \<inter> (c'' - c). x \<notin> marked \<sigma>''"
  proof
    fix x assume x: "x \<in> garbage \<sigma> \<inter> (c'' - c)"
    show "x \<notin> marked \<sigma>''"
    proof (cases "x \<in> c'")
      case True
      with x 2 have "x \<notin> marked \<sigma>'" by blast
      with x 1(3) 1(6) show ?thesis by blast
    next
      case False
      with x 1(3) 3 show ?thesis by blast
    qed
  qed
  with cc G MG show ?thesis unfolding so_farU_def by blast
qed

text \<open>Thesis: Lemma 13, second half: so-farU is well-founded.  consid grows
  strictly in every iteration and is bounded by Addr, which is finite.\<close>

theorem lemma13_so_farU_wf:
  "wf {((c',\<sigma>'),(c,\<sigma>)) | c \<sigma> c' \<sigma>'. so_farU c \<sigma> c' (\<sigma>' :: ('a::finite,'i) state)}"
  by (rule wf_psubset_rel[where F = fst]) (auto simp: so_farU_def)

text \<open>Thesis: post-Unmark (Section 4.8.2, Appendix C): garbage \<inter> marked' = {}.\<close>

definition post_Unmark :: "('a,'i) state \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "post_Unmark \<sigma> \<sigma>' \<longleftrightarrow> garbage \<sigma> \<inter> marked \<sigma>' = {}"

text \<open>Thesis: Theorem 4 (Unmark post condition):
    consid' = Addr \<and> so-farU(\<sigma>, \<sigma>') \<Rightarrow> post-Unmark(\<sigma>, \<sigma>').\<close>

theorem theorem4_post_Unmark:
  assumes "so_farU {} \<sigma> UNIV \<sigma>'"
  shows "post_Unmark \<sigma> \<sigma>'"
  using assms unfolding so_farU_def post_Unmark_def by auto

text \<open>Beyond the thesis: what Unmark guarantees about pointers, as a relation
      between its first and last states: no pointer out of the old free or
      reachable region points outside it.  Sublemma 2 (Section 4.8.5) uses
      it; GC_Unmark_Sat proves it as part of Unmark's post condition
      (\<open>U_post\<close>).\<close>

definition no_new_ptr :: "('a,'i) state \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "no_new_ptr \<sigma> \<sigma>' \<longleftrightarrow> (\<forall>x \<in> free \<sigma> \<union> reach (roots \<sigma>) (hp \<sigma>). \<forall>i b.
       hp \<sigma>' (x,i) = Some b \<longrightarrow> b \<in> free \<sigma> \<union> reach (roots \<sigma>) (hp \<sigma>))"

end
