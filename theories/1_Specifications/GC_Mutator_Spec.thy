(*  GC_Mutator_Spec: the Mutator's rely and guarantee conditions
    (Sections 4.5.5 and 4.6).

    PART 1 of the mechanisation (see GC_Collector_Spec).  The Mutator relies
    on guar-Collector, the Collector's guarantee (GC_Collector_Spec), and
    guarantees guar-Mutator: each of its steps is a step of Redirect, Malloc
    or Zap allowed by Section 4.6.  GC_Parallel uses this specification and
    the Collector's; Part 2 proves that the Mutator's code meets it (folder
    2b_Mutator, GC_Mutator).

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
      the Mutator's rely, guar-Collector (4.6)      rely_M
      the guarantees of Redirect, Malloc and Zap,   g_Redirect_hp, ...,
        one per atomic step (Section 4.6)             g_Zap
      guar-Mutator (Sections 4.5.5, 4.6)            guar_Mutator, guar_M     *)

theory GC_Mutator_Spec
  imports GC_Collector_Spec
begin

section \<open>The Mutator's specification (Sections 4.5.5 and 4.6)\<close>

text \<open>Thesis: the Mutator's specification (Sections 4.5.5 and 4.6):
    pre  new-risk = {}
    rely guar-Collector
    guar guar-Mutator
    post true
  Below are its rely and guarantee conditions.  A Mutator's private state is
  abstract here (type 'm), and nr_of reads new-risk from it.\<close>

text \<open>Thesis: the Mutator's rely condition, guar-Collector (the rely condition of
  each operation in Section 4.6), with inv-\<Sigma> after the step.  The Mutator's
  private state is abstract (type 'm).\<close>

definition rely_M :: "('m, ('a,'i) state) rg_rely" where
  "rely_M m \<sigma> \<sigma>' \<longleftrightarrow> guar_Collector \<sigma> \<sigma>' \<and> inv_state \<sigma>'"

text \<open>The Mutator's guarantee is written step by step, as in Section 4.6.  Each
  relation below is one conjunct of an operation's guarantee, together with
  how that step reads and changes new-risk: N is new-risk before the step and
  N' after it (Section 4.5.5 and the start of Section 4.6).\<close>

text \<open>Thesis: the first conjunct of Redirect's guarantee (Section 4.6), for its
  heap update: hp' = hp \<dagger> {(a, i) \<mapsto> b}, a, b \<in> reach(roots, hp) and
  free \<inter> reach(roots, hp) = {}.  With it, how the step changes new-risk
  (Section 4.5.5 and the start of Section 4.6): new-risk = {} before, and
  new-risk' = {(a, i)} if b \<notin> marked, else {}.\<close>

definition g_Redirect_hp :: "'a \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow>
                             ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "g_Redirect_hp a i b N \<sigma> N' \<sigma>' \<longleftrightarrow>
     a \<in> reach (roots \<sigma>) (hp \<sigma>) \<and> b \<in> reach (roots \<sigma>) (hp \<sigma>) \<and>
     free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {} \<and> N = {} \<and>
     \<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((a,i) \<mapsto> b)\<rparr> \<and> N' = (if b \<in> marked \<sigma> then {} else {(a,i)})"

text \<open>Thesis: the second conjunct of Redirect's guarantee, for its marking step:
  marked' = marked \<union> {b}, hp(a, i) = b and b \<in> reach(roots, hp); with
  new-risk \<subseteq> {(a, i)} before and new-risk' = {}.\<close>

definition g_Redirect_mk :: "'a \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow>
                             ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "g_Redirect_mk a i b N \<sigma> N' \<sigma>' \<longleftrightarrow>
     hp \<sigma> (a,i) = Some b \<and> b \<in> reach (roots \<sigma>) (hp \<sigma>) \<and> N \<subseteq> {(a,i)} \<and>
     \<sigma>' = \<sigma>\<lparr>marked := marked \<sigma> \<union> {b}\<rparr> \<and> N' = {}"

text \<open>Thesis: the first conjunct of Malloc's guarantee, for its heap update:
  hp' = hp \<dagger> {(a, i) \<mapsto> b}, a \<in> reach(roots, hp), b \<in> free and
  free \<inter> reach(roots, hp) = {}; with new-risk = {} before and after.\<close>

definition g_Malloc_hp :: "'a \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow>
                           ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "g_Malloc_hp a i b N \<sigma> N' \<sigma>' \<longleftrightarrow>
     a \<in> reach (roots \<sigma>) (hp \<sigma>) \<and> b \<in> free \<sigma> \<and>
     free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {} \<and> N = {} \<and>
     \<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((a,i) \<mapsto> b)\<rparr> \<and> N' = {}"

text \<open>Thesis: the second conjunct of Malloc's guarantee, for its free step:
  free' = free - {b} and hp(a, i) = b, with b \<in> free; new-risk = {} before
  and after.\<close>

definition g_Malloc_fr :: "'a \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow>
                           ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "g_Malloc_fr a i b N \<sigma> N' \<sigma>' \<longleftrightarrow>
     hp \<sigma> (a,i) = Some b \<and> b \<in> free \<sigma> \<and> N = {} \<and>
     \<sigma>' = \<sigma>\<lparr>free := free \<sigma> - {b}\<rparr> \<and> N' = {}"

text \<open>Thesis: Zap's guarantee: (a, i) is removed from hp, a \<in> reach(roots, hp)
  and free \<inter> reach(roots, hp) = {}, with Zap's pre condition (a, i) \<in> dom hp;
  new-risk = {} before and after.\<close>

definition g_Zap :: "'a \<Rightarrow> 'i \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow>
                     ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "g_Zap a i N \<sigma> N' \<sigma>' \<longleftrightarrow>
     a \<in> reach (roots \<sigma>) (hp \<sigma>) \<and> (a,i) \<in> dom (hp \<sigma>) \<and>
     free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {} \<and> N = {} \<and>
     \<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((a,i) := None)\<rparr> \<and> N' = {}"

text \<open>Thesis: guar-Mutator, used in the implication of Section 4.5.5: a step of
  the Mutator is a step of Redirect, Malloc or Zap allowed by its guarantee in
  Section 4.6, for some a, i and b, with inv-\<Sigma> before and after.  As every
  guarantee condition (Section 2.2), it is reflexive: a step that changes
  neither the shared state nor new-risk (such as the Mutator choosing its
  next operation) is allowed.\<close>

definition guar_Mutator :: "('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "guar_Mutator N \<sigma> N' \<sigma>' \<longleftrightarrow> inv_state \<sigma> \<and> inv_state \<sigma>' \<and>
     ((\<sigma>' = \<sigma> \<and> N' = N) \<or>
      (\<exists>a i b. g_Redirect_hp a i b N \<sigma> N' \<sigma>' \<or> g_Redirect_mk a i b N \<sigma> N' \<sigma>' \<or>
              g_Malloc_hp a i b N \<sigma> N' \<sigma>' \<or> g_Malloc_fr a i b N \<sigma> N' \<sigma>' \<or>
              g_Zap a i N \<sigma> N' \<sigma>'))"

text \<open>Mechanisation only: guar-Mutator as a relation on the Mutator's
  configurations; nr_of reads new-risk from the Mutator's private state.\<close>

definition guar_M :: "('m \<Rightarrow> ('a \<times> 'i) set) \<Rightarrow> ('m, ('a,'i) state) rg_conf \<Rightarrow>
                      ('m, ('a,'i) state) rg_conf \<Rightarrow> bool" where
  "guar_M nr_of c c' \<longleftrightarrow> guar_Mutator (nr_of (fst c)) (snd c) (nr_of (fst c')) (snd c')"

end
