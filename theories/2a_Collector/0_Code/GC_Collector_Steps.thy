(*  GC_Collector_Steps: what a single step of the Collector's code may do.

    PART 2 of the mechanisation, for the Collector (folder 2a_Collector):
    why the Collector's code (Appendix C) meets its specification
    (GC_Collector_Spec).  It follows Sections 4.7 and 4.8.  For each
    subsection of 4.8 there is first a theory with the thesis's lemmas and
    theorems, in the thesis's order (they are about steps and relations, and
    mention no code), and then a theory (X_Sat) proving that that part of the
    code meets its specification, using them:
      Appendix C      GC_Collector_Steps, GC_Code   the steps, the code
      Section 4.7     GC_Invariant                  invB, Lemmas 1-4
      Section 4.8.1   GC_Mark, GC_Mark_Sat          Mark-kids, Propagate, Mark
      Section 4.8.2   GC_Unmark, GC_Unmark_Sat      Unmark
      Section 4.8.3   GC_Sweep                      Lemma 14, Theorem 5
      Section 4.8.4   GC_Safety, GC_Sweep_Sat       Add-to-free and Sweep
      Section 4.8.5   GC_Collector_Post,            Unmark; Mark; Sweep
                      GC_Collector                    (Collector_sat)
    The proofs that Add-to-free and Sweep meet their specifications use the
    safety invariants of Section 4.8.4, so GC_Sweep_Sat comes after GC_Safety.

    This theory has the guarantee condition of each phase of the code
    (Appendix C), the Add-to-free invariant invA (Section 4.8.4), and
    step-Collector (Section 4.7.2): the facts about a single program step of
    the Collector that the lemmas of Sections 4.7 and 4.8 use.

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
      guar-Unmark (Appendix C)                      guar_Unmark
      guar-Mark-kids, guar-Mark (Appendix C)        guar_MarkKids, guar_MarkEnd,
                                                      guar_Mark
      guar-Sweep, guar-Add-to-free (Appendix C)     guar_Sweep, guar_AddToFree
      invA (Section 4.8.4)                          invA
      step-Collector (Section 4.7.2)                step_Collector           *)

theory GC_Collector_Steps
  imports GC_Collector_Spec
begin

section \<open>Guarantee conditions of the Collector phases (Appendix C)\<close>

text \<open>Mechanisation only: each relation below describes a single atomic
  program step; s and s' are the protected set before and after the step.  A
  step that only changes the Collector's bookkeeping variables (consid,
  checked, mc) leaves the shared state and s unchanged.\<close>

definition stutter :: "('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "stutter s \<sigma> s' \<sigma>' \<longleftrightarrow> hp \<sigma>' = hp \<sigma> \<and> roots \<sigma>' = roots \<sigma> \<and> free \<sigma>' = free \<sigma> \<and>
                          marked \<sigma>' = marked \<sigma> \<and> s' = s"

text \<open>Thesis: guar-Unmark (Appendix C), with s = {} before and after the
  step.\<close>

definition guar_Unmark :: "('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "guar_Unmark s \<sigma> s' \<sigma>' \<longleftrightarrow> hp \<sigma>' = hp \<sigma> \<and> roots \<sigma>' = roots \<sigma> \<and> free \<sigma>' = free \<sigma> \<and>
                              marked \<sigma>' \<subseteq> marked \<sigma> \<and> s = {} \<and> s' = {}"

text \<open>Thesis: one atomic step of Mark-kids(x) (Appendix C): the target of one
  edge of x is marked and the edge is protected in the same step
  (Algorithm 6, line 4).\<close>

definition guar_MarkKids :: "'a \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "guar_MarkKids x s \<sigma> s' \<sigma>' \<longleftrightarrow> hp \<sigma>' = hp \<sigma> \<and> roots \<sigma>' = roots \<sigma> \<and> free \<sigma>' = free \<sigma> \<and>
     marked \<sigma> \<subseteq> marked \<sigma>' \<and> s \<subseteq> s' \<and>
     marked \<sigma>' - marked \<sigma> \<subseteq> kids x (hp \<sigma>) \<and>
     (\<forall>e\<in>s' - s. e \<notin> dom (hp \<sigma>) \<or> (\<exists>b. hp \<sigma> e = Some b \<and> b \<in> marked \<sigma>'))"

text \<open>Thesis: the final step of Mark resets the protected set (Algorithm 4,
  line 5).\<close>

definition guar_MarkEnd :: "('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "guar_MarkEnd s \<sigma> s' \<sigma>' \<longleftrightarrow> hp \<sigma>' = hp \<sigma> \<and> roots \<sigma>' = roots \<sigma> \<and> free \<sigma>' = free \<sigma> \<and>
                               marked \<sigma>' = marked \<sigma> \<and> s' = {}"

text \<open>Thesis: guar-Mark (Appendix C): a step of Mark is a step of Mark-kids(x)
  for a marked x, its final step, or a step that changes only its
  bookkeeping variables.\<close>

definition guar_Mark :: "('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "guar_Mark s \<sigma> s' \<sigma>' \<longleftrightarrow> stutter s \<sigma> s' \<sigma>' \<or> guar_MarkEnd s \<sigma> s' \<sigma>' \<or>
                            (\<exists>x\<in>marked \<sigma>. guar_MarkKids x s \<sigma> s' \<sigma>')"

text \<open>Thesis: guar-Sweep and guar-Add-to-free (Appendix C).  These relations
  do not mention the protected set: s = {} throughout Sweep, which is
  recorded in step_Collector below.  dom (hp - hp') of the thesis is
  dom hp - dom hp' here, since hp' \<subseteq> hp.\<close>

definition guar_Sweep :: "('a,'i) state \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "guar_Sweep \<sigma> \<sigma>' \<longleftrightarrow> roots \<sigma>' = roots \<sigma> \<and>
     free \<sigma> \<subseteq> free \<sigma>' \<and> marked \<sigma> \<subseteq> marked \<sigma>' \<and> hp \<sigma>' \<subseteq>\<^sub>m hp \<sigma>"

definition guar_AddToFree :: "'a \<Rightarrow> ('a,'i) state \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "guar_AddToFree x \<sigma> \<sigma>' \<longleftrightarrow> roots \<sigma>' = roots \<sigma> \<and>
     marked \<sigma> \<subseteq> marked \<sigma>' \<and> free \<sigma> \<subseteq> free \<sigma>' \<and> hp \<sigma>' \<subseteq>\<^sub>m hp \<sigma> \<and>
     marked \<sigma>' - marked \<sigma> \<subseteq> {x} \<and> free \<sigma>' - free \<sigma> \<subseteq> {x} \<and>
     dom (hp \<sigma>) - dom (hp \<sigma>') \<subseteq> {x} \<times> UNIV"

text \<open>Thesis: the Add-to-free invariant invA (Section 4.8.4): the node being
  freed is garbage until it is added to free.  Lemmas 17 and 18 are in
  GC_Safety.\<close>

definition invA :: "'a \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "invA x \<sigma> \<longleftrightarrow> x \<notin> reach (roots \<sigma>) (hp \<sigma>) \<and> x \<notin> free \<sigma>"

section \<open>step-Collector (Section 4.7.2)\<close>

text \<open>Thesis: step-Collector (Section 4.7.2).  The thesis writes
  step-Collector(\<sigma>,\<sigma>') when \<sigma> and \<sigma>' are the consecutive states of a
  single program step of the Collector.  Every such step is a step of
  Unmark, Mark or Sweep, and a step of Sweep that changes free or hp is a
  step of Add-to-free(x), taken in a state where invA(x,\<sigma>) holds (by
  pre-Add-to-free, inv-safe and Lemmas 17 and 18; this is what the proofs of
  Theorem 6 and Lemma 19 use).  The relation below records exactly these
  facts about a single step; GC_Collector proves that every atomic step of
  the Collector's code satisfies it (C_step, in Unmark_C, Mark_C and
  Sweep_C).\<close>

definition step_Collector :: "('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> ('a \<times> 'i) set \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "step_Collector s \<sigma> s' \<sigma>' \<longleftrightarrow>
     guar_Unmark s \<sigma> s' \<sigma>' \<or> guar_Mark s \<sigma> s' \<sigma>' \<or>
     (s = {} \<and> s' = {} \<and> guar_Sweep \<sigma> \<sigma>' \<and>
      ((free \<sigma>' = free \<sigma> \<and> hp \<sigma>' = hp \<sigma>) \<or> (\<exists>x. guar_AddToFree x \<sigma> \<sigma>' \<and> invA x \<sigma>)))"

text \<open>Thesis: every program step is a step of one of the three phases
  (Section 4.7.2).\<close>

lemma step_Collector_phases:
  assumes "step_Collector s \<sigma> s' \<sigma>'"
  shows "guar_Unmark s \<sigma> s' \<sigma>' \<or> guar_Mark s \<sigma> s' \<sigma>' \<or> guar_Sweep \<sigma> \<sigma>'"
  using assms unfolding step_Collector_def by blast

text \<open>Mechanisation only: the case split used by Theorem 6, Lemma 19 and
  Corollary 2: a program step either leaves hp, free and roots unchanged, or
  it is a step of Add-to-free(x) taken while invA(x,\<sigma>) holds.\<close>

lemma step_Collector_cases:
  assumes "step_Collector s \<sigma> s' \<sigma>'"
  shows "(hp \<sigma>' = hp \<sigma> \<and> free \<sigma>' = free \<sigma> \<and> roots \<sigma>' = roots \<sigma>) \<or>
         (\<exists>x. guar_AddToFree x \<sigma> \<sigma>' \<and> invA x \<sigma>)"
proof -
  have M: "guar_Mark s \<sigma> s' \<sigma>' \<Longrightarrow> hp \<sigma>' = hp \<sigma> \<and> free \<sigma>' = free \<sigma> \<and> roots \<sigma>' = roots \<sigma>"
    unfolding guar_Mark_def stutter_def guar_MarkEnd_def guar_MarkKids_def by blast
  have U: "guar_Unmark s \<sigma> s' \<sigma>' \<Longrightarrow> hp \<sigma>' = hp \<sigma> \<and> free \<sigma>' = free \<sigma> \<and> roots \<sigma>' = roots \<sigma>"
    unfolding guar_Unmark_def by blast
  have S: "guar_Sweep \<sigma> \<sigma>' \<Longrightarrow> roots \<sigma>' = roots \<sigma>"
    unfolding guar_Sweep_def by blast
  from assms M U S show ?thesis unfolding step_Collector_def by blast
qed

end
