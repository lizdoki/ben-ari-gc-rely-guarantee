(*  RG_Semantics: rely/guarantee specifications and the parallel rule.

    A semantics of rely/guarantee quadruples over computations (finite
    prefixes of Aczel traces: program steps and environment steps), and the
    rule for parallel composition, proved sound.  Nothing here is specific
    to the garbage collector.

    HOW TO READ THE LABELS.  Each definition and theorem below has a text
    block saying how it relates to the thesis:
      "Thesis:"             it is that part of the thesis;
      "Beyond the thesis:"  the thesis states or argues it informally or not
                            at all; the label says which part of the thesis
                            it makes precise or supports;
      "Mechanisation only:" a helper needed only for the Isabelle proof.
    Section, lemma and theorem numbers are those of the thesis.

      thesis                                        Isabelle
      ------------------------------------------    ---------------------
      Aczel trace (Section 2.2, Figure 2.2)         rg_reach
      {p, r} c {g, q} (Section 2.2)                 rg_sat
      possible values (Section 2.3)                 history function h
      proof pattern of Sections 4.7 and 4.8.4       rg_reach_invariant,
                                                    rg_sat_inv
      rule of consequence                           rg_conseq
      A \<parallel> B (Section 2.2)                            par, hpar
      the parallel rule of Section 2.2              rg_parallel_plain
      beyond the thesis: the rule generalised for   rg_parallel,
        Section 4.5.5, and its soundness proof      par_project

    Relative to the plain rule of Section 2.2 of the thesis, two things are
    general here, because the garbage collector needs them:
      - a rely or guarantee condition may refer to the component's own
        private variables (rely-Collector refers to the Collector's ghost s);
      - the side conditions of the parallel rule need only hold in states
        satisfying a coupling predicate J between the two components' private
        variables and the shared state, which every step must preserve.  This
        is the quantification over an abstract set of Yatapanage (2026, arXiv:
        2609.27392), with J playing the role of the restricting property
        (consistent(s, sigma) in Section 4.5.5).
    With J true and conditions that ignore private variables, the rule is the
    plain one (rg_parallel_plain).                                            *)

theory RG_Semantics
  imports Main
begin

section \<open>Components and computations\<close>

text \<open>A configuration is a pair of a component's private state and the shared
  state.  A component is given by its atomic program steps.  An environment
  step changes only the shared state, and must satisfy the rely condition,
  which may depend on the component's own private variables.  A history
  function \<open>h\<close> updates the component's history (ghost) variables after every
  step, whichever process takes it; this is how the possible-values notation
  (Section 2.3 of the thesis) is given meaning.  Components without history
  variables use \<open>\<lambda>l s. l\<close>.\<close>

text \<open>Thesis: Section 2.2.  A configuration (l, s) is one state of an Aczel
  trace, split into the process's private variables l (the owns variables of
  a VDM specification, including ghost variables such as the Collector's s and
  the Mutator's new-risk) and the shared state s (\<Sigma>).  rg_prog = the
  process's program steps; rg_rely = a rely condition, which may read the
  process's own private variables; rg_hist = how history variables are
  updated after every step.\<close>

type_synonym ('l,'s) rg_conf = "'l \<times> 's"
type_synonym ('l,'s) rg_prog = "('l,'s) rg_conf \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> bool"
type_synonym ('l,'s) rg_rely = "'l \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
type_synonym ('l,'s) rg_hist = "'l \<Rightarrow> 's \<Rightarrow> 'l"

text \<open>Mechanisation only: the history function of a process without history
  variables.\<close>

definition no_hist :: "('l,'s) rg_hist" where
  "no_hist l s = l"

text \<open>Thesis: Aczel traces (Section 2.2, Figure 2.2).  rg_reach C R h c0 l s
  holds when some finite trace of C from c0 reaches (l, s).  Rule start is
  the first state, rule prog a program step, and rule env an environment step
  satisfying the rely condition R.  Environment steps may come at any point,
  including after the process's last program step.\<close>

inductive rg_reach :: "('l,'s) rg_prog \<Rightarrow> ('l,'s) rg_rely \<Rightarrow> ('l,'s) rg_hist \<Rightarrow>
                       ('l,'s) rg_conf \<Rightarrow> 'l \<Rightarrow> 's \<Rightarrow> bool"
  for C :: "('l,'s) rg_prog" and R :: "('l,'s) rg_rely" and h :: "('l,'s) rg_hist"
    and c0 :: "('l,'s) rg_conf"
where
  start: "rg_reach C R h c0 (fst c0) (snd c0)"
| prog:  "rg_reach C R h c0 l s \<Longrightarrow> C (l,s) (l',s') \<Longrightarrow> rg_reach C R h c0 (h l' s') s'"
| env:   "rg_reach C R h c0 l s \<Longrightarrow> R l s s' \<Longrightarrow> rg_reach C R h c0 (h l s') s'"

text \<open>Mechanisation only: a trace with no steps.\<close>

lemma rg_reach_start: "rg_reach C R h (l,s) l s"
  using rg_reach.start[of C R h "(l,s)"] by simp

section \<open>The rely/guarantee judgement\<close>

text \<open>Thesis: the quadruple {p, r} c {g, q} of Section 2.2, written
  rg_sat C h P R G Q.  From every initial configuration satisfying the pre
  condition P, in every trace whose environment steps satisfy the rely
  condition R, every program step satisfies the guarantee G, and Q relates
  the initial configuration to every configuration reached.  Q is checked in
  every reached state, not only the last, so it can also state an invariant;
  a post condition in the thesis's sense is Q c0 c = (c has finished \<longrightarrow>
  post c0 c).\<close>

definition rg_sat :: "('l,'s) rg_prog \<Rightarrow> ('l,'s) rg_hist \<Rightarrow> (('l,'s) rg_conf \<Rightarrow> bool) \<Rightarrow>
    ('l,'s) rg_rely \<Rightarrow> (('l,'s) rg_conf \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> bool) \<Rightarrow>
    (('l,'s) rg_conf \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> bool) \<Rightarrow> bool" where
  "rg_sat C h P R G Q \<longleftrightarrow>
     (\<forall>c0 l s. P c0 \<longrightarrow> rg_reach C R h c0 l s \<longrightarrow>
        Q c0 (l,s) \<and> (\<forall>l' s'. C (l,s) (l',s') \<longrightarrow> G (l,s) (l',s')))"

text \<open>Mechanisation only: reading the post condition off a quadruple.\<close>

lemma rg_satD_post:
  assumes "rg_sat C h P R G Q" and "P c0" and "rg_reach C R h c0 l s"
  shows "Q c0 (l,s)"
  using assms unfolding rg_sat_def by blast

text \<open>Mechanisation only: reading the guarantee off a quadruple.\<close>

lemma rg_satD_guar:
  assumes "rg_sat C h P R G Q" and "P c0" and "rg_reach C R h c0 l s" and "C (l,s) (l',s')"
  shows "G (l,s) (l',s')"
  using assms unfolding rg_sat_def by blast

section \<open>Proving a component correct: stable invariants\<close>

text \<open>Thesis: the argument used throughout Sections 4.7 and 4.8.4: a property
  that holds initially, and is preserved by every program step and by every
  environment step satisfying the rely condition, holds in every state (as
  for invB in Lemmas 1-4, and for inv-safe and invA in Lemmas 15-18).\<close>

lemma rg_reach_invariant:
  assumes Rc: "rg_reach C R h c0 l s"
    and Iinit: "I (fst c0) (snd c0)"
    and Iprog: "\<And>l s l' s'. I l s \<Longrightarrow> C (l,s) (l',s') \<Longrightarrow> I (h l' s') s'"
    and Ienv: "\<And>l s s'. I l s \<Longrightarrow> R l s s' \<Longrightarrow> I (h l s') s'"
  shows "I l s"
  using Rc
proof (induction rule: rg_reach.induct)
  case start
  show ?case by (rule Iinit)
next
  case (prog la sa la' sa')
  from prog.IH prog.hyps(2) show ?case by (rule Iprog)
next
  case (env la sa sa')
  from env.IH env.hyps(2) show ?case by (rule Ienv)
qed

text \<open>Thesis: the same argument as a proof rule for a quadruple: an invariant I
  that holds initially, is preserved by program steps and is stable under the
  rely condition, and from which the post condition and the guarantee follow.
  rg_sat_guar_inv (RG_VDM) is a form of it for a quadruple already proved.\<close>

lemma rg_sat_inv:
  assumes Iinit: "\<And>c0. P c0 \<Longrightarrow> I c0 (fst c0) (snd c0)"
    and Iprog: "\<And>c0 l s l' s'. P c0 \<Longrightarrow> I c0 l s \<Longrightarrow> C (l,s) (l',s') \<Longrightarrow> I c0 (h l' s') s'"
    and Ienv: "\<And>c0 l s s'. P c0 \<Longrightarrow> I c0 l s \<Longrightarrow> R l s s' \<Longrightarrow> I c0 (h l s') s'"
    and IQ: "\<And>c0 l s. P c0 \<Longrightarrow> I c0 l s \<Longrightarrow> Q c0 (l,s)"
    and IG: "\<And>c0 l s l' s'. P c0 \<Longrightarrow> I c0 l s \<Longrightarrow> C (l,s) (l',s') \<Longrightarrow> G (l,s) (l',s')"
  shows "rg_sat C h P R G Q"
  unfolding rg_sat_def
proof (intro allI impI)
  fix c0 l s assume P: "P c0" and Rc: "rg_reach C R h c0 l s"
  have I: "I c0 l s"
  proof (rule rg_reach_invariant[where I = "I c0", OF Rc])
    show "I c0 (fst c0) (snd c0)" by (rule Iinit[OF P])
  next
    fix la sa la' sa' assume "I c0 la sa" and "C (la,sa) (la',sa')"
    then show "I c0 (h la' sa') sa'" by (rule Iprog[OF P])
  next
    fix la sa sa' assume "I c0 la sa" and "R la sa sa'"
    then show "I c0 (h la sa') sa'" by (rule Ienv[OF P])
  qed
  have Q: "Q c0 (l,s)" by (rule IQ[OF P I])
  have G: "\<forall>l' s'. C (l,s) (l',s') \<longrightarrow> G (l,s) (l',s')"
  proof (intro allI impI)
    fix l' s' assume "C (l,s) (l',s')"
    then show "G (l,s) (l',s')" by (rule IG[OF P I])
  qed
  from Q G show "Q c0 (l,s) \<and> (\<forall>l' s'. C (l,s) (l',s') \<longrightarrow> G (l,s) (l',s'))" by (rule conjI)
qed

section \<open>Consequence\<close>

text \<open>Mechanisation only: a trace under a stronger rely condition is also a
  trace under a weaker one.\<close>

lemma rg_reach_rely_mono:
  assumes Rc: "rg_reach C R h c0 l s" and RR: "\<And>l s s'. R l s s' \<Longrightarrow> R' l s s'"
  shows "rg_reach C R' h c0 l s"
  using Rc
proof (induction rule: rg_reach.induct)
  case start
  show ?case by (rule rg_reach.start)
next
  case (prog la sa la' sa')
  show ?case by (rule rg_reach.prog[OF prog.IH prog.hyps(2)])
next
  case (env la sa sa')
  show ?case by (rule rg_reach.env[OF env.IH RR[OF env.hyps(2)]])
qed

text \<open>Thesis: the rule of consequence: strengthen the pre and rely conditions,
  weaken the guarantee and post condition.  Section 2.2's parallel rule uses
  it in its side conditions gA \<or> gB \<Rrightarrow> g and p \<and> qA \<and> qB \<and> ... \<Rrightarrow> q.\<close>

lemma rg_conseq:
  assumes V: "rg_sat C h P R G Q"
    and PP: "\<And>c. P' c \<Longrightarrow> P c"
    and RR: "\<And>l s s'. R' l s s' \<Longrightarrow> R l s s'"
    and GG: "\<And>c c'. G c c' \<Longrightarrow> G' c c'"
    and QQ: "\<And>c0 c. P' c0 \<Longrightarrow> Q c0 c \<Longrightarrow> Q' c0 c"
  shows "rg_sat C h P' R' G' Q'"
  unfolding rg_sat_def
proof (intro allI impI)
  fix c0 l s assume P': "P' c0" and Rc: "rg_reach C R' h c0 l s"
  have P: "P c0" by (rule PP[OF P'])
  have Rc2: "rg_reach C R h c0 l s" by (rule rg_reach_rely_mono[OF Rc RR])
  have Q: "Q c0 (l,s)" by (rule rg_satD_post[OF V P Rc2])
  have G: "\<forall>l' s'. C (l,s) (l',s') \<longrightarrow> G' (l,s) (l',s')"
  proof (intro allI impI)
    fix l' s' assume "C (l,s) (l',s')"
    then have "G (l,s) (l',s')" by (rule rg_satD_guar[OF V P Rc2])
    then show "G' (l,s) (l',s')" by (rule GG)
  qed
  from QQ[OF P' Q] G show "Q' c0 (l,s) \<and> (\<forall>l' s'. C (l,s) (l',s') \<longrightarrow> G' (l,s) (l',s'))"
    by (rule conjI)
qed

section \<open>Parallel composition\<close>

text \<open>Thesis: A \<parallel> B (Section 2.2): a step of the composition is a program step of
  A or of B.  The other process's private variables do not change, apart from
  its history variables, which hpar updates.\<close>

definition par :: "('l1,'s) rg_prog \<Rightarrow> ('l2,'s) rg_prog \<Rightarrow> ('l1 \<times> 'l2, 's) rg_prog" where
  "par C1 C2 c c' \<longleftrightarrow>
     (C1 (fst (fst c), snd c) (fst (fst c'), snd c') \<and> snd (fst c') = snd (fst c)) \<or>
     (C2 (snd (fst c), snd c) (snd (fst c'), snd c') \<and> fst (fst c') = fst (fst c))"

text \<open>Mechanisation only: par on explicit pairs.\<close>

lemma par_iff [simp]:
  "par C1 C2 ((l1,l2),s) ((l1',l2'),s') \<longleftrightarrow>
     (C1 (l1,s) (l1',s') \<and> l2' = l2) \<or> (C2 (l2,s) (l2',s') \<and> l1' = l1)"
  unfolding par_def by simp

text \<open>Mechanisation only: after every step of A \<parallel> B, both processes' history
  variables are updated.\<close>

definition hpar :: "('l1,'s) rg_hist \<Rightarrow> ('l2,'s) rg_hist \<Rightarrow> ('l1 \<times> 'l2, 's) rg_hist" where
  "hpar h1 h2 l s = (h1 (fst l) s, h2 (snd l) s)"

text \<open>Mechanisation only: hpar on explicit pairs.\<close>

lemma hpar_iff [simp]: "hpar h1 h2 (l1,l2) s = (h1 l1 s, h2 l2 s)"
  unfolding hpar_def by simp

text \<open>Thesis: the pre condition of A \<parallel> B, as in the rule of Section 2.2
  (pA \<and> pB), with the coupling predicate J added.\<close>

definition par_pre :: "(('l1,'s) rg_conf \<Rightarrow> bool) \<Rightarrow> (('l2,'s) rg_conf \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<Rightarrow> 'l2 \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('l1 \<times> 'l2, 's) rg_conf \<Rightarrow> bool" where
  "par_pre P1 P2 J c \<longleftrightarrow>
     P1 (fst (fst c), snd c) \<and> P2 (snd (fst c), snd c) \<and> J (fst (fst c)) (snd (fst c)) (snd c)"

text \<open>Thesis: the guarantee of A \<parallel> B, gA \<or> gB, as in the rule of Section 2.2.
  A step of A satisfies gA and leaves B's private variables alone, and vice
  versa.\<close>

definition par_guar :: "(('l1,'s) rg_conf \<Rightarrow> ('l1,'s) rg_conf \<Rightarrow> bool) \<Rightarrow>
    (('l2,'s) rg_conf \<Rightarrow> ('l2,'s) rg_conf \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l2, 's) rg_conf \<Rightarrow> ('l1 \<times> 'l2, 's) rg_conf \<Rightarrow> bool" where
  "par_guar G1 G2 c c' \<longleftrightarrow>
     (G1 (fst (fst c), snd c) (fst (fst c'), snd c') \<and> snd (fst c') = snd (fst c)) \<or>
     (G2 (snd (fst c), snd c) (snd (fst c'), snd c') \<and> fst (fst c') = fst (fst c))"

text \<open>Thesis: the post condition of A \<parallel> B, as in the rule of Section 2.2
  (qA \<and> qB), with the coupling predicate J added.\<close>

definition par_post :: "(('l1,'s) rg_conf \<Rightarrow> ('l1,'s) rg_conf \<Rightarrow> bool) \<Rightarrow>
    (('l2,'s) rg_conf \<Rightarrow> ('l2,'s) rg_conf \<Rightarrow> bool) \<Rightarrow> ('l1 \<Rightarrow> 'l2 \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
    ('l1 \<times> 'l2, 's) rg_conf \<Rightarrow> ('l1 \<times> 'l2, 's) rg_conf \<Rightarrow> bool" where
  "par_post Q1 Q2 J c0 c \<longleftrightarrow>
     Q1 (fst (fst c0), snd c0) (fst (fst c), snd c) \<and>
     Q2 (snd (fst c0), snd c0) (snd (fst c), snd c) \<and>
     J (fst (fst c)) (snd (fst c)) (snd c)"

text \<open>Beyond the thesis: the soundness argument for rg_parallel: every trace of
  A \<parallel> B projects to a trace of A and a trace of B, in which each step of
  the other process is an environment step satisfying the rely condition, and
  J holds in every state.  The induction is over the trace: a step of A is a
  program step for A and, by the side condition G1R2, an environment step for
  B; and symmetrically for a step of B.\<close>

lemma par_project:
  assumes V1: "rg_sat C1 h1 P1 R1 G1 Q1"
    and V2: "rg_sat C2 h2 P2 R2 G2 Q2"
    and G1R2: "\<And>l1 l2 s l1' s'. J l1 l2 s \<Longrightarrow> G1 (l1,s) (l1',s') \<Longrightarrow>
                 R2 l2 s s' \<and> J (h1 l1' s') (h2 l2 s') s'"
    and G2R1: "\<And>l1 l2 s l2' s'. J l1 l2 s \<Longrightarrow> G2 (l2,s) (l2',s') \<Longrightarrow>
                 R1 l1 s s' \<and> J (h1 l1 s') (h2 l2' s') s'"
    and RR: "\<And>l1 l2 s s'. J l1 l2 s \<Longrightarrow> R (l1,l2) s s' \<Longrightarrow>
                 R1 l1 s s' \<and> R2 l2 s s' \<and> J (h1 l1 s') (h2 l2 s') s'"
    and P: "par_pre P1 P2 J c0"
    and Rc: "rg_reach (par C1 C2) R (hpar h1 h2) c0 l s"
  shows "rg_reach C1 R1 h1 (fst (fst c0), snd c0) (fst l) s \<and>
         rg_reach C2 R2 h2 (snd (fst c0), snd c0) (snd l) s \<and>
         J (fst l) (snd l) s"
  using Rc
proof (induction rule: rg_reach.induct)
  case start
  from P show ?case unfolding par_pre_def by (simp add: rg_reach_start)
next
  case (prog la sa la' sa')
  obtain l1 l2 where lp: "la = (l1,l2)" by (cases la)
  obtain l1' l2' where lp': "la' = (l1',l2')" by (cases la')
  have P1: "P1 (fst (fst c0), snd c0)" and P2: "P2 (snd (fst c0), snd c0)"
    using P unfolding par_pre_def by simp_all
  from prog.IH lp have c1: "rg_reach C1 R1 h1 (fst (fst c0), snd c0) l1 sa"
    and c2: "rg_reach C2 R2 h2 (snd (fst c0), snd c0) l2 sa" and J: "J l1 l2 sa" by simp_all
  from prog.hyps(2) lp lp' have "(C1 (l1,sa) (l1',sa') \<and> l2' = l2) \<or> (C2 (l2,sa) (l2',sa') \<and> l1' = l1)"
    by simp
  then show ?case
  proof
    assume A: "C1 (l1,sa) (l1',sa') \<and> l2' = l2"
    then have st: "C1 (l1,sa) (l1',sa')" and eq: "l2' = l2" by simp_all
    have G: "G1 (l1,sa) (l1',sa')" by (rule rg_satD_guar[OF V1 P1 c1 st])
    from G1R2[OF J G] have R2s: "R2 l2 sa sa'" and J': "J (h1 l1' sa') (h2 l2 sa') sa'" by blast+
    have d1: "rg_reach C1 R1 h1 (fst (fst c0), snd c0) (h1 l1' sa') sa'" by (rule rg_reach.prog[OF c1 st])
    have d2: "rg_reach C2 R2 h2 (snd (fst c0), snd c0) (h2 l2 sa') sa'" by (rule rg_reach.env[OF c2 R2s])
    from d1 d2 J' show ?thesis using lp' eq by simp
  next
    assume A: "C2 (l2,sa) (l2',sa') \<and> l1' = l1"
    then have st: "C2 (l2,sa) (l2',sa')" and eq: "l1' = l1" by simp_all
    have G: "G2 (l2,sa) (l2',sa')" by (rule rg_satD_guar[OF V2 P2 c2 st])
    from G2R1[OF J G] have R1s: "R1 l1 sa sa'" and J': "J (h1 l1 sa') (h2 l2' sa') sa'" by blast+
    have d1: "rg_reach C1 R1 h1 (fst (fst c0), snd c0) (h1 l1 sa') sa'" by (rule rg_reach.env[OF c1 R1s])
    have d2: "rg_reach C2 R2 h2 (snd (fst c0), snd c0) (h2 l2' sa') sa'" by (rule rg_reach.prog[OF c2 st])
    from d1 d2 J' show ?thesis using lp' eq by simp
  qed
next
  case (env la sa sa')
  obtain l1 l2 where lp: "la = (l1,l2)" by (cases la)
  from env.IH lp have c1: "rg_reach C1 R1 h1 (fst (fst c0), snd c0) l1 sa"
    and c2: "rg_reach C2 R2 h2 (snd (fst c0), snd c0) l2 sa" and J: "J l1 l2 sa" by simp_all
  have Rs: "R (l1,l2) sa sa'" using env.hyps(2) lp by simp
  from RR[OF J Rs] have R1s: "R1 l1 sa sa'" and R2s: "R2 l2 sa sa'"
    and J': "J (h1 l1 sa') (h2 l2 sa') sa'" by blast+
  have d1: "rg_reach C1 R1 h1 (fst (fst c0), snd c0) (h1 l1 sa') sa'" by (rule rg_reach.env[OF c1 R1s])
  have d2: "rg_reach C2 R2 h2 (snd (fst c0), snd c0) (h2 l2 sa') sa'" by (rule rg_reach.env[OF c2 R2s])
  from d1 d2 J' show ?case using lp by simp
qed

text \<open>Beyond the thesis: the parallel rule of Section 2.2, generalised in the two
  ways Section 4.5.5 needs (see the header):
    {pA, rA} A {gA, qA}      {pB, rB} B {gB, qB}
    J \<and> gA \<Rrightarrow> rB \<and> J'    J \<and> gB \<Rrightarrow> rA \<and> J'    J \<and> r \<Rrightarrow> rA \<and> rB \<and> J'
    --------------------------------------------------------------
    {pA \<and> pB \<and> J, r} A \<parallel> B {gA \<or> gB, qA \<and> qB \<and> J}
  V1 and V2 are the two quadruples on the first line; G1R2, G2R1 and RR are
  the three side conditions on the second.  J' is J after the step, with
  history variables updated.  For the garbage collector, J is
  consistent(s, \<sigma>): rely-Collector mentions the Collector's private s, and
  Section 4.5.5 requires its implication only for sets s consistent with
  new-risk.\<close>

theorem rg_parallel:
  assumes V1: "rg_sat C1 h1 P1 R1 G1 Q1"
    and V2: "rg_sat C2 h2 P2 R2 G2 Q2"
    and G1R2: "\<And>l1 l2 s l1' s'. J l1 l2 s \<Longrightarrow> G1 (l1,s) (l1',s') \<Longrightarrow>
                 R2 l2 s s' \<and> J (h1 l1' s') (h2 l2 s') s'"
    and G2R1: "\<And>l1 l2 s l2' s'. J l1 l2 s \<Longrightarrow> G2 (l2,s) (l2',s') \<Longrightarrow>
                 R1 l1 s s' \<and> J (h1 l1 s') (h2 l2' s') s'"
    and RR: "\<And>l1 l2 s s'. J l1 l2 s \<Longrightarrow> R (l1,l2) s s' \<Longrightarrow>
                 R1 l1 s s' \<and> R2 l2 s s' \<and> J (h1 l1 s') (h2 l2 s') s'"
  shows "rg_sat (par C1 C2) (hpar h1 h2) (par_pre P1 P2 J) R (par_guar G1 G2) (par_post Q1 Q2 J)"
  unfolding rg_sat_def
proof (intro allI impI)
  fix c0 l s assume P: "par_pre P1 P2 J c0" and Rc: "rg_reach (par C1 C2) R (hpar h1 h2) c0 l s"
  have Pr: "rg_reach C1 R1 h1 (fst (fst c0), snd c0) (fst l) s \<and>
            rg_reach C2 R2 h2 (snd (fst c0), snd c0) (snd l) s \<and> J (fst l) (snd l) s"
    by (rule par_project[OF V1 V2 G1R2 G2R1 RR P Rc])
  then have c1: "rg_reach C1 R1 h1 (fst (fst c0), snd c0) (fst l) s"
    and c2: "rg_reach C2 R2 h2 (snd (fst c0), snd c0) (snd l) s" and J: "J (fst l) (snd l) s"
    by blast+
  have P1: "P1 (fst (fst c0), snd c0)" and P2: "P2 (snd (fst c0), snd c0)"
    using P unfolding par_pre_def by simp_all
  have Q1: "Q1 (fst (fst c0), snd c0) (fst l, s)" by (rule rg_satD_post[OF V1 P1 c1])
  have Q2: "Q2 (snd (fst c0), snd c0) (snd l, s)" by (rule rg_satD_post[OF V2 P2 c2])
  have Post: "par_post Q1 Q2 J c0 (l,s)" unfolding par_post_def using Q1 Q2 J by simp
  have Guar: "\<forall>l' s'. par C1 C2 (l,s) (l',s') \<longrightarrow> par_guar G1 G2 (l,s) (l',s')"
  proof (intro allI impI)
    fix l' s' assume St: "par C1 C2 (l,s) (l',s')"
    then have "(C1 (fst l, s) (fst l', s') \<and> snd l' = snd l) \<or>
               (C2 (snd l, s) (snd l', s') \<and> fst l' = fst l)"
      unfolding par_def by simp
    then show "par_guar G1 G2 (l,s) (l',s')"
    proof
      assume A: "C1 (fst l, s) (fst l', s') \<and> snd l' = snd l"
      then have "G1 (fst l, s) (fst l', s')" using rg_satD_guar[OF V1 P1 c1] by blast
      with A show ?thesis unfolding par_guar_def by simp
    next
      assume A: "C2 (snd l, s) (snd l', s') \<and> fst l' = fst l"
      then have "G2 (snd l, s) (snd l', s')" using rg_satD_guar[OF V2 P2 c2] by blast
      with A show ?thesis unfolding par_guar_def by simp
    qed
  qed
  from Post Guar show "par_post Q1 Q2 J c0 (l,s) \<and>
      (\<forall>l' s'. par C1 C2 (l,s) (l',s') \<longrightarrow> par_guar G1 G2 (l,s) (l',s'))" by (rule conjI)
qed

text \<open>Thesis: the rule of Section 2.2 (Hayes and Jones, 2018), as the special
  case of rg_parallel with J true and rely and guarantee conditions over the
  shared state only: r \<or> gA \<Rrightarrow> rB and r \<or> gB \<Rrightarrow> rA.  Its other two
  side conditions, gA \<or> gB \<Rrightarrow> g and the one for q, are applications of
  rg_conseq.\<close>

corollary rg_parallel_plain:
  assumes V1: "rg_sat C1 h1 P1 (\<lambda>l. R1) G1 Q1"
    and V2: "rg_sat C2 h2 P2 (\<lambda>l. R2) G2 Q2"
    and G1R2: "\<And>l1 s l1' s'. G1 (l1,s) (l1',s') \<Longrightarrow> R2 s s'"
    and G2R1: "\<And>l2 s l2' s'. G2 (l2,s) (l2',s') \<Longrightarrow> R1 s s'"
    and RR: "\<And>s s'. R s s' \<Longrightarrow> R1 s s' \<and> R2 s s'"
  shows "rg_sat (par C1 C2) (hpar h1 h2) (par_pre P1 P2 (\<lambda>l1 l2 s. True)) (\<lambda>l. R)
           (par_guar G1 G2) (par_post Q1 Q2 (\<lambda>l1 l2 s. True))"
proof (rule rg_parallel[OF V1 V2])
  fix l1 l2 s l1' s' assume "True" and "G1 (l1,s) (l1',s')"
  then show "R2 s s' \<and> True" using G1R2 by blast
next
  fix l1 l2 s l2' s' assume "True" and "G2 (l2,s) (l2',s')"
  then show "R1 s s' \<and> True" using G2R1 by blast
next
  fix l1 l2 s s' assume "True" and "R s s'"
  then show "R1 s s' \<and> R2 s s' \<and> True" using RR by blast
qed

end
