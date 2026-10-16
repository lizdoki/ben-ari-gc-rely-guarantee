(*  RG_VDM: VDM-style rely/guarantee reasoning about programs, and the
    inference rules used in Chapter 4 of the thesis, proved sound.

    A small language of programs (atomic statements, sequential composition,
    conditionals and while-loops) is given a semantics of computations with
    program steps and environment steps, as in RG_Semantics.  The quadruple
    {p, r} c {g, q} of Section 2.2 is vdm h p r c g q.  The rules are those of
    Appendix B.1 (sequential composition with post1 | post2, the while rule
    with test, inv and so-far), the rule of consequence, and the rules for
    atomic statements and conditionals that the thesis uses without stating.
    Nothing here is specific to the garbage collector.

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
      code of Appendix C (Algorithms 15-20)         com: Basic, Seq, Cond,
                                                      While, Skip
      {p, r} c {g, q} (Section 2.2)                 vdm h p r c g q
      p is unaffected by interference ("despite     stable, tolerates
        environment interference", Section 4.8)
      rule of consequence                           rule_conseq, rule_weaken
      sequential composition, post1 | post2         rule_seq, seq_post
        (Appendix B.1)
      the while rule (Section 4.8.1, Appendix B.1)  rule_while
      the while rule for a loop whose body runs     rule_repeat
        at least once (Mark, Algorithm 7)
      atomic statements, conditionals               rule_basic, rule_cond,
                                                      rule_if, rule_skip,
                                                      rule_seq_basic
      a property kept by every rely and guarantee   rule_trace, rule_trace_h,
        step holds throughout ((r or g)-star)         rule_inv
      a VDM quadruple is a quadruple of             vdm_rg_sat
        RG_Semantics, so the parallel rule applies

    Two points of the semantics, both standard in rely/guarantee (Hayes and
    Jones, 2018), are worth knowing when reading the rules:
      - The environment may also take steps after a program has finished, so
        a post condition must tolerate interference (tolerates): this is what
        makes the sequential rule exactly post1 | post2.  For a loop this is
        the "despite environment interference" that Section 4.8 shows for
        each so-far relation.
      - Rely and guarantee conditions are reflexive (Section 2.2): an
        environment step may leave the shared state unchanged, and a program
        step that changes nothing (such as evaluating a loop test) satisfies
        every guarantee.                                                     *)

theory RG_VDM
  imports RG_Semantics
begin


section \<open>Programs\<close>

text \<open>Thesis: the code of Appendix C.  A program acts on a configuration (l, s):
  the process's private variables l and the shared state s.  Basic r is an
  atomic statement: one program step from (l, s) to any (l', s') with
  r (l, s) (l', s'); the angle brackets of Mark-kids line 4 mark such a
  statement, and every assignment of the code is one.  Skip is the program
  that has finished.\<close>

datatype ('l,'s) com =
    Skip
  | Basic "('l,'s) rg_conf \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> bool"
  | Seq "('l,'s) com" "('l,'s) com"
  | Cond "('l,'s) rg_conf \<Rightarrow> bool" "('l,'s) com" "('l,'s) com"
  | While "('l,'s) rg_conf \<Rightarrow> bool" "('l,'s) com"

text \<open>Thesis: "if b then c" with no else branch, as in Algorithms 15, 17 and 19.\<close>

abbreviation IfThen :: "(('l,'s) rg_conf \<Rightarrow> bool) \<Rightarrow> ('l,'s) com \<Rightarrow> ('l,'s) com" where
  "IfThen b c \<equiv> Cond b c Skip"

text \<open>Thesis: the program steps of the code.  An atomic statement takes one step.
  Evaluating the test of a conditional or a loop, and moving on to the second
  half of a sequential composition, are steps that change nothing.\<close>

inductive cstep :: "('l,'s) com \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> ('l,'s) com \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> bool"
where
  Basic:  "r k k' \<Longrightarrow> cstep (Basic r) k Skip k'"
| Seq1:   "cstep c1 k c1' k' \<Longrightarrow> cstep (Seq c1 c2) k (Seq c1' c2) k'"
| Seq2:   "cstep (Seq Skip c2) k c2 k"
| CondT:  "b k \<Longrightarrow> cstep (Cond b c1 c2) k c1 k"
| CondF:  "\<not> b k \<Longrightarrow> cstep (Cond b c1 c2) k c2 k"
| WhileT: "b k \<Longrightarrow> cstep (While b c) k (Seq c (While b c)) k"
| WhileF: "\<not> b k \<Longrightarrow> cstep (While b c) k Skip k"

text \<open>Mechanisation only: case analysis on a program step.\<close>

inductive_cases cstep_SkipE: "cstep Skip k c' k'"
inductive_cases cstep_BasicE: "cstep (Basic r) k c' k'"
inductive_cases cstep_SeqE: "cstep (Seq c1 c2) k c' k'"
inductive_cases cstep_CondE: "cstep (Cond b c1 c2) k c' k'"
inductive_cases cstep_WhileE: "cstep (While b c) k c' k'"

section \<open>Computations\<close>

text \<open>Thesis: the history variables (possible values, Section 2.3) are updated
  after every step, whichever process takes it: hupd h k is the configuration
  k with its history variables updated.\<close>

definition hupd :: "('l,'s) rg_hist \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> ('l,'s) rg_conf" where
  "hupd h k = (h (fst k) (snd k), snd k)"

lemma hupd_pair [simp]: "hupd h (l,s) = (h l s, s)"
  by (simp add: hupd_def)

text \<open>Thesis: an environment step (Figure 2.2), seen from a process with history
  function h: the shared state changes as the rely condition R allows, or not
  at all (rely conditions are reflexive, Section 2.2); the process's private
  variables do not change, apart from its history variables.\<close>

definition renv :: "('l,'s) rg_hist \<Rightarrow> ('l,'s) rg_rely \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> bool" where
  "renv h R k k' \<longleftrightarrow> (R (fst k) (snd k) (snd k') \<or> snd k' = snd k) \<and> fst k' = h (fst k) (snd k')"

text \<open>Mechanisation only: renv on explicit pairs, and an environment step that
  changes nothing but the history variables.\<close>

lemma renv_iff [simp]: "renv h R (l,s) (l',s') \<longleftrightarrow> (R l s s' \<or> s' = s) \<and> l' = h l s'"
  by (simp add: renv_def)

lemma renv_stutter: "renv h R k (hupd h k)"
  by (simp add: renv_def hupd_def)

text \<open>Thesis: the computations of c (Aczel traces, Section 2.2, Figure 2.2).
  creach h R c k0 c' k holds when some computation of c from configuration k0
  reaches k with c' left to run (c' = Skip when c has finished).  Each step is
  a program step or an environment step; after every step the history
  variables are updated.\<close>

inductive creach :: "('l,'s) rg_hist \<Rightarrow> ('l,'s) rg_rely \<Rightarrow> ('l,'s) com \<Rightarrow> ('l,'s) rg_conf \<Rightarrow>
                     ('l,'s) com \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> bool"
  for h :: "('l,'s) rg_hist" and R :: "('l,'s) rg_rely" and c :: "('l,'s) com"
    and k0 :: "('l,'s) rg_conf"
where
  start: "creach h R c k0 c k0"
| prog:  "creach h R c k0 c1 k \<Longrightarrow> cstep c1 k c2 k' \<Longrightarrow> creach h R c k0 c2 (hupd h k')"
| env:   "creach h R c k0 c1 k \<Longrightarrow> renv h R k k' \<Longrightarrow> creach h R c k0 c1 k'"

section \<open>The quadruple {p, r} c {g, q}\<close>

text \<open>Thesis: the quadruple {p, r} c {g, q} of Section 2.2, for a process with
  history function h.  From every initial configuration satisfying p, in every
  computation whose environment steps satisfy r: every program step satisfies
  g (or changes nothing: guarantee conditions are reflexive), and whenever c
  has finished, q relates the initial configuration to the current one.\<close>

definition vdm :: "('l,'s) rg_hist \<Rightarrow> (('l,'s) rg_conf \<Rightarrow> bool) \<Rightarrow> ('l,'s) rg_rely \<Rightarrow> ('l,'s) com \<Rightarrow>
                   (('l,'s) rg_conf \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> bool) \<Rightarrow>
                   (('l,'s) rg_conf \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> bool) \<Rightarrow> bool" where
  "vdm h P R c G Q \<longleftrightarrow>
     (\<forall>k0 c1 k. P k0 \<longrightarrow> creach h R c k0 c1 k \<longrightarrow>
        (c1 = Skip \<longrightarrow> Q k0 k) \<and> (\<forall>c2 k'. cstep c1 k c2 k' \<longrightarrow> k' = k \<or> G k k'))"

text \<open>Mechanisation only: introducing and using a quadruple.\<close>

lemma vdmI:
  assumes "\<And>k0 k. P k0 \<Longrightarrow> creach h R c k0 Skip k \<Longrightarrow> Q k0 k"
    and "\<And>k0 c1 k c2 k'. P k0 \<Longrightarrow> creach h R c k0 c1 k \<Longrightarrow> cstep c1 k c2 k' \<Longrightarrow> k' = k \<or> G k k'"
  shows "vdm h P R c G Q"
  using assms unfolding vdm_def by blast

lemma vdmD_post: "vdm h P R c G Q \<Longrightarrow> P k0 \<Longrightarrow> creach h R c k0 Skip k \<Longrightarrow> Q k0 k"
  unfolding vdm_def by blast

lemma vdmD_guar:
  "vdm h P R c G Q \<Longrightarrow> P k0 \<Longrightarrow> creach h R c k0 c1 k \<Longrightarrow> cstep c1 k c2 k' \<Longrightarrow> k' = k \<or> G k k'"
  unfolding vdm_def by blast

section \<open>Stability under interference\<close>

text \<open>Thesis: a pre condition or invariant p "holds despite interference"
  (Section 4.8): it is preserved by every environment step.\<close>

definition stable :: "('l,'s) rg_hist \<Rightarrow> ('l,'s) rg_rely \<Rightarrow> (('l,'s) rg_conf \<Rightarrow> bool) \<Rightarrow> bool" where
  "stable h R P \<longleftrightarrow> (\<forall>k k'. P k \<longrightarrow> renv h R k k' \<longrightarrow> P k')"

text \<open>Thesis: a post condition or so-far relation q "is satisfied despite
  environment interference" (Section 4.8): environment steps after the end
  state do not falsify it, nor do environment steps before the start state
  when the start state satisfies I (the pre condition or loop invariant).
  Hayes and Jones (2018) call this "q tolerates r".\<close>

definition tolerates :: "('l,'s) rg_hist \<Rightarrow> ('l,'s) rg_rely \<Rightarrow> (('l,'s) rg_conf \<Rightarrow> bool) \<Rightarrow>
                         (('l,'s) rg_conf \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> bool) \<Rightarrow> bool" where
  "tolerates h R I Q \<longleftrightarrow>
     (\<forall>k0 k k'. Q k0 k \<longrightarrow> renv h R k k' \<longrightarrow> Q k0 k') \<and>
     (\<forall>k0 k0' k. I k0 \<longrightarrow> renv h R k0 k0' \<longrightarrow> Q k0' k \<longrightarrow> Q k0 k)"

text \<open>Mechanisation only: introduction and use of stable and tolerates.\<close>

lemma stableI:
  assumes "\<And>l s s'. P (l,s) \<Longrightarrow> R l s s' \<or> s' = s \<Longrightarrow> P (h l s', s')"
  shows "stable h R P"
  unfolding stable_def
proof (intro allI impI)
  fix k k' assume Pk: "P k" and E: "renv h R k k'"
  obtain l s where k: "k = (l,s)" by (cases k)
  obtain l' s' where k': "k' = (l',s')" by (cases k')
  from E k k' have R: "R l s s' \<or> s' = s" and l': "l' = h l s'" by simp_all
  from Pk k have "P (l,s)" by simp
  from assms[OF this R] k' l' show "P k'" by simp
qed

lemma stableD: "stable h R P \<Longrightarrow> P k \<Longrightarrow> renv h R k k' \<Longrightarrow> P k'"
  unfolding stable_def by blast

lemma stable_rtranclp:
  assumes PS: "stable h R P" and RS: "(renv h R)\<^sup>*\<^sup>* k k'" and P: "P k"
  shows "P k'"
  using RS P
proof (induction rule: rtranclp_induct)
  case base
  then show ?case .
next
  case (step y z)
  from step.IH[OF step.prems] have "P y" .
  from stableD[OF PS this step.hyps(2)] show ?case .
qed

lemma toleratesI:
  assumes "\<And>k0 l s s'. Q k0 (l,s) \<Longrightarrow> R l s s' \<or> s' = s \<Longrightarrow> Q k0 (h l s', s')"
    and "\<And>l0 s0 s0' k. I (l0,s0) \<Longrightarrow> R l0 s0 s0' \<or> s0' = s0 \<Longrightarrow> Q (h l0 s0', s0') k \<Longrightarrow> Q (l0,s0) k"
  shows "tolerates h R I Q"
  unfolding tolerates_def
proof (intro conjI allI impI)
  fix k0 k k' assume Q: "Q k0 k" and E: "renv h R k k'"
  obtain l s where k: "k = (l,s)" by (cases k)
  obtain l' s' where k': "k' = (l',s')" by (cases k')
  from E k k' have R: "R l s s' \<or> s' = s" and l': "l' = h l s'" by simp_all
  from Q k have "Q k0 (l,s)" by simp
  from assms(1)[OF this R] k' l' show "Q k0 k'" by simp
next
  fix k0 k0' k assume I: "I k0" and E: "renv h R k0 k0'" and Q: "Q k0' k"
  obtain l s where k0: "k0 = (l,s)" by (cases k0)
  obtain l' s' where k0': "k0' = (l',s')" by (cases k0')
  from E k0 k0' have R: "R l s s' \<or> s' = s" and l': "l' = h l s'" by simp_all
  from I k0 have I': "I (l,s)" by simp
  from Q k0' l' have Q': "Q (h l s', s') k" by simp
  from assms(2)[OF I' R Q'] k0 show "Q k0 k" by simp
qed

lemma tolerates_rightD: "tolerates h R I Q \<Longrightarrow> Q k0 k \<Longrightarrow> renv h R k k' \<Longrightarrow> Q k0 k'"
  unfolding tolerates_def by blast

lemma tolerates_leftD: "tolerates h R I Q \<Longrightarrow> I k0 \<Longrightarrow> renv h R k0 k0' \<Longrightarrow> Q k0' k \<Longrightarrow> Q k0 k"
  unfolding tolerates_def by blast

lemma tolerates_right:
  assumes T: "tolerates h R I Q" and RS: "(renv h R)\<^sup>*\<^sup>* k k'" and Q: "Q k0 k"
  shows "Q k0 k'"
  using RS Q
proof (induction rule: rtranclp_induct)
  case base
  then show ?case .
next
  case (step y z)
  from step.IH[OF step.prems] have "Q k0 y" .
  from tolerates_rightD[OF T this step.hyps(2)] show ?case .
qed

text \<open>Mechanisation only: interference before the start state, over any
  number of environment steps, when the start state satisfies a stable I.\<close>

lemma left_closure:
  assumes IS: "stable h R I"
    and L: "\<And>k0 k0' k. I k0 \<Longrightarrow> renv h R k0 k0' \<Longrightarrow> Q k0' k \<Longrightarrow> Q k0 k"
    and RS: "(renv h R)\<^sup>*\<^sup>* k0 k0'" and I: "I k0" and Q: "Q k0' k"
  shows "Q k0 k"
  using RS I Q
proof (induction rule: converse_rtranclp_induct)
  case base
  then show ?case by blast
next
  case (step y z)
  have "I z" by (rule stableD[OF IS step.prems(1) step.hyps(1)])
  then have "Q z k" by (rule step.IH[OF _ step.prems(2)])
  from L[OF step.prems(1) step.hyps(1) this] show ?case .
qed

lemma tolerates_left:
  assumes T: "tolerates h R I Q" and IS: "stable h R I"
    and RS: "(renv h R)\<^sup>*\<^sup>* k0 k0'" and I: "I k0" and Q: "Q k0' k"
  shows "Q k0 k"
  by (rule left_closure[where I = I and Q = Q, OF IS tolerates_leftD[OF T] RS I Q])

text \<open>Mechanisation only: a relation preserved by every environment step holds
  across any number of them.\<close>

lemma rtranclp_trace:
  assumes RS: "(renv h R)\<^sup>*\<^sup>* k0 k" and T0: "T k0 k0"
    and Te: "\<And>k k'. T k0 k \<Longrightarrow> renv h R k k' \<Longrightarrow> T k0 k'"
  shows "T k0 k"
  using RS
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (rule T0)
next
  case (step y z)
  from Te[OF step.IH step.hyps(2)] show ?case .
qed

section \<open>The rules\<close>

subsection \<open>Consequence\<close>

text \<open>Mechanisation only: a computation under a stronger rely condition is also
  one under a weaker one.\<close>

lemma creach_rely_mono:
  assumes Rc: "creach h R c k0 c1 k" and RR: "\<And>l s s'. R l s s' \<Longrightarrow> R' l s s'"
  shows "creach h R' c k0 c1 k"
  using Rc
proof (induction rule: creach.induct)
  case start
  show ?case by (rule creach.start)
next
  case (prog ca ka cb kb)
  show ?case by (rule creach.prog[OF prog.IH prog.hyps(2)])
next
  case (env ca ka kb)
  have "renv h R' ka kb" using env.hyps(2) RR unfolding renv_def by blast
  then show ?case by (rule creach.env[OF env.IH])
qed

text \<open>Thesis: the rule of consequence: strengthen the pre and rely conditions,
  weaken the guarantee and post condition.\<close>

theorem rule_conseq:
  assumes V: "vdm h P R c G Q"
    and PP: "\<And>k. P' k \<Longrightarrow> P k"
    and RR: "\<And>l s s'. R' l s s' \<Longrightarrow> R l s s'"
    and GG: "\<And>k k'. G k k' \<Longrightarrow> G' k k'"
    and QQ: "\<And>k0 k. P' k0 \<Longrightarrow> Q k0 k \<Longrightarrow> Q' k0 k"
  shows "vdm h P' R' c G' Q'"
proof (rule vdmI)
  fix k0 k assume P': "P' k0" and Rc: "creach h R' c k0 Skip k"
  have Rc2: "creach h R c k0 Skip k" by (rule creach_rely_mono[OF Rc RR])
  have "Q k0 k" by (rule vdmD_post[OF V PP[OF P'] Rc2])
  then show "Q' k0 k" by (rule QQ[OF P'])
next
  fix k0 c1 k c2 k' assume P': "P' k0" and Rc: "creach h R' c k0 c1 k" and S: "cstep c1 k c2 k'"
  have Rc2: "creach h R c k0 c1 k" by (rule creach_rely_mono[OF Rc RR])
  have "k' = k \<or> G k k'" by (rule vdmD_guar[OF V PP[OF P'] Rc2 S])
  then show "k' = k \<or> G' k k'" using GG by blast
qed

text \<open>Mechanisation only: the rule of consequence with the same rely condition.\<close>

corollary rule_weaken:
  assumes V: "vdm h P R c G Q"
    and PP: "\<And>k. P' k \<Longrightarrow> P k"
    and GG: "\<And>k k'. G k k' \<Longrightarrow> G' k k'"
    and QQ: "\<And>k0 k. P' k0 \<Longrightarrow> Q k0 k \<Longrightarrow> Q' k0 k"
  shows "vdm h P' R c G' Q'"
  by (rule rule_conseq[OF V PP _ GG QQ])

subsection \<open>Atomic statements and Skip\<close>

text \<open>Mechanisation only: the computations of Skip are environment steps only.\<close>

lemma creach_Skip:
  assumes "creach h R Skip k0 c1 k"
  shows "c1 = Skip \<and> (renv h R)\<^sup>*\<^sup>* k0 k"
  using assms
proof (induction rule: creach.induct)
  case start
  show ?case by simp
next
  case (prog ca ka cb kb)
  from prog.IH prog.hyps(2) show ?case by (auto elim: cstep_SkipE)
next
  case (env ca ka kb)
  from env.IH env.hyps(2) show ?case by (auto intro: rtranclp.rtrancl_into_rtrancl)
qed

text \<open>Beyond the thesis: the rule for a program that has nothing left to do, such
  as the missing else branch of "if b then c": its post condition need only
  follow from interference.\<close>

theorem rule_skip:
  assumes "\<And>k0 k. P k0 \<Longrightarrow> (renv h R)\<^sup>*\<^sup>* k0 k \<Longrightarrow> Q k0 k"
  shows "vdm h P R Skip G Q"
proof (rule vdmI)
  fix k0 k assume "P k0" and "creach h R Skip k0 Skip k"
  with assms creach_Skip show "Q k0 k" by blast
next
  fix k0 c1 k c2 k' assume "creach h R Skip k0 c1 k" and S: "cstep c1 k c2 k'"
  then have "c1 = Skip" using creach_Skip by blast
  with S show "k' = k \<or> G k k'" by (auto elim: cstep_SkipE)
qed

text \<open>Mechanisation only: the computations of an atomic statement: interference,
  then the statement's one step, then interference.\<close>

lemma creach_Basic:
  assumes "creach h R (Basic r) k0 c1 k"
  shows "(c1 = Basic r \<and> (renv h R)\<^sup>*\<^sup>* k0 k) \<or>
         (c1 = Skip \<and> (\<exists>k1 k2. (renv h R)\<^sup>*\<^sup>* k0 k1 \<and> r k1 k2 \<and> (renv h R)\<^sup>*\<^sup>* (hupd h k2) k))"
  using assms
proof (induction rule: creach.induct)
  case start
  show ?case by simp
next
  case (prog ca ka cb kb)
  from prog.IH show ?case
  proof (elim disjE conjE exE)
    assume ca: "ca = Basic r" and RS: "(renv h R)\<^sup>*\<^sup>* k0 ka"
    from prog.hyps(2) ca have cb: "cb = Skip" and rr: "r ka kb" by (auto elim: cstep_BasicE)
    have "(renv h R)\<^sup>*\<^sup>* (hupd h kb) (hupd h kb)" by simp
    with RS rr cb show ?thesis by blast
  next
    fix k1 k2 assume "ca = Skip"
    with prog.hyps(2) show ?thesis by (auto elim: cstep_SkipE)
  qed
next
  case (env ca ka kb)
  from env.IH env.hyps(2) show ?case by (blast intro: rtranclp.rtrancl_into_rtrancl)
qed

text \<open>Beyond the thesis: the rule for an atomic statement.  The pre condition
  must hold despite interference until the statement runs; the step itself
  must satisfy the guarantee; and the post condition, relating the start to
  the end, must cover interference before and after the step.\<close>

theorem rule_basic_gen:
  assumes PS: "stable h R P"
    and G: "\<And>k k'. P k \<Longrightarrow> r k k' \<Longrightarrow> G k k'"
    and Q: "\<And>k0 k1 k2 k. P k0 \<Longrightarrow> (renv h R)\<^sup>*\<^sup>* k0 k1 \<Longrightarrow> P k1 \<Longrightarrow> r k1 k2 \<Longrightarrow>
                         (renv h R)\<^sup>*\<^sup>* (hupd h k2) k \<Longrightarrow> Q k0 k"
  shows "vdm h P R (Basic r) G Q"
proof (rule vdmI)
  fix k0 k assume P: "P k0" and Rc: "creach h R (Basic r) k0 Skip k"
  from creach_Basic[OF Rc] obtain k1 k2 where R1: "(renv h R)\<^sup>*\<^sup>* k0 k1" and S: "r k1 k2"
    and R2: "(renv h R)\<^sup>*\<^sup>* (hupd h k2) k" by auto
  have P1: "P k1" by (rule stable_rtranclp[OF PS R1 P])
  show "Q k0 k" by (rule Q[OF P R1 P1 S R2])
next
  fix k0 c1 k c2 k' assume P: "P k0" and Rc: "creach h R (Basic r) k0 c1 k" and S: "cstep c1 k c2 k'"
  from creach_Basic[OF Rc] show "k' = k \<or> G k k'"
  proof (elim disjE conjE exE)
    assume c1: "c1 = Basic r" and R1: "(renv h R)\<^sup>*\<^sup>* k0 k"
    from S c1 have "r k k'" by (auto elim: cstep_BasicE)
    moreover have "P k" by (rule stable_rtranclp[OF PS R1 P])
    ultimately show ?thesis using G by blast
  next
    fix k1 k2 assume "c1 = Skip"
    with S show ?thesis by (auto elim: cstep_SkipE)
  qed
qed

text \<open>Beyond the thesis: the rule for an atomic statement, when the post
  condition tolerates interference: it then suffices that the step itself
  establishes it (in the configuration reached, after the history variables
  are updated).\<close>

theorem rule_basic:
  assumes PS: "stable h R P" and QT: "tolerates h R P Q"
    and S: "\<And>k k'. P k \<Longrightarrow> r k k' \<Longrightarrow> G k k' \<and> Q k (hupd h k')"
  shows "vdm h P R (Basic r) G Q"
proof (rule rule_basic_gen[OF PS])
  fix k k' assume "P k" and "r k k'"
  then show "G k k'" using S by blast
next
  fix k0 k1 k2 k
  assume P: "P k0" and R1: "(renv h R)\<^sup>*\<^sup>* k0 k1" and P1: "P k1" and St: "r k1 k2"
    and R2: "(renv h R)\<^sup>*\<^sup>* (hupd h k2) k"
  have "Q k1 (hupd h k2)" using S[OF P1 St] by blast
  then have "Q k1 k" by (rule tolerates_right[OF QT R2])
  then show "Q k0 k" by (rule tolerates_left[OF QT PS R1 P])
qed

subsection \<open>Sequential composition\<close>

text \<open>Thesis: post1 | post2 (Appendix B.1): there is an intermediate state in
  which post1 holds from the start and post2 holds to the end.\<close>

definition seq_post :: "(('l,'s) rg_conf \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> bool) \<Rightarrow>
                        (('l,'s) rg_conf \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> bool) \<Rightarrow>
                        ('l,'s) rg_conf \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> bool" where
  "seq_post Q1 Q2 k0 k \<longleftrightarrow> (\<exists>k1. Q1 k0 k1 \<and> Q2 k1 k)"

text \<open>Mechanisation only: the computations of c1; c2: a computation of c1 still
  running, or a finished computation of c1 followed by one of c2.\<close>

lemma creach_Seq:
  assumes "creach h R (Seq c1 c2) k0 c k"
  shows "(\<exists>c1'. c = Seq c1' c2 \<and> creach h R c1 k0 c1' k) \<or>
         (\<exists>k1. creach h R c1 k0 Skip k1 \<and> creach h R c2 k1 c k)"
  using assms
proof (induction rule: creach.induct)
  case start
  have "creach h R c1 k0 c1 k0" by (rule creach.start)
  then show ?case by blast
next
  case (prog ca ka cb kb)
  from prog.IH show ?case
  proof (elim disjE exE conjE)
    fix c1' assume ca: "ca = Seq c1' c2" and R1: "creach h R c1 k0 c1' ka"
    from prog.hyps(2) ca
    have "(\<exists>c1''. cb = Seq c1'' c2 \<and> cstep c1' ka c1'' kb) \<or> (c1' = Skip \<and> cb = c2 \<and> kb = ka)"
      by (auto elim: cstep_SeqE)
    then show ?thesis
    proof (elim disjE exE conjE)
      fix c1'' assume cb: "cb = Seq c1'' c2" and S1: "cstep c1' ka c1'' kb"
      have "creach h R c1 k0 c1'' (hupd h kb)" by (rule creach.prog[OF R1 S1])
      with cb show ?thesis by blast
    next
      assume c1': "c1' = Skip" and cb: "cb = c2" and kb: "kb = ka"
      from R1 c1' have R1': "creach h R c1 k0 Skip ka" by simp
      have "creach h R c1 k0 Skip (hupd h ka)" by (rule creach.env[OF R1' renv_stutter])
      moreover have "creach h R c2 (hupd h ka) c2 (hupd h ka)" by (rule creach.start)
      ultimately show ?thesis using cb kb by blast
    qed
  next
    fix k1 assume R1: "creach h R c1 k0 Skip k1" and R2: "creach h R c2 k1 ca ka"
    have "creach h R c2 k1 cb (hupd h kb)" by (rule creach.prog[OF R2 prog.hyps(2)])
    with R1 show ?thesis by blast
  qed
next
  case (env ca ka kb)
  from env.IH show ?case
  proof (elim disjE exE conjE)
    fix c1' assume "ca = Seq c1' c2" and "creach h R c1 k0 c1' ka"
    then show ?thesis using creach.env[OF _ env.hyps(2)] by blast
  next
    fix k1 assume "creach h R c1 k0 Skip k1" and "creach h R c2 k1 ca ka"
    then show ?thesis using creach.env[OF _ env.hyps(2)] by blast
  qed
qed

text \<open>Thesis: the rule for sequential composition (Appendix B.1):
    {p1, r} c1 {g, q1}    q1 establishes p2    {p2, r} c2 {g, q2}
    --------------------------------------------------------------
                {p1, r} c1; c2 {g, q1 | q2}\<close>

theorem rule_seq:
  assumes V1: "vdm h P1 R c1 G Q1" and V2: "vdm h P2 R c2 G Q2"
    and Mid: "\<And>k0 k. P1 k0 \<Longrightarrow> Q1 k0 k \<Longrightarrow> P2 k"
  shows "vdm h P1 R (Seq c1 c2) G (seq_post Q1 Q2)"
proof (rule vdmI)
  fix k0 k assume P: "P1 k0" and Rc: "creach h R (Seq c1 c2) k0 Skip k"
  from creach_Seq[OF Rc] obtain k1 where R1: "creach h R c1 k0 Skip k1"
    and R2: "creach h R c2 k1 Skip k" by auto
  have Q1: "Q1 k0 k1" by (rule vdmD_post[OF V1 P R1])
  have Q2: "Q2 k1 k" by (rule vdmD_post[OF V2 Mid[OF P Q1] R2])
  from Q1 Q2 show "seq_post Q1 Q2 k0 k" unfolding seq_post_def by blast
next
  fix k0 ca ka cb kb assume P: "P1 k0" and Rc: "creach h R (Seq c1 c2) k0 ca ka"
    and S: "cstep ca ka cb kb"
  from creach_Seq[OF Rc] show "kb = ka \<or> G ka kb"
  proof (elim disjE exE conjE)
    fix c1' assume ca: "ca = Seq c1' c2" and R1: "creach h R c1 k0 c1' ka"
    from S ca have "(\<exists>c1''. cb = Seq c1'' c2 \<and> cstep c1' ka c1'' kb) \<or> (c1' = Skip \<and> cb = c2 \<and> kb = ka)"
      by (auto elim: cstep_SeqE)
    then show ?thesis
    proof (elim disjE exE conjE)
      fix c1'' assume "cb = Seq c1'' c2" and S1: "cstep c1' ka c1'' kb"
      show ?thesis by (rule vdmD_guar[OF V1 P R1 S1])
    next
      assume "kb = ka"
      then show ?thesis by simp
    qed
  next
    fix k1 assume R1: "creach h R c1 k0 Skip k1" and R2: "creach h R c2 k1 ca ka"
    have P2: "P2 k1" by (rule Mid[OF P vdmD_post[OF V1 P R1]])
    show ?thesis by (rule vdmD_guar[OF V2 P2 R2 S])
  qed
qed

subsection \<open>Conditionals\<close>

text \<open>Mechanisation only: the computations of a conditional: interference, then
  the test, then a computation of the chosen branch.\<close>

lemma creach_Cond:
  assumes "creach h R (Cond b c1 c2) k0 c k"
  shows "(c = Cond b c1 c2 \<and> (renv h R)\<^sup>*\<^sup>* k0 k) \<or>
         (\<exists>k1. (renv h R)\<^sup>*\<^sup>* k0 k1 \<and> b k1 \<and> creach h R c1 (hupd h k1) c k) \<or>
         (\<exists>k1. (renv h R)\<^sup>*\<^sup>* k0 k1 \<and> \<not> b k1 \<and> creach h R c2 (hupd h k1) c k)"
  using assms
proof (induction rule: creach.induct)
  case start
  show ?case by simp
next
  case (prog ca ka cb kb)
  from prog.IH show ?case
  proof (elim disjE exE conjE)
    assume ca: "ca = Cond b c1 c2" and RS: "(renv h R)\<^sup>*\<^sup>* k0 ka"
    from prog.hyps(2) ca
    have "(b ka \<and> cb = c1 \<and> kb = ka) \<or> (\<not> b ka \<and> cb = c2 \<and> kb = ka)"
      by (auto elim: cstep_CondE)
    then show ?thesis
    proof (elim disjE conjE)
      assume b: "b ka" and cb: "cb = c1" and kb: "kb = ka"
      have "creach h R c1 (hupd h ka) c1 (hupd h ka)" by (rule creach.start)
      with RS b cb kb show ?thesis by blast
    next
      assume b: "\<not> b ka" and cb: "cb = c2" and kb: "kb = ka"
      have "creach h R c2 (hupd h ka) c2 (hupd h ka)" by (rule creach.start)
      with RS b cb kb show ?thesis by blast
    qed
  next
    fix k1 assume "(renv h R)\<^sup>*\<^sup>* k0 k1" and "b k1" and "creach h R c1 (hupd h k1) ca ka"
    then show ?thesis using creach.prog[OF _ prog.hyps(2)] by blast
  next
    fix k1 assume "(renv h R)\<^sup>*\<^sup>* k0 k1" and "\<not> b k1" and "creach h R c2 (hupd h k1) ca ka"
    then show ?thesis using creach.prog[OF _ prog.hyps(2)] by blast
  qed
next
  case (env ca ka kb)
  from env.IH show ?case
  proof (elim disjE exE conjE)
    assume "ca = Cond b c1 c2" and "(renv h R)\<^sup>*\<^sup>* k0 ka"
    then show ?thesis using env.hyps(2) by (blast intro: rtranclp.rtrancl_into_rtrancl)
  next
    fix k1 assume "(renv h R)\<^sup>*\<^sup>* k0 k1" and "b k1" and "creach h R c1 (hupd h k1) ca ka"
    then show ?thesis using creach.env[OF _ env.hyps(2)] by blast
  next
    fix k1 assume "(renv h R)\<^sup>*\<^sup>* k0 k1" and "\<not> b k1" and "creach h R c2 (hupd h k1) ca ka"
    then show ?thesis using creach.env[OF _ env.hyps(2)] by blast
  qed
qed

text \<open>Beyond the thesis: the rule for a conditional.  The test may read shared
  variables, so it is evaluated after interference: the pre condition must
  hold despite interference, and the post condition must tolerate
  interference before the test.  The test must not read history variables.\<close>

theorem rule_cond:
  assumes V1: "vdm h (\<lambda>k. P k \<and> b k) R c1 G Q" and V2: "vdm h (\<lambda>k. P k \<and> \<not> b k) R c2 G Q"
    and PS: "stable h R P" and BH: "\<And>k. b (hupd h k) = b k"
    and QL: "\<And>k0 k0' k. P k0 \<Longrightarrow> renv h R k0 k0' \<Longrightarrow> Q k0' k \<Longrightarrow> Q k0 k"
  shows "vdm h P R (Cond b c1 c2) G Q"
proof -
  have pre: "P (hupd h k1) \<and> b (hupd h k1) = b k1"
    if "P k0" and "(renv h R)\<^sup>*\<^sup>* k0 k1" for k0 k1
  proof
    have "P k1" by (rule stable_rtranclp[OF PS that(2) that(1)])
    then show "P (hupd h k1)" by (rule stableD[OF PS _ renv_stutter])
    show "b (hupd h k1) = b k1" by (rule BH)
  qed
  have left: "Q k0 k" if "P k0" and "(renv h R)\<^sup>*\<^sup>* k0 k1" and "Q (hupd h k1) k" for k0 k1 k
  proof -
    have "(renv h R)\<^sup>*\<^sup>* k0 (hupd h k1)"
      using that(2) renv_stutter[of h R k1] by (rule rtranclp.rtrancl_into_rtrancl)
    from left_closure[where I = P and Q = Q, OF PS QL this that(1) that(3)] show ?thesis .
  qed
  show ?thesis
  proof (rule vdmI)
    fix k0 k assume P: "P k0" and Rc: "creach h R (Cond b c1 c2) k0 Skip k"
    from creach_Cond[OF Rc] show "Q k0 k"
    proof (elim disjE exE conjE)
      assume "Skip = Cond b c1 c2"
      then show ?thesis by simp
    next
      fix k1 assume R1: "(renv h R)\<^sup>*\<^sup>* k0 k1" and b1: "b k1"
        and Rc1: "creach h R c1 (hupd h k1) Skip k"
      from pre[OF P R1] b1 have "P (hupd h k1) \<and> b (hupd h k1)" by simp
      from vdmD_post[OF V1 this Rc1] show ?thesis by (rule left[OF P R1])
    next
      fix k1 assume R1: "(renv h R)\<^sup>*\<^sup>* k0 k1" and b1: "\<not> b k1"
        and Rc2: "creach h R c2 (hupd h k1) Skip k"
      from pre[OF P R1] b1 have "P (hupd h k1) \<and> \<not> b (hupd h k1)" by simp
      from vdmD_post[OF V2 this Rc2] show ?thesis by (rule left[OF P R1])
    qed
  next
    fix k0 ca ka cb kb assume P: "P k0" and Rc: "creach h R (Cond b c1 c2) k0 ca ka"
      and S: "cstep ca ka cb kb"
    from creach_Cond[OF Rc] show "kb = ka \<or> G ka kb"
    proof (elim disjE exE conjE)
      assume "ca = Cond b c1 c2"
      with S show ?thesis by (auto elim: cstep_CondE)
    next
      fix k1 assume R1: "(renv h R)\<^sup>*\<^sup>* k0 k1" and b1: "b k1"
        and Rc1: "creach h R c1 (hupd h k1) ca ka"
      from pre[OF P R1] b1 have "P (hupd h k1) \<and> b (hupd h k1)" by simp
      from vdmD_guar[OF V1 this Rc1 S] show ?thesis .
    next
      fix k1 assume R1: "(renv h R)\<^sup>*\<^sup>* k0 k1" and b1: "\<not> b k1"
        and Rc2: "creach h R c2 (hupd h k1) ca ka"
      from pre[OF P R1] b1 have "P (hupd h k1) \<and> \<not> b (hupd h k1)" by simp
      from vdmD_guar[OF V2 this Rc2 S] show ?thesis .
    qed
  qed
qed

text \<open>Beyond the thesis: "if b then c" (Algorithms 15, 17 and 19).  When the
  test fails nothing is done, so the post condition must follow from the pre
  condition, the failed test and interference.\<close>

theorem rule_if:
  assumes V: "vdm h (\<lambda>k. P k \<and> b k) R c G Q"
    and E: "\<And>k0 k. P k0 \<and> \<not> b k0 \<Longrightarrow> (renv h R)\<^sup>*\<^sup>* k0 k \<Longrightarrow> Q k0 k"
    and PS: "stable h R P" and BH: "\<And>k. b (hupd h k) = b k"
    and QL: "\<And>k0 k0' k. P k0 \<Longrightarrow> renv h R k0 k0' \<Longrightarrow> Q k0' k \<Longrightarrow> Q k0 k"
  shows "vdm h P R (IfThen b c) G Q"
proof (rule rule_cond[where b = b, OF V _ PS BH QL])
  show "vdm h (\<lambda>k. P k \<and> \<not> b k) R Skip G Q" by (rule rule_skip) (rule E)
qed

subsection \<open>While-loops\<close>

text \<open>Thesis: the while rule (Section 4.8.1, Appendix B.1).  For a loop
  "while test do body" with invariant inv (I here) and progress relation
  so-far:
    - the body, started where inv and test hold, re-establishes inv and makes
      progress so-far;
    - inv holds despite interference, and so-far is transitive and is
      satisfied despite interference;
  then the post condition of the loop is inv \<and> \<not>test \<and> (so-far \<or> iden): the
  body ran at least once, or not at all.  Under interference "not at all"
  still allows environment steps, so iden becomes (renv h R)**, the
  reflexive transitive closure of the rely condition.  The rule is stated
  for any post condition q that follows from this when the loop exits and
  then tolerates interference; P0 is what is known when the loop starts (such
  as consid = {}).  The test must not read history variables.  The rule
  here is for partial correctness, so it does not need so-far to be
  well-founded; that it is, so that each loop terminates, is the second half
  of Lemmas 5, 6, 10, 13 and 14 (GC_Mark, GC_Unmark and GC_Sweep).\<close>

theorem rule_while:
  assumes P0I: "\<And>k. P0 k \<Longrightarrow> I k"
    and body: "vdm h (\<lambda>k. I k \<and> b k) R c G (\<lambda>k0 k. I k \<and> sofar k0 k)"
    and IS: "stable h R I"
    and BH: "\<And>k. b (hupd h k) = b k"
    and trans: "\<And>k0 k1 k2. sofar k0 k1 \<Longrightarrow> sofar k1 k2 \<Longrightarrow> sofar k0 k2"
    and ST: "tolerates h R I sofar"
    and exit: "\<And>k0 k. P0 k0 \<Longrightarrow> I k \<Longrightarrow> \<not> b k \<Longrightarrow> sofar k0 k \<or> (renv h R)\<^sup>*\<^sup>* k0 k \<Longrightarrow> Q k0 k"
    and QR: "\<And>k0 k k'. Q k0 k \<Longrightarrow> I k \<Longrightarrow> renv h R k k' \<Longrightarrow> Q k0 k'"
  shows "vdm h P0 R (While b c) G Q"
proof -
  define W where "W k0 k \<longleftrightarrow> sofar k0 k \<or> (renv h R)\<^sup>*\<^sup>* k0 k" for k0 k
  have W_right: "W k0 k'" if "W k0 k" and "renv h R k k'" for k0 k k'
    using that tolerates_rightD[OF ST] unfolding W_def by (blast intro: rtranclp.rtrancl_into_rtrancl)
  have W_sofar: "sofar k0 k2" if "I k0" and "W k0 k1" and "sofar k1 k2" for k0 k1 k2
    using that trans tolerates_left[OF ST IS] unfolding W_def by blast
  have pre: "I (hupd h k1) \<and> b (hupd h k1)" if "I k1" and "b k1" for k1
  proof
    show "I (hupd h k1)" by (rule stableD[OF IS that(1) renv_stutter])
    show "b (hupd h k1)" using that(2) BH[of k1] by simp
  qed
  define Inv where "Inv k0 cfg k \<longleftrightarrow>
     (cfg = While b c \<and> I k \<and> W k0 k) \<or>
     (\<exists>c' k1. cfg = Seq c' (While b c) \<and> I k1 \<and> b k1 \<and> W k0 k1 \<and> creach h R c (hupd h k1) c' k) \<or>
     (cfg = Skip \<and> I k \<and> Q k0 k)" for k0 cfg k
  have main: "Inv k0 cfg k" if P0: "P0 k0" and Rc: "creach h R (While b c) k0 cfg k" for k0 cfg k
    using Rc
  proof (induction rule: creach.induct)
    case start
    show ?case unfolding Inv_def W_def using P0I[OF P0] by simp
  next
    case (prog ca ka cb kb)
    have I0: "I k0" by (rule P0I[OF P0])
    from prog.IH[unfolded Inv_def] show ?case
    proof (elim disjE exE conjE)
      assume ca: "ca = While b c" and I: "I ka" and W: "W k0 ka"
      from prog.hyps(2) ca
      have "(b ka \<and> cb = Seq c (While b c) \<and> kb = ka) \<or> (\<not> b ka \<and> cb = Skip \<and> kb = ka)"
        by (auto elim: cstep_WhileE)
      then show ?thesis
      proof (elim disjE conjE)
        assume bk: "b ka" and cb: "cb = Seq c (While b c)" and kb: "kb = ka"
        have "creach h R c (hupd h ka) c (hupd h ka)" by (rule creach.start)
        then show ?thesis unfolding Inv_def using cb kb I bk W by blast
      next
        assume bk: "\<not> b ka" and cb: "cb = Skip" and kb: "kb = ka"
        have "Q k0 ka" using exit[OF P0 I bk] W unfolding W_def by blast
        then have "Q k0 (hupd h ka)" by (rule QR[OF _ I renv_stutter])
        moreover have "I (hupd h ka)" by (rule stableD[OF IS I renv_stutter])
        ultimately show ?thesis unfolding Inv_def using cb kb by blast
      qed
    next
      fix c' k1 assume ca: "ca = Seq c' (While b c)" and I1: "I k1" and b1: "b k1"
        and W1: "W k0 k1" and RB: "creach h R c (hupd h k1) c' ka"
      from prog.hyps(2) ca
      have "(\<exists>c''. cb = Seq c'' (While b c) \<and> cstep c' ka c'' kb) \<or>
            (c' = Skip \<and> cb = While b c \<and> kb = ka)"
        by (auto elim: cstep_SeqE)
      then show ?thesis
      proof (elim disjE exE conjE)
        fix c'' assume cb: "cb = Seq c'' (While b c)" and S: "cstep c' ka c'' kb"
        have "creach h R c (hupd h k1) c'' (hupd h kb)" by (rule creach.prog[OF RB S])
        then show ?thesis unfolding Inv_def using cb I1 b1 W1 by blast
      next
        assume c': "c' = Skip" and cb: "cb = While b c" and kb: "kb = ka"
        from RB c' have RB': "creach h R c (hupd h k1) Skip ka" by simp
        have Post: "I ka \<and> sofar (hupd h k1) ka" by (rule vdmD_post[OF body pre[OF I1 b1] RB'])
        have W1': "W k0 (hupd h k1)" by (rule W_right[OF W1 renv_stutter])
        have SF: "sofar k0 ka" by (rule W_sofar[OF I0 W1' conjunct2[OF Post]])
        have SF': "sofar k0 (hupd h ka)" by (rule tolerates_rightD[OF ST SF renv_stutter])
        have I': "I (hupd h ka)" by (rule stableD[OF IS conjunct1[OF Post] renv_stutter])
        have "W k0 (hupd h ka)" using SF' unfolding W_def by blast
        then show ?thesis unfolding Inv_def using cb kb I' by blast
      qed
    next
      assume ca: "ca = Skip"
      with prog.hyps(2) show ?thesis by (auto elim: cstep_SkipE)
    qed
  next
    case (env ca ka kb)
    from env.IH[unfolded Inv_def] show ?case
    proof (elim disjE exE conjE)
      assume ca: "ca = While b c" and I: "I ka" and W: "W k0 ka"
      have "I kb" by (rule stableD[OF IS I env.hyps(2)])
      moreover have "W k0 kb" by (rule W_right[OF W env.hyps(2)])
      ultimately show ?thesis unfolding Inv_def using ca by blast
    next
      fix c' k1 assume ca: "ca = Seq c' (While b c)" and I1: "I k1" and b1: "b k1"
        and W1: "W k0 k1" and RB: "creach h R c (hupd h k1) c' ka"
      have "creach h R c (hupd h k1) c' kb" by (rule creach.env[OF RB env.hyps(2)])
      then show ?thesis unfolding Inv_def using ca I1 b1 W1 by blast
    next
      assume ca: "ca = Skip" and I: "I ka" and Q: "Q k0 ka"
      have "Q k0 kb" by (rule QR[OF Q I env.hyps(2)])
      moreover have "I kb" by (rule stableD[OF IS I env.hyps(2)])
      ultimately show ?thesis unfolding Inv_def using ca by blast
    qed
  qed
  show ?thesis
  proof (rule vdmI)
    fix k0 k assume P0: "P0 k0" and Rc: "creach h R (While b c) k0 Skip k"
    from main[OF P0 Rc] show "Q k0 k" unfolding Inv_def by auto
  next
    fix k0 ca ka cb kb assume P0: "P0 k0" and Rc: "creach h R (While b c) k0 ca ka"
      and S: "cstep ca ka cb kb"
    from main[OF P0 Rc, unfolded Inv_def] show "kb = ka \<or> G ka kb"
    proof (elim disjE exE conjE)
      assume "ca = While b c"
      with S show ?thesis by (auto elim: cstep_WhileE)
    next
      fix c' k1 assume ca: "ca = Seq c' (While b c)" and I1: "I k1" and b1: "b k1"
        and W1: "W k0 k1" and RB: "creach h R c (hupd h k1) c' ka"
      from S ca have "(\<exists>c''. cb = Seq c'' (While b c) \<and> cstep c' ka c'' kb) \<or>
                      (c' = Skip \<and> cb = While b c \<and> kb = ka)"
        by (auto elim: cstep_SeqE)
      then show ?thesis
      proof (elim disjE exE conjE)
        fix c'' assume "cb = Seq c'' (While b c)" and S1: "cstep c' ka c'' kb"
        show ?thesis by (rule vdmD_guar[OF body pre[OF I1 b1] RB S1])
      next
        assume "kb = ka"
        then show ?thesis by simp
      qed
    next
      assume "ca = Skip"
      with S show ?thesis by (auto elim: cstep_SkipE)
    qed
  qed
qed

text \<open>Thesis: the while rule for a loop whose body runs at least once, as in
  Mark (Algorithm 7: body; while test do body).  Since the body has run, the
  post condition of the loop is inv \<and> \<not>test \<and> so-far, with so-far measured
  from before the first run of the body (Section 4.8.1, "Mark Loop").\<close>

theorem rule_repeat:
  assumes body1: "vdm h P R c G (\<lambda>k0 k. I k \<and> sofar k0 k)"
    and again: "\<And>k. I k \<Longrightarrow> b k \<Longrightarrow> P k"
    and IS: "stable h R I"
    and BH: "\<And>k. b (hupd h k) = b k"
    and trans: "\<And>k0 k1 k2. sofar k0 k1 \<Longrightarrow> sofar k1 k2 \<Longrightarrow> sofar k0 k2"
    and ST: "tolerates h R I sofar"
    and exit: "\<And>k0 k. P k0 \<Longrightarrow> I k \<Longrightarrow> \<not> b k \<Longrightarrow> sofar k0 k \<Longrightarrow> Q k0 k"
    and QR: "\<And>k0 k k'. Q k0 k \<Longrightarrow> I k \<Longrightarrow> renv h R k k' \<Longrightarrow> Q k0 k'"
  shows "vdm h P R (Seq c (While b c)) G Q"
proof -
  define Q2 where "Q2 k1 k \<longleftrightarrow> (\<forall>k0. P k0 \<longrightarrow> sofar k0 k1 \<longrightarrow> Q k0 k)" for k1 k
  have body: "vdm h (\<lambda>k. I k \<and> b k) R c G (\<lambda>k0 k. I k \<and> sofar k0 k)"
    by (rule rule_conseq[OF body1]) (use again in auto)
  have loop: "vdm h I R (While b c) G Q2"
  proof (rule rule_while[where b = b, OF _ body IS BH trans ST])
    fix k assume "I k"
    then show "I k" .
  next
    fix k1 k assume I: "I k" and nb: "\<not> b k" and W: "sofar k1 k \<or> (renv h R)\<^sup>*\<^sup>* k1 k"
    show "Q2 k1 k" unfolding Q2_def
    proof (intro allI impI)
      fix k0 assume P: "P k0" and S0: "sofar k0 k1"
      have "sofar k0 k" using W
      proof
        assume "sofar k1 k" then show ?thesis by (rule trans[OF S0])
      next
        assume "(renv h R)\<^sup>*\<^sup>* k1 k" then show ?thesis by (rule tolerates_right[OF ST _ S0])
      qed
      then show "Q k0 k" by (rule exit[OF P I nb])
    qed
  next
    fix k1 k k' assume "Q2 k1 k" and "I k" and "renv h R k k'"
    then show "Q2 k1 k'" unfolding Q2_def using QR by blast
  qed
  have "vdm h P R (Seq c (While b c)) G (seq_post (\<lambda>k0 k. I k \<and> sofar k0 k) Q2)"
    by (rule rule_seq[OF body1 loop]) blast
  then show ?thesis
    by (rule rule_conseq) (auto simp: seq_post_def Q2_def)
qed

subsection \<open>A final atomic statement\<close>

text \<open>Beyond the thesis: c followed by an atomic statement that keeps what c
  established, as for the last line of Mark (s \<leftarrow> {}, Algorithm 7) and the
  last lines of Add-to-free (Algorithm 20).  It is the rule for sequential
  composition with the post condition of c carried across the statement.\<close>

theorem rule_seq_basic:
  assumes V: "vdm h P R c G Q"
    and QR: "\<And>k0 k k'. P k0 \<Longrightarrow> Q k0 k \<Longrightarrow> renv h R k k' \<Longrightarrow> Q k0 k'"
    and S: "\<And>k0 k k'. P k0 \<Longrightarrow> Q k0 k \<Longrightarrow> r k k' \<Longrightarrow> G k k' \<and> Q' k0 (hupd h k')"
    and Q'R: "\<And>k0 k k'. P k0 \<Longrightarrow> Q' k0 k \<Longrightarrow> renv h R k k' \<Longrightarrow> Q' k0 k'"
  shows "vdm h P R (Seq c (Basic r)) G Q'"
proof -
  define P2 where "P2 k \<longleftrightarrow> (\<exists>k0. P k0 \<and> Q k0 k)" for k
  define Q2 where "Q2 k1 k \<longleftrightarrow> (\<forall>k0. P k0 \<longrightarrow> Q k0 k1 \<longrightarrow> Q' k0 k)" for k1 k
  have P2S: "stable h R P2" unfolding stable_def P2_def using QR by blast
  have last: "vdm h P2 R (Basic r) G Q2"
  proof (rule rule_basic_gen[OF P2S])
    fix k k' assume "P2 k" and "r k k'"
    then show "G k k'" unfolding P2_def using S by blast
  next
    fix k1 k1' k2 k
    assume R1: "(renv h R)\<^sup>*\<^sup>* k1 k1'" and St: "r k1' k2" and R2: "(renv h R)\<^sup>*\<^sup>* (hupd h k2) k"
    show "Q2 k1 k" unfolding Q2_def
    proof (intro allI impI)
      fix k0 assume P: "P k0" and Q: "Q k0 k1"
      have "Q k0 k1'" using R1 Q
      proof (induction rule: rtranclp_induct)
        case base then show ?case .
      next
        case (step y z)
        from QR[OF P step.IH[OF step.prems] step.hyps(2)] show ?case .
      qed
      then have "Q' k0 (hupd h k2)" using S[OF P _ St] by blast
      with R2 show "Q' k0 k"
      proof (induction rule: rtranclp_induct)
        case base then show ?case .
      next
        case (step y z)
        from Q'R[OF P step.IH[OF step.prems] step.hyps(2)] show ?case .
      qed
    qed
  qed
  have "vdm h P R (Seq c (Basic r)) G (seq_post Q Q2)"
    by (rule rule_seq[OF V last]) (auto simp: P2_def)
  then show ?thesis
    by (rule rule_conseq) (auto simp: seq_post_def Q2_def)
qed

subsection \<open>Properties that hold throughout\<close>

text \<open>Beyond the thesis: a relation T between the start and the current state
  that every environment step and every program step preserve holds between
  the start and the end.  This is the (r \<or> g)* of the parallel rule (Section
  2.2): the thesis uses it whenever it argues that something "does not change
  during this phase", for example that marked never decreases during Mark.\<close>

theorem rule_trace:
  assumes V: "vdm h P R c G Q"
    and Tr: "\<And>k. P k \<Longrightarrow> T k k"
    and Te: "\<And>k0 k k'. P k0 \<Longrightarrow> T k0 k \<Longrightarrow> renv h R k k' \<Longrightarrow> T k0 k'"
    and Tg: "\<And>k0 k k'. P k0 \<Longrightarrow> T k0 k \<Longrightarrow> G k k' \<Longrightarrow> T k0 k'"
  shows "vdm h P R c G (\<lambda>k0 k. Q k0 k \<and> T k0 k)"
proof -
  have main: "T k0 k" if P: "P k0" and Rc: "creach h R c k0 c1 k" for k0 c1 k
    using Rc
  proof (induction rule: creach.induct)
    case start
    show ?case by (rule Tr[OF P])
  next
    case (prog ca ka cb kb)
    have "kb = ka \<or> G ka kb" by (rule vdmD_guar[OF V P prog.hyps(1) prog.hyps(2)])
    then have "T k0 kb"
    proof
      assume "kb = ka"
      then show ?thesis using prog.IH by simp
    next
      assume "G ka kb"
      then show ?thesis by (rule Tg[OF P prog.IH])
    qed
    then show ?case by (rule Te[OF P _ renv_stutter])
  next
    case (env ca ka kb)
    from Te[OF P env.IH env.hyps(2)] show ?case .
  qed
  show ?thesis
  proof (rule vdmI)
    fix k0 k assume "P k0" and "creach h R c k0 Skip k"
    then show "Q k0 k \<and> T k0 k" using vdmD_post[OF V] main by blast
  next
    fix k0 c1 k c2 k' assume "P k0" and "creach h R c k0 c1 k" and "cstep c1 k c2 k'"
    then show "k' = k \<or> G k k'" by (rule vdmD_guar[OF V])
  qed
qed

text \<open>Mechanisation only: the same, for a relation that program steps preserve
  only once the history variables have been updated after the step (such as
  "every value taken by free has been recorded").\<close>

theorem rule_trace_h:
  assumes V: "vdm h P R c G Q"
    and Tr: "\<And>k. P k \<Longrightarrow> T k k"
    and Te: "\<And>k0 k k'. P k0 \<Longrightarrow> T k0 k \<Longrightarrow> renv h R k k' \<Longrightarrow> T k0 k'"
    and Tg: "\<And>k0 k k'. P k0 \<Longrightarrow> T k0 k \<Longrightarrow> G k k' \<Longrightarrow> T k0 (hupd h k')"
  shows "vdm h P R c G (\<lambda>k0 k. Q k0 k \<and> T k0 k)"
proof -
  have main: "T k0 k" if P: "P k0" and Rc: "creach h R c k0 c1 k" for k0 c1 k
    using Rc
  proof (induction rule: creach.induct)
    case start
    show ?case by (rule Tr[OF P])
  next
    case (prog ca ka cb kb)
    have "kb = ka \<or> G ka kb" by (rule vdmD_guar[OF V P prog.hyps(1) prog.hyps(2)])
    then show ?case
    proof
      assume "kb = ka"
      then show ?thesis using Te[OF P prog.IH renv_stutter] by simp
    next
      assume "G ka kb"
      then show ?thesis by (rule Tg[OF P prog.IH])
    qed
  next
    case (env ca ka kb)
    from Te[OF P env.IH env.hyps(2)] show ?case .
  qed
  show ?thesis
  proof (rule vdmI)
    fix k0 k assume "P k0" and "creach h R c k0 Skip k"
    then show "Q k0 k \<and> T k0 k" using vdmD_post[OF V] main by blast
  next
    fix k0 c1 k c2 k' assume "P k0" and "creach h R c k0 c1 k" and "cstep c1 k c2 k'"
    then show "k' = k \<or> G k k'" by (rule vdmD_guar[OF V])
  qed
qed

text \<open>Beyond the thesis: an invariant: a property that holds initially, holds
  despite interference and is preserved by every program step holds in every
  state.  Then every program step is taken in a state satisfying it.  This is
  how the thesis uses inv-\<Sigma> (Section 4.4.2), invB (Section 4.7) and inv-safe
  (Section 4.8.4).\<close>

theorem rule_inv:
  assumes V: "vdm h P R c G Q"
    and I0: "\<And>k. P k \<Longrightarrow> I k"
    and IS: "stable h R I"
    and IG: "\<And>k k'. I k \<Longrightarrow> G k k' \<Longrightarrow> I k'"
  shows "vdm h P R c (\<lambda>k k'. G k k' \<and> I k) (\<lambda>k0 k. Q k0 k \<and> I k)"
proof -
  have main: "I k" if P: "P k0" and Rc: "creach h R c k0 c1 k" for k0 c1 k
    using Rc
  proof (induction rule: creach.induct)
    case start
    show ?case by (rule I0[OF P])
  next
    case (prog ca ka cb kb)
    have "kb = ka \<or> G ka kb" by (rule vdmD_guar[OF V P prog.hyps(1) prog.hyps(2)])
    then have "I kb"
    proof
      assume "kb = ka"
      then show ?thesis using prog.IH by simp
    next
      assume "G ka kb"
      then show ?thesis by (rule IG[OF prog.IH])
    qed
    then show ?case by (rule stableD[OF IS _ renv_stutter])
  next
    case (env ca ka kb)
    from stableD[OF IS env.IH env.hyps(2)] show ?case .
  qed
  show ?thesis
  proof (rule vdmI)
    fix k0 k assume P: "P k0" and Rc: "creach h R c k0 Skip k"
    from vdmD_post[OF V P Rc] main[OF P Rc] show "Q k0 k \<and> I k" by blast
  next
    fix k0 c1 k c2 k' assume P: "P k0" and Rc: "creach h R c k0 c1 k" and S: "cstep c1 k c2 k'"
    have "k' = k \<or> G k k'" by (rule vdmD_guar[OF V P Rc S])
    with main[OF P Rc] show "k' = k \<or> G k k' \<and> I k" by blast
  qed
qed

section \<open>From VDM quadruples to the parallel rule\<close>

text \<open>Mechanisation only: a program, run as a process of RG_Semantics.  Its
  private state is the program still to run together with its private
  variables.\<close>

definition prog_of :: "(('l,'s) com \<times> 'l, 's) rg_prog" where
  "prog_of = (\<lambda>((c,l),s) ((c',l'),s'). cstep c (l,s) c' (l',s'))"

definition hist_of :: "('l,'s) rg_hist \<Rightarrow> (('l,'s) com \<times> 'l, 's) rg_hist" where
  "hist_of h = (\<lambda>(c,l) s. (c, h l s))"

definition rely_of :: "('l,'s) rg_rely \<Rightarrow> (('l,'s) com \<times> 'l, 's) rg_rely" where
  "rely_of R = (\<lambda>(c,l) s s'. R l s s' \<or> s' = s)"

definition pre_of :: "('l,'s) com \<Rightarrow> (('l,'s) rg_conf \<Rightarrow> bool) \<Rightarrow> (('l,'s) com \<times> 'l, 's) rg_conf \<Rightarrow> bool" where
  "pre_of c P = (\<lambda>((c',l),s). c' = c \<and> P (l,s))"

definition guar_of :: "(('l,'s) rg_conf \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> bool) \<Rightarrow>
                       (('l,'s) com \<times> 'l, 's) rg_conf \<Rightarrow> (('l,'s) com \<times> 'l, 's) rg_conf \<Rightarrow> bool" where
  "guar_of G = (\<lambda>((c,l),s) ((c',l'),s'). (l',s') = (l,s) \<or> G (l,s) (l',s'))"

definition post_of :: "(('l,'s) rg_conf \<Rightarrow> ('l,'s) rg_conf \<Rightarrow> bool) \<Rightarrow>
                       (('l,'s) com \<times> 'l, 's) rg_conf \<Rightarrow> (('l,'s) com \<times> 'l, 's) rg_conf \<Rightarrow> bool" where
  "post_of Q = (\<lambda>((c0,l0),s0) ((c,l),s). c = Skip \<longrightarrow> Q (l0,s0) (l,s))"

lemma prog_of_iff [simp]: "prog_of ((c,l),s) ((c',l'),s') \<longleftrightarrow> cstep c (l,s) c' (l',s')"
  by (simp add: prog_of_def)

lemma hist_of_iff [simp]: "hist_of h (c,l) s = (c, h l s)"
  by (simp add: hist_of_def)

lemma rely_of_iff [simp]: "rely_of R (c,l) s s' \<longleftrightarrow> R l s s' \<or> s' = s"
  by (simp add: rely_of_def)

lemma pre_of_iff [simp]: "pre_of c P ((c',l),s) \<longleftrightarrow> c' = c \<and> P (l,s)"
  by (simp add: pre_of_def)

lemma guar_of_iff [simp]: "guar_of G ((c,l),s) ((c',l'),s') \<longleftrightarrow> (l',s') = (l,s) \<or> G (l,s) (l',s')"
  by (simp add: guar_of_def)

lemma post_of_iff [simp]: "post_of Q ((c0,l0),s0) ((c,l),s) \<longleftrightarrow> (c = Skip \<longrightarrow> Q (l0,s0) (l,s))"
  by (simp add: post_of_def)

text \<open>Mechanisation only: a computation of the process prog_of is a computation
  of the program.\<close>

lemma rg_reach_creach:
  assumes "rg_reach prog_of (rely_of R) (hist_of h) ((c,l0),s0) l s"
  shows "creach h R c (l0,s0) (fst l) (snd l, s)"
  using assms
proof (induction rule: rg_reach.induct)
  case start
  show ?case by (simp add: creach.start)
next
  case (prog la sa la' sa')
  obtain ca l1 where la: "la = (ca,l1)" by (cases la)
  obtain cb l2 where la': "la' = (cb,l2)" by (cases la')
  from prog.IH la have R1: "creach h R c (l0,s0) ca (l1,sa)" by simp
  from prog.hyps(2) la la' have S: "cstep ca (l1,sa) cb (l2,sa')" by simp
  from creach.prog[OF R1 S] la' show ?case by simp
next
  case (env la sa sa')
  obtain ca l1 where la: "la = (ca,l1)" by (cases la)
  from env.IH la have R1: "creach h R c (l0,s0) ca (l1,sa)" by simp
  from env.hyps(2) la have "renv h R (l1,sa) (h l1 sa', sa')" by simp
  from creach.env[OF R1 this] la show ?case by simp
qed

text \<open>Thesis: a VDM quadruple {p, r} c {g, q} is a rely/guarantee quadruple of
  RG_Semantics for the process that runs c, so the parallel rule of Section
  2.2 (rg_parallel) applies to programs.  The process's post condition is
  q once c has finished.\<close>

theorem vdm_rg_sat:
  assumes V: "vdm h P R c G Q"
  shows "rg_sat prog_of (hist_of h) (pre_of c P) (rely_of R) (guar_of G) (post_of Q)"
  unfolding rg_sat_def
proof (intro allI impI)
  fix k0 l s
  assume P: "pre_of c P k0" and Rc: "rg_reach prog_of (rely_of R) (hist_of h) k0 l s"
  obtain cl0 s0 where k0a: "k0 = (cl0,s0)" by (cases k0)
  obtain c0 l0 where cl0: "cl0 = (c0,l0)" by (cases cl0)
  from P k0a cl0 have c0: "c0 = c" and P0: "P (l0,s0)" by simp_all
  obtain c1 l1 where l: "l = (c1,l1)" by (cases l)
  have "rg_reach prog_of (rely_of R) (hist_of h) ((c,l0),s0) (c1,l1) s" using Rc k0a cl0 c0 l by simp
  from rg_reach_creach[OF this] have CR: "creach h R c (l0,s0) c1 (l1,s)" by simp
  have post: "post_of Q k0 (l,s)" using vdmD_post[OF V P0] CR k0a cl0 l by auto
  have guar: "\<forall>l' s'. prog_of (l,s) (l',s') \<longrightarrow> guar_of G (l,s) (l',s')"
  proof (intro allI impI)
    fix l' s' assume St: "prog_of (l,s) (l',s')"
    obtain c2 l2 where l': "l' = (c2,l2)" by (cases l')
    from St l l' have "cstep c1 (l1,s) c2 (l2,s')" by simp
    from vdmD_guar[OF V P0 CR this] show "guar_of G (l,s) (l',s')" using l l' by auto
  qed
  from post guar show "post_of Q k0 (l,s) \<and> (\<forall>l' s'. prog_of (l,s) (l',s') \<longrightarrow> guar_of G (l,s) (l',s'))"
    by (rule conjI)
qed

text \<open>Beyond the thesis: a guarantee may be weakened using a property that holds
  in every state of every computation (such as inv-\<Sigma>).  Needed because a
  program step that changes nothing satisfies every guarantee only in states
  where the guarantee's own side conditions (such as inv-\<Sigma>) hold.\<close>

theorem rg_sat_guar_inv:
  assumes V: "rg_sat C h P R G Q"
    and I0: "\<And>c. P c \<Longrightarrow> I c"
    and IR: "\<And>l s s'. I (l,s) \<Longrightarrow> R l s s' \<Longrightarrow> I (h l s', s')"
    and IG: "\<And>l s l' s'. I (l,s) \<Longrightarrow> C (l,s) (l',s') \<Longrightarrow> G (l,s) (l',s') \<Longrightarrow> I (h l' s', s')"
    and GG: "\<And>c c'. I c \<Longrightarrow> G c c' \<Longrightarrow> G' c c'"
  shows "rg_sat C h P R G' (\<lambda>c0 c. Q c0 c \<and> I c)"
  unfolding rg_sat_def
proof (intro allI impI)
  fix c0 l s assume P: "P c0" and Rc: "rg_reach C R h c0 l s"
  have Il: "I (l,s)" using Rc
  proof (induction rule: rg_reach.induct)
    case start
    show ?case using I0[OF P] by simp
  next
    case (prog la sa la' sa')
    have "G (la,sa) (la',sa')" by (rule rg_satD_guar[OF V P prog.hyps(1) prog.hyps(2)])
    from IG[OF prog.IH prog.hyps(2) this] show ?case .
  next
    case (env la sa sa')
    from IR[OF env.IH env.hyps(2)] show ?case .
  qed
  have Q: "Q c0 (l,s)" by (rule rg_satD_post[OF V P Rc])
  have G: "\<forall>l' s'. C (l,s) (l',s') \<longrightarrow> G' (l,s) (l',s')"
  proof (intro allI impI)
    fix l' s' assume "C (l,s) (l',s')"
    from GG[OF Il rg_satD_guar[OF V P Rc this]] show "G' (l,s) (l',s')" .
  qed
  from Q Il G show "(Q c0 (l,s) \<and> I (l,s)) \<and> (\<forall>l' s'. C (l,s) (l',s') \<longrightarrow> G' (l,s) (l',s'))"
    by blast
qed

end
