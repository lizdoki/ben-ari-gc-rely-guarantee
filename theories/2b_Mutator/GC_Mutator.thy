(*  GC_Mutator: the Mutator's code meets its specification (Section 4.6;
    Part 2 of the mechanisation).

    The Mutator's specification (rely guar-Collector, guar guar-Mutator) is
    in GC_Mutator_Spec, and its obligation towards the Collector (Section 4.5.5) is
    in GC_Parallel; both are in Part 1.  This theory proves, with the VDM
    rules of RG_VDM, that the Mutator's code (Algorithm 12, with the
    operations Redirect, Malloc and Zap of Section 4.6) meets that
    specification (Mutator_sat).

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
      the code: Algorithm 12 with Redirect,         Mutator, Mut_op, Redirect,
        Malloc and Zap (Section 4.6)                  Malloc, Zap
      the pre conditions of the operations (4.6)    pre_op
      pre new-risk = {} (Section 4.6)               Mut_pre
      Redirect, Malloc and Zap meet their           Redirect_sat, Malloc_sat,
        specifications (Section 4.6)                  Zap_sat
      the Mutator meets its specification           Mutator_sat           *)

theory GC_Mutator
  imports GC_Mutator_Spec GC_Safety RG_VDM
begin

section \<open>The Mutator's code (Algorithm 12 and Section 4.6)\<close>

text \<open>Thesis: the Mutator "executes these instructions at its discretion"
  (Algorithm 12): repeatedly, it chooses an operation, Redirect(a, i, b),
  Malloc(a, i, b) or Zap(a, i), with arguments satisfying the operation's
  pre condition (Section 4.6), and performs it.  Redirect is a heap update
  and then a marking step, Malloc a heap update and then a removal from
  free, and Zap a single heap update (Section 4.6, Figure 4.10).\<close>

datatype operation = Op_Redirect | Op_Malloc | Op_Zap

text \<open>Thesis: the Mutator's private variables: the operation chosen and its
  arguments a, i and b, and the ghost variable new-risk (Section 4.5.5).\<close>

record ('a,'i) mvars =
  oper :: operation
  ma   :: 'a
  mi   :: 'i
  mb   :: 'a
  nr   :: "('a \<times> 'i) set"

text \<open>Mechanisation only: a configuration of the Mutator, and a program of
  the Mutator.  The Mutator has no history variables.\<close>

type_synonym ('a,'i) mconf = "(('a,'i) mvars, ('a,'i) state) rg_conf"
type_synonym ('a,'i) mcom = "(('a,'i) mvars, ('a,'i) state) com"

text \<open>Thesis: {p, guar-Collector} c {g, q} for a program c of the Mutator: every
  operation of Section 4.6 has rely condition guar-Collector.\<close>

abbreviation mut_sat :: "(('a,'i) mconf \<Rightarrow> bool) \<Rightarrow> ('a,'i) mcom \<Rightarrow>
                         (('a,'i) mconf \<Rightarrow> ('a,'i) mconf \<Rightarrow> bool) \<Rightarrow>
                         (('a,'i) mconf \<Rightarrow> ('a,'i) mconf \<Rightarrow> bool) \<Rightarrow> bool" where
  "mut_sat P c G Q \<equiv> vdm no_hist P rely_M c G Q"

text \<open>Thesis: the pre conditions of the operations (Section 4.6):
    Redirect(a, i, b)  a, b \<in> reach(roots, hp)
    Malloc(a, i, b)    a \<in> reach(roots, hp) \<and> b \<in> free
    Zap(a, i)          a \<in> reach(roots, hp) \<and> (a, i) \<in> dom hp\<close>

definition pre_op :: "operation \<Rightarrow> 'a \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> ('a,'i) state \<Rightarrow> bool" where
  "pre_op opn a i b \<sigma> \<longleftrightarrow> a \<in> reach (roots \<sigma>) (hp \<sigma>) \<and>
     (case opn of Op_Redirect \<Rightarrow> b \<in> reach (roots \<sigma>) (hp \<sigma>)
              | Op_Malloc \<Rightarrow> b \<in> free \<sigma>
              | Op_Zap \<Rightarrow> (a,i) \<in> dom (hp \<sigma>))"

text \<open>Thesis: the Mutator chooses an operation and its arguments.\<close>

definition Mut_choose :: "('a,'i) mcom" where
  "Mut_choose = Basic (\<lambda>(m,\<sigma>) (m',\<sigma>'). \<sigma>' = \<sigma> \<and>
      (\<exists>opn a i b. pre_op opn a i b \<sigma> \<and> m' = m\<lparr>oper := opn, ma := a, mi := i, mb := b\<rparr>))"

text \<open>Thesis: Redirect(a, i, b): hp(a, i) \<leftarrow> b, then marked \<leftarrow> marked \<union> {b}
  (Algorithm 12).  The heap update adds (a, i) to new-risk if b is unmarked;
  the marking step resets new-risk to {} (Section 4.6).\<close>

definition redirect_hp :: "('a,'i) mcom" where
  "redirect_hp = Basic (\<lambda>(m,\<sigma>) (m',\<sigma>'). \<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((ma m, mi m) \<mapsto> mb m)\<rparr> \<and>
      m' = m\<lparr>nr := (if mb m \<in> marked \<sigma> then {} else {(ma m, mi m)})\<rparr>)"

definition redirect_mk :: "('a,'i) mcom" where
  "redirect_mk = Basic (\<lambda>(m,\<sigma>) (m',\<sigma>'). \<sigma>' = \<sigma>\<lparr>marked := marked \<sigma> \<union> {mb m}\<rparr> \<and> m' = m\<lparr>nr := {}\<rparr>)"

definition Redirect :: "('a,'i) mcom" where
  "Redirect = Seq redirect_hp redirect_mk"

text \<open>Thesis: Malloc(a, i, b): hp(a, i) \<leftarrow> b, then free \<leftarrow> free - {b}.\<close>

definition malloc_hp :: "('a,'i) mcom" where
  "malloc_hp = Basic (\<lambda>(m,\<sigma>) (m',\<sigma>'). \<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((ma m, mi m) \<mapsto> mb m)\<rparr> \<and> m' = m)"

definition malloc_fr :: "('a,'i) mcom" where
  "malloc_fr = Basic (\<lambda>(m,\<sigma>) (m',\<sigma>'). \<sigma>' = \<sigma>\<lparr>free := free \<sigma> - {mb m}\<rparr> \<and> m' = m)"

definition Malloc :: "('a,'i) mcom" where
  "Malloc = Seq malloc_hp malloc_fr"

text \<open>Thesis: Zap(a, i): hp(a, i) \<leftarrow> null.\<close>

definition Zap :: "('a,'i) mcom" where
  "Zap = Basic (\<lambda>(m,\<sigma>) (m',\<sigma>'). \<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((ma m, mi m) := None)\<rparr> \<and> m' = m)"

text \<open>Thesis: the Mutator: repeatedly choose an operation and perform it.\<close>

definition is_op :: "operation \<Rightarrow> ('a,'i) mconf \<Rightarrow> bool" where
  "is_op opn = (\<lambda>(m,\<sigma>). oper m = opn)"

definition Mut_op :: "('a,'i) mcom" where
  "Mut_op = Seq Mut_choose (Cond (is_op Op_Redirect) Redirect (Cond (is_op Op_Malloc) Malloc Zap))"

definition Mutator :: "('a,'i) mcom" where
  "Mutator = While (\<lambda>k. True) Mut_op"

section \<open>The Mutator meets its specification (Section 4.6)\<close>

text \<open>Thesis: the Mutator's specification (Sections 4.5.5 and 4.6):
    pre  new-risk = {}
    rely guar-Collector
    guar guar-Mutator
    post true
  The Mutator does not terminate, so its post condition is true.  In
  Isabelle the pre condition also states inv-\<Sigma> and that no free node is
  reachable, free \<inter> reach(roots, hp) = {}: these hold between the Mutator's
  operations (Section 4.4.2; the guarantees of Section 4.6 require the
  second before each heap update).\<close>

definition Mut_pre :: "('a,'i) mconf \<Rightarrow> bool" where
  "Mut_pre = (\<lambda>(m,\<sigma>). inv_state \<sigma> \<and> nr m = {} \<and> free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {})"

text \<open>Thesis: what holds between the Mutator's operations, and so is the
  invariant of its loop: the pre condition.  It holds despite interference:
  by guar-Collector (Section 4.4) the Collector neither changes which nodes
  are reachable (guar_Collector_reach) nor frees a reachable node (Theorem 6).\<close>

definition Mut_inv :: "('a,'i) mconf \<Rightarrow> bool" where
  "Mut_inv = Mut_pre"

text \<open>Mechanisation only: what one step of guar-Collector, with inv-\<Sigma> after it,
  preserves: reachability, the pointers out of reachable nodes, and which
  free nodes are reachable.\<close>

lemma rely_M_facts:
  assumes R: "rely_M m \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  shows "reach (roots \<sigma>') (hp \<sigma>') = reach (roots \<sigma>) (hp \<sigma>)"
    and "free \<sigma> \<subseteq> free \<sigma>'"
    and "free \<sigma>' \<inter> reach (roots \<sigma>) (hp \<sigma>) = free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>)"
    and "\<And>e. fst e \<in> reach (roots \<sigma>) (hp \<sigma>) \<Longrightarrow> hp \<sigma>' e = hp \<sigma> e"
    and "inv_state \<sigma> \<Longrightarrow> inv_state \<sigma>'"
proof -
  have G: "guar_Collector \<sigma> \<sigma>' \<and> (inv_state \<sigma> \<longrightarrow> inv_state \<sigma>')"
    using R guar_Collector_refl unfolding rely_M_def by auto
  then have GC: "guar_Collector \<sigma> \<sigma>'" by simp
  from GC have F: "free \<sigma> \<subseteq> free \<sigma>'" and FN: "free \<sigma>' - free \<sigma> \<subseteq> garbage \<sigma>"
    and E: "\<forall>e. fst e \<in> reach (roots \<sigma>) (hp \<sigma>) \<longrightarrow> hp \<sigma>' e = hp \<sigma> e"
    unfolding guar_Collector_def by blast+
  show "reach (roots \<sigma>') (hp \<sigma>') = reach (roots \<sigma>) (hp \<sigma>)" by (rule guar_Collector_reach[OF GC])
  show "free \<sigma> \<subseteq> free \<sigma>'" by (rule F)
  show "free \<sigma>' \<inter> reach (roots \<sigma>) (hp \<sigma>) = free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>)"
    using F FN unfolding garbage_def by blast
  show "hp \<sigma>' e = hp \<sigma> e" if "fst e \<in> reach (roots \<sigma>) (hp \<sigma>)" for e using E that by blast
  show "inv_state \<sigma>'" if "inv_state \<sigma>" using G that by blast
qed

lemma stableM:
  assumes "\<And>m \<sigma> \<sigma>'. P (m,\<sigma>) \<Longrightarrow> rely_M m \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma> \<Longrightarrow> P (m,\<sigma>')"
  shows "stable no_hist rely_M P"
proof (rule stableI)
  fix l s s' assume "P (l,s)" and "rely_M l s s' \<or> s' = s"
  then show "P (no_hist l s', s')" using assms unfolding no_hist_def by blast
qed

text \<open>Mechanisation only: the rule for an atomic statement of the Mutator whose
  post condition is a property of the state reached, stable under
  guar-Collector.\<close>

lemma rule_basicM:
  assumes PS: "stable no_hist rely_M P" and AS: "stable no_hist rely_M A"
    and S: "\<And>m \<sigma> m' \<sigma>'. P (m,\<sigma>) \<Longrightarrow> r (m,\<sigma>) (m',\<sigma>') \<Longrightarrow> G (m,\<sigma>) (m',\<sigma>') \<and> A (m',\<sigma>')"
  shows "mut_sat P (Basic r) G (\<lambda>k0 k. A k)"
proof (rule rule_basic[OF PS])
  show "tolerates no_hist rely_M P (\<lambda>k0 k. A k)"
    unfolding tolerates_def using stableD[OF AS] by blast
next
  fix k k' assume Pk: "P k" and rk: "r k k'"
  obtain m \<sigma> where k: "k = (m,\<sigma>)" by (cases k)
  obtain m' \<sigma>' where k': "k' = (m',\<sigma>')" by (cases k')
  from S[OF Pk[unfolded k] rk[unfolded k k']] k k' show "G k k' \<and> A (hupd no_hist k')"
    by (simp add: no_hist_def)
qed

lemma Mut_inv_stable: "stable no_hist rely_M (Mut_inv :: ('a,'i) mconf \<Rightarrow> bool)"
proof (rule stableM)
  fix m and \<sigma> \<sigma>' :: "('a,'i) state"
  assume I: "Mut_inv (m,\<sigma>)" and R: "rely_M m \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  from I have inv: "inv_state \<sigma>" and n: "nr m = {}" and d: "free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}"
    unfolding Mut_inv_def Mut_pre_def by simp_all
  have "free \<sigma>' \<inter> reach (roots \<sigma>') (hp \<sigma>') = {}"
    using rely_M_facts(1,3)[OF R] d by simp
  with rely_M_facts(5)[OF R inv] n show "Mut_inv (m,\<sigma>')" unfolding Mut_inv_def Mut_pre_def by simp
qed

text \<open>Thesis: guar-Mutator is reflexive (Section 2.2): a step that changes only
  the Mutator's own choice of operation is allowed.\<close>

lemma guar_M_stutter: "inv_state \<sigma> \<Longrightarrow> nr m' = nr m \<Longrightarrow> guar_M nr (m,\<sigma>) (m',\<sigma>)"
  unfolding guar_M_def guar_Mutator_def by simp

subsection \<open>Choosing an operation\<close>

definition Mut_chosen :: "('a,'i) mconf \<Rightarrow> bool" where
  "Mut_chosen = (\<lambda>(m,\<sigma>). Mut_inv (m,\<sigma>) \<and> pre_op (oper m) (ma m) (mi m) (mb m) \<sigma>)"

text \<open>Thesis: the pre conditions of the operations hold despite interference
  (Section 4.6): reachability does not change, free only grows, and the
  pointers out of reachable nodes do not change.\<close>

lemma pre_op_stable:
  assumes P: "pre_op opn a i b \<sigma>" and R: "rely_M m \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  shows "pre_op opn a i b \<sigma>'"
proof -
  note F = rely_M_facts[OF R]
  from P have aR: "a \<in> reach (roots \<sigma>) (hp \<sigma>)" unfolding pre_op_def by simp
  have aR': "a \<in> reach (roots \<sigma>') (hp \<sigma>')" using aR F(1) by simp
  show ?thesis
  proof (cases opn)
    case Op_Redirect
    with P have "b \<in> reach (roots \<sigma>) (hp \<sigma>)" unfolding pre_op_def by simp
    with aR' F(1) Op_Redirect show ?thesis unfolding pre_op_def by simp
  next
    case Op_Malloc
    with P have "b \<in> free \<sigma>" unfolding pre_op_def by simp
    with aR' F(2) Op_Malloc show ?thesis unfolding pre_op_def by auto
  next
    case Op_Zap
    with P have "(a,i) \<in> dom (hp \<sigma>)" unfolding pre_op_def by simp
    moreover have "hp \<sigma>' (a,i) = hp \<sigma> (a,i)" using F(4)[of "(a,i)"] aR by simp
    ultimately show ?thesis using aR' Op_Zap unfolding pre_op_def by (simp add: domIff)
  qed
qed

lemma Mut_chosen_stable: "stable no_hist rely_M (Mut_chosen :: ('a,'i) mconf \<Rightarrow> bool)"
proof (rule stableM)
  fix m and \<sigma> \<sigma>' :: "('a,'i) state"
  assume P: "Mut_chosen (m,\<sigma>)" and R: "rely_M m \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  from P have I: "Mut_inv (m,\<sigma>)" and O: "pre_op (oper m) (ma m) (mi m) (mb m) \<sigma>"
    unfolding Mut_chosen_def by simp_all
  have "Mut_inv (m,\<sigma>')" by (rule stableD[OF Mut_inv_stable I]) (simp add: no_hist_def R)
  with pre_op_stable[OF O R] show "Mut_chosen (m,\<sigma>')" unfolding Mut_chosen_def by simp
qed

lemma Mut_choose_sat: "mut_sat Mut_inv Mut_choose (guar_M nr) (\<lambda>k0 k. Mut_chosen k)"
  unfolding Mut_choose_def
proof (rule rule_basicM[OF Mut_inv_stable Mut_chosen_stable])
  fix m \<sigma> m' \<sigma>'
  assume I: "Mut_inv (m,\<sigma>)"
    and St: "(\<lambda>(m,\<sigma>) (m',\<sigma>'). \<sigma>' = \<sigma> \<and>
               (\<exists>opn a i b. pre_op opn a i b \<sigma> \<and> m' = m\<lparr>oper := opn, ma := a, mi := i, mb := b\<rparr>)) (m,\<sigma>) (m',\<sigma>')"
  from St obtain opn a i b where \<sigma>': "\<sigma>' = \<sigma>" and P: "pre_op opn a i b \<sigma>"
    and m': "m' = m\<lparr>oper := opn, ma := a, mi := i, mb := b\<rparr>" by auto
  from I have inv: "inv_state \<sigma>" unfolding Mut_inv_def Mut_pre_def by simp
  have "guar_M nr (m,\<sigma>) (m',\<sigma>')"
    unfolding guar_M_def guar_Mutator_def using inv \<sigma>' m' by simp
  moreover have "Mut_chosen (m',\<sigma>')" using I P \<sigma>' m' unfolding Mut_chosen_def Mut_inv_def Mut_pre_def by simp
  ultimately show "guar_M nr (m,\<sigma>) (m',\<sigma>') \<and> Mut_chosen (m',\<sigma>')" by blast
qed

subsection \<open>Redirect\<close>

text \<open>Thesis: between the two steps of Redirect(a, i, b): hp(a, i) = b, a is
  reachable, new-risk \<subseteq> {(a, i)}, and no free node is reachable.  This is
  the pre condition of the marking step; it holds despite interference since
  a is reachable (the last conjunct of guar-Collector, Section 4.4).\<close>

definition R_mid :: "('a,'i) mconf \<Rightarrow> bool" where
  "R_mid = (\<lambda>(m,\<sigma>). inv_state \<sigma> \<and> ma m \<in> reach (roots \<sigma>) (hp \<sigma>) \<and> hp \<sigma> (ma m, mi m) = Some (mb m) \<and>
                     nr m \<subseteq> {(ma m, mi m)} \<and> free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {})"

lemma R_mid_stable: "stable no_hist rely_M (R_mid :: ('a,'i) mconf \<Rightarrow> bool)"
proof (rule stableM)
  fix m and \<sigma> \<sigma>' :: "('a,'i) state"
  assume P: "R_mid (m,\<sigma>)" and R: "rely_M m \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  note F = rely_M_facts[OF R]
  from P have inv: "inv_state \<sigma>" and aR: "ma m \<in> reach (roots \<sigma>) (hp \<sigma>)"
    and h: "hp \<sigma> (ma m, mi m) = Some (mb m)" and n: "nr m \<subseteq> {(ma m, mi m)}"
    and d: "free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}" unfolding R_mid_def by simp_all
  have "hp \<sigma>' (ma m, mi m) = hp \<sigma> (ma m, mi m)" using F(4)[of "(ma m, mi m)"] aR by simp
  with h have h': "hp \<sigma>' (ma m, mi m) = Some (mb m)" by simp
  have aR': "ma m \<in> reach (roots \<sigma>') (hp \<sigma>')" using aR F(1) by simp
  have d': "free \<sigma>' \<inter> reach (roots \<sigma>') (hp \<sigma>') = {}" using F(1,3) d by simp
  from F(5)[OF inv] aR' h' n d' show "R_mid (m,\<sigma>')" unfolding R_mid_def by simp
qed

lemma redirect_hp_sat:
  "mut_sat (\<lambda>k. Mut_chosen k \<and> is_op Op_Redirect k) (redirect_hp :: ('a::finite,'i::finite) mcom)
           (guar_M nr) (\<lambda>k0 k. R_mid k)"
  unfolding redirect_hp_def
proof (rule rule_basicM[OF _ R_mid_stable])
  show "stable no_hist rely_M (\<lambda>k::('a,'i) mconf. Mut_chosen k \<and> is_op Op_Redirect k)"
  proof (rule stableM)
    fix m and \<sigma> \<sigma>' :: "('a,'i) state"
    assume P: "Mut_chosen (m,\<sigma>) \<and> is_op Op_Redirect (m,\<sigma>)" and R: "rely_M m \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    have "Mut_chosen (m,\<sigma>')" by (rule stableD[OF Mut_chosen_stable conjunct1[OF P]]) (simp add: no_hist_def R)
    with P show "Mut_chosen (m,\<sigma>') \<and> is_op Op_Redirect (m,\<sigma>')" unfolding is_op_def by simp
  qed
next
  fix m and \<sigma> :: "('a,'i) state" and m' \<sigma>'
  assume P: "Mut_chosen (m,\<sigma>) \<and> is_op Op_Redirect (m,\<sigma>)"
    and St: "(\<lambda>(m,\<sigma>) (m',\<sigma>'). \<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((ma m, mi m) \<mapsto> mb m)\<rparr> \<and>
               m' = m\<lparr>nr := (if mb m \<in> marked \<sigma> then {} else {(ma m, mi m)})\<rparr>) (m,\<sigma>) (m',\<sigma>')"
  let ?a = "ma m" and ?i = "mi m" and ?b = "mb m"
  from St have s': "\<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((?a,?i) \<mapsto> ?b)\<rparr>"
    and m': "m' = m\<lparr>nr := (if ?b \<in> marked \<sigma> then {} else {(?a,?i)})\<rparr>" by simp_all
  from P have C: "Mut_chosen (m,\<sigma>)" and O: "oper m = Op_Redirect" unfolding is_op_def by simp_all
  from C have inv: "inv_state \<sigma>" and nr0: "nr m = {}" and disj: "free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}"
    and PO: "pre_op (oper m) (ma m) (mi m) (mb m) \<sigma>"
    unfolding Mut_chosen_def Mut_inv_def Mut_pre_def by simp_all
  from PO have aR: "ma m \<in> reach (roots \<sigma>) (hp \<sigma>)" unfolding pre_op_def by simp
  from PO O have bR: "?b \<in> reach (roots \<sigma>) (hp \<sigma>)" unfolding pre_op_def by simp
  let ?h = "(hp \<sigma>)((?a,?i) \<mapsto> ?b)"
  have Rsub: "reach (roots \<sigma>) ?h \<subseteq> reach (roots \<sigma>) (hp \<sigma>)" by (rule reach_redirect_subset[OF bR])
  have aR': "?a \<in> reach (roots \<sigma>) ?h" by (rule reach_self_upd[OF aR])
  have anf: "?a \<notin> free \<sigma>" using disj aR by blast
  have d': "free \<sigma> \<inter> reach (roots \<sigma>) ?h = {}" using Rsub disj by blast
  have inv': "inv_state \<sigma>'"
    using inv s' anf d' unfolding inv_state_def by (auto simp: domIff)
  have g: "g_Redirect_hp ?a ?i ?b (nr m) \<sigma> (nr m') \<sigma>'"
    unfolding g_Redirect_hp_def using s' m' nr0 disj aR bR by simp
  have "guar_Mutator (nr m) \<sigma> (nr m') \<sigma>'"
    unfolding guar_Mutator_def using inv inv' g by blast
  then have "guar_M nr (m,\<sigma>) (m',\<sigma>')" unfolding guar_M_def by simp
  moreover have "R_mid (m',\<sigma>')" using inv' aR' d' s' m' unfolding R_mid_def by auto
  ultimately show "guar_M nr (m,\<sigma>) (m',\<sigma>') \<and> R_mid (m',\<sigma>')" by blast
qed

lemma redirect_mk_sat: "mut_sat R_mid (redirect_mk :: ('a,'i) mcom) (guar_M nr) (\<lambda>k0 k. Mut_inv k)"
  unfolding redirect_mk_def
proof (rule rule_basicM[OF R_mid_stable Mut_inv_stable])
  fix m and \<sigma> :: "('a,'i) state" and m' \<sigma>'
  assume P: "R_mid (m,\<sigma>)"
    and St: "(\<lambda>(m,\<sigma>) (m',\<sigma>'). \<sigma>' = \<sigma>\<lparr>marked := marked \<sigma> \<union> {mb m}\<rparr> \<and> m' = m\<lparr>nr := {}\<rparr>) (m,\<sigma>) (m',\<sigma>')"
  from St have s': "\<sigma>' = \<sigma>\<lparr>marked := marked \<sigma> \<union> {mb m}\<rparr>" and m': "m' = m\<lparr>nr := {}\<rparr>" by simp_all
  from P have inv: "inv_state \<sigma>" and aR: "ma m \<in> reach (roots \<sigma>) (hp \<sigma>)"
    and hab: "hp \<sigma> (ma m, mi m) = Some (mb m)" and nrs: "nr m \<subseteq> {(ma m, mi m)}"
    and disj: "free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}" unfolding R_mid_def by simp_all
  have bR: "mb m \<in> reach (roots \<sigma>) (hp \<sigma>)" by (rule reach_step[OF aR hab])
  have inv': "inv_state \<sigma>'" using inv_state_mark[OF inv, of "{mb m}"] s' by simp
  have g: "g_Redirect_mk (ma m) (mi m) (mb m) (nr m) \<sigma> (nr m') \<sigma>'"
    unfolding g_Redirect_mk_def using s' m' hab bR nrs by simp
  have "guar_Mutator (nr m) \<sigma> (nr m') \<sigma>'"
    unfolding guar_Mutator_def using inv inv' g by blast
  then have "guar_M nr (m,\<sigma>) (m',\<sigma>')" unfolding guar_M_def by simp
  moreover have "Mut_inv (m',\<sigma>')" using inv' disj s' m' unfolding Mut_inv_def Mut_pre_def by simp
  ultimately show "guar_M nr (m,\<sigma>) (m',\<sigma>') \<and> Mut_inv (m',\<sigma>')" by blast
qed

text \<open>Thesis: Redirect meets its specification: each of its two steps is
  allowed by its guarantee, in order (Section 4.6), and it ends with
  new-risk = {}.\<close>

lemma Redirect_sat:
  "mut_sat (\<lambda>k. Mut_chosen k \<and> is_op Op_Redirect k) (Redirect :: ('a::finite,'i::finite) mcom)
           (guar_M nr) (\<lambda>k0 k. Mut_inv k)"
proof -
  have "mut_sat (\<lambda>k. Mut_chosen k \<and> is_op Op_Redirect k) (Redirect :: ('a,'i) mcom) (guar_M nr)
          (seq_post (\<lambda>k0 k. R_mid k) (\<lambda>k0 k. Mut_inv k))"
    unfolding Redirect_def by (rule rule_seq[OF redirect_hp_sat redirect_mk_sat]) simp
  then show ?thesis by (rule rule_weaken) (auto simp: seq_post_def)
qed

subsection \<open>Malloc\<close>

text \<open>Thesis: between the two steps of Malloc(a, i, b): hp(a, i) = b, a is
  reachable, b is free, new-risk = {}, and at most b is both free and
  reachable (the overlap inv-\<Sigma> allows, Section 4.4.2).\<close>

definition Ml_mid :: "('a,'i) mconf \<Rightarrow> bool" where
  "Ml_mid = (\<lambda>(m,\<sigma>). inv_state \<sigma> \<and> nr m = {} \<and> ma m \<in> reach (roots \<sigma>) (hp \<sigma>) \<and>
                      hp \<sigma> (ma m, mi m) = Some (mb m) \<and> mb m \<in> free \<sigma> \<and>
                      free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) \<subseteq> {mb m})"

lemma Ml_mid_stable: "stable no_hist rely_M (Ml_mid :: ('a,'i) mconf \<Rightarrow> bool)"
proof (rule stableM)
  fix m and \<sigma> \<sigma>' :: "('a,'i) state"
  assume P: "Ml_mid (m,\<sigma>)" and R: "rely_M m \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  note F = rely_M_facts[OF R]
  from P have inv: "inv_state \<sigma>" and n: "nr m = {}" and aR: "ma m \<in> reach (roots \<sigma>) (hp \<sigma>)"
    and h: "hp \<sigma> (ma m, mi m) = Some (mb m)" and bf: "mb m \<in> free \<sigma>"
    and d: "free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) \<subseteq> {mb m}" unfolding Ml_mid_def by simp_all
  have "hp \<sigma>' (ma m, mi m) = hp \<sigma> (ma m, mi m)" using F(4)[of "(ma m, mi m)"] aR by simp
  with h have h': "hp \<sigma>' (ma m, mi m) = Some (mb m)" by simp
  have aR': "ma m \<in> reach (roots \<sigma>') (hp \<sigma>')" using aR F(1) by simp
  have bf': "mb m \<in> free \<sigma>'" using bf F(2) by blast
  have d': "free \<sigma>' \<inter> reach (roots \<sigma>') (hp \<sigma>') \<subseteq> {mb m}" using F(1,3) d by simp
  from F(5)[OF inv] n aR' h' bf' d' show "Ml_mid (m,\<sigma>')" unfolding Ml_mid_def by simp
qed

lemma malloc_hp_sat:
  "mut_sat (\<lambda>k. Mut_chosen k \<and> is_op Op_Malloc k) (malloc_hp :: ('a::finite,'i::finite) mcom)
           (guar_M nr) (\<lambda>k0 k. Ml_mid k)"
  unfolding malloc_hp_def
proof (rule rule_basicM[OF _ Ml_mid_stable])
  show "stable no_hist rely_M (\<lambda>k::('a,'i) mconf. Mut_chosen k \<and> is_op Op_Malloc k)"
  proof (rule stableM)
    fix m and \<sigma> \<sigma>' :: "('a,'i) state"
    assume P: "Mut_chosen (m,\<sigma>) \<and> is_op Op_Malloc (m,\<sigma>)" and R: "rely_M m \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    have "Mut_chosen (m,\<sigma>')" by (rule stableD[OF Mut_chosen_stable conjunct1[OF P]]) (simp add: no_hist_def R)
    with P show "Mut_chosen (m,\<sigma>') \<and> is_op Op_Malloc (m,\<sigma>')" unfolding is_op_def by simp
  qed
next
  fix m and \<sigma> :: "('a,'i) state" and m' \<sigma>'
  assume P: "Mut_chosen (m,\<sigma>) \<and> is_op Op_Malloc (m,\<sigma>)"
    and St: "(\<lambda>(m,\<sigma>) (m',\<sigma>'). \<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((ma m, mi m) \<mapsto> mb m)\<rparr> \<and> m' = m) (m,\<sigma>) (m',\<sigma>')"
  let ?a = "ma m" and ?i = "mi m" and ?b = "mb m"
  from St have s': "\<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((?a,?i) \<mapsto> ?b)\<rparr>" and m': "m' = m" by simp_all
  from P have C: "Mut_chosen (m,\<sigma>)" and O: "oper m = Op_Malloc" unfolding is_op_def by simp_all
  from C have inv: "inv_state \<sigma>" and nr0: "nr m = {}" and disj: "free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}"
    and PO: "pre_op (oper m) (ma m) (mi m) (mb m) \<sigma>"
    unfolding Mut_chosen_def Mut_inv_def Mut_pre_def by simp_all
  from PO have aR: "ma m \<in> reach (roots \<sigma>) (hp \<sigma>)" unfolding pre_op_def by simp
  from PO O have bf: "?b \<in> free \<sigma>" unfolding pre_op_def by simp
  let ?h = "(hp \<sigma>)((?a,?i) \<mapsto> ?b)"
  have bleaf: "\<forall>j. hp \<sigma> (?b,j) = None" using inv bf unfolding inv_state_def by (auto simp: domIff)
  have Rsub: "reach (roots \<sigma>) ?h \<subseteq> reach (roots \<sigma>) (hp \<sigma>) \<union> {?b}"
    by (rule reach_redirect_leaf_subset[OF bleaf])
  have aR': "?a \<in> reach (roots \<sigma>) ?h" by (rule reach_self_upd[OF aR])
  have anf: "?a \<notin> free \<sigma>" using disj aR by blast
  have d': "free \<sigma> \<inter> reach (roots \<sigma>) ?h \<subseteq> {?b}" using Rsub disj by blast
  have inv': "inv_state \<sigma>'"
  proof -
    have "card (free \<sigma> \<inter> reach (roots \<sigma>) ?h) \<le> 1"
      using card_mono[OF _ d'] by simp
    then show ?thesis using inv s' anf unfolding inv_state_def by (auto simp: domIff)
  qed
  have g: "g_Malloc_hp ?a ?i ?b (nr m) \<sigma> (nr m') \<sigma>'"
    unfolding g_Malloc_hp_def using s' m' nr0 disj aR bf by simp
  have "guar_Mutator (nr m) \<sigma> (nr m') \<sigma>'"
    unfolding guar_Mutator_def using inv inv' g by blast
  then have "guar_M nr (m,\<sigma>) (m',\<sigma>')" unfolding guar_M_def by simp
  moreover have "Ml_mid (m',\<sigma>')" using inv' nr0 aR' bf d' s' m' unfolding Ml_mid_def by auto
  ultimately show "guar_M nr (m,\<sigma>) (m',\<sigma>') \<and> Ml_mid (m',\<sigma>')" by blast
qed

lemma malloc_fr_sat: "mut_sat Ml_mid (malloc_fr :: ('a,'i) mcom) (guar_M nr) (\<lambda>k0 k. Mut_inv k)"
  unfolding malloc_fr_def
proof (rule rule_basicM[OF Ml_mid_stable Mut_inv_stable])
  fix m and \<sigma> :: "('a,'i) state" and m' \<sigma>'
  assume P: "Ml_mid (m,\<sigma>)"
    and St: "(\<lambda>(m,\<sigma>) (m',\<sigma>'). \<sigma>' = \<sigma>\<lparr>free := free \<sigma> - {mb m}\<rparr> \<and> m' = m) (m,\<sigma>) (m',\<sigma>')"
  from St have s': "\<sigma>' = \<sigma>\<lparr>free := free \<sigma> - {mb m}\<rparr>" and m': "m' = m" by simp_all
  from P have inv: "inv_state \<sigma>" and nr0: "nr m = {}" and bf: "mb m \<in> free \<sigma>"
    and hab: "hp \<sigma> (ma m, mi m) = Some (mb m)"
    and disj: "free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) \<subseteq> {mb m}" unfolding Ml_mid_def by simp_all
  have d': "(free \<sigma> - {mb m}) \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}" using disj by blast
  have inv': "inv_state \<sigma>'" using inv s' d' unfolding inv_state_def by (auto simp: domIff)
  have g: "g_Malloc_fr (ma m) (mi m) (mb m) (nr m) \<sigma> (nr m') \<sigma>'"
    unfolding g_Malloc_fr_def using s' m' hab bf nr0 by simp
  have "guar_Mutator (nr m) \<sigma> (nr m') \<sigma>'"
    unfolding guar_Mutator_def using inv inv' g by blast
  then have "guar_M nr (m,\<sigma>) (m',\<sigma>')" unfolding guar_M_def by simp
  moreover have "Mut_inv (m',\<sigma>')" using inv' nr0 d' s' m' unfolding Mut_inv_def Mut_pre_def by simp
  ultimately show "guar_M nr (m,\<sigma>) (m',\<sigma>') \<and> Mut_inv (m',\<sigma>')" by blast
qed

lemma Malloc_sat:
  "mut_sat (\<lambda>k. Mut_chosen k \<and> is_op Op_Malloc k) (Malloc :: ('a::finite,'i::finite) mcom)
           (guar_M nr) (\<lambda>k0 k. Mut_inv k)"
proof -
  have "mut_sat (\<lambda>k. Mut_chosen k \<and> is_op Op_Malloc k) (Malloc :: ('a,'i) mcom) (guar_M nr)
          (seq_post (\<lambda>k0 k. Ml_mid k) (\<lambda>k0 k. Mut_inv k))"
    unfolding Malloc_def by (rule rule_seq[OF malloc_hp_sat malloc_fr_sat]) simp
  then show ?thesis by (rule rule_weaken) (auto simp: seq_post_def)
qed

subsection \<open>Zap\<close>

lemma Zap_sat:
  "mut_sat (\<lambda>k. Mut_chosen k \<and> is_op Op_Zap k) (Zap :: ('a::finite,'i::finite) mcom)
           (guar_M nr) (\<lambda>k0 k. Mut_inv k)"
  unfolding Zap_def
proof (rule rule_basicM[OF _ Mut_inv_stable])
  show "stable no_hist rely_M (\<lambda>k::('a,'i) mconf. Mut_chosen k \<and> is_op Op_Zap k)"
  proof (rule stableM)
    fix m and \<sigma> \<sigma>' :: "('a,'i) state"
    assume P: "Mut_chosen (m,\<sigma>) \<and> is_op Op_Zap (m,\<sigma>)" and R: "rely_M m \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
    have "Mut_chosen (m,\<sigma>')" by (rule stableD[OF Mut_chosen_stable conjunct1[OF P]]) (simp add: no_hist_def R)
    with P show "Mut_chosen (m,\<sigma>') \<and> is_op Op_Zap (m,\<sigma>')" unfolding is_op_def by simp
  qed
next
  fix m and \<sigma> :: "('a,'i) state" and m' \<sigma>'
  assume P: "Mut_chosen (m,\<sigma>) \<and> is_op Op_Zap (m,\<sigma>)"
    and St: "(\<lambda>(m,\<sigma>) (m',\<sigma>'). \<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((ma m, mi m) := None)\<rparr> \<and> m' = m) (m,\<sigma>) (m',\<sigma>')"
  from St have s': "\<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((ma m, mi m) := None)\<rparr>" and m': "m' = m" by simp_all
  from P have C: "Mut_chosen (m,\<sigma>)" and O: "oper m = Op_Zap" unfolding is_op_def by simp_all
  from C have inv: "inv_state \<sigma>" and nr0: "nr m = {}" and disj: "free \<sigma> \<inter> reach (roots \<sigma>) (hp \<sigma>) = {}"
    and PO: "pre_op (oper m) (ma m) (mi m) (mb m) \<sigma>"
    unfolding Mut_chosen_def Mut_inv_def Mut_pre_def by simp_all
  from PO have aR: "ma m \<in> reach (roots \<sigma>) (hp \<sigma>)" unfolding pre_op_def by simp
  from PO O have dom: "(ma m, mi m) \<in> dom (hp \<sigma>)" unfolding pre_op_def by simp
  have Rsub: "reach (roots \<sigma>) ((hp \<sigma>)((ma m, mi m) := None)) \<subseteq> reach (roots \<sigma>) (hp \<sigma>)"
    by (rule reach_del)
  have inv': "inv_state \<sigma>'" using inv_state_del[OF inv, of "(ma m, mi m)"] s' by simp
  have g: "g_Zap (ma m) (mi m) (nr m) \<sigma> (nr m') \<sigma>'"
    unfolding g_Zap_def using s' m' nr0 disj aR dom by simp
  have "guar_Mutator (nr m) \<sigma> (nr m') \<sigma>'"
    unfolding guar_Mutator_def using inv inv' g by blast
  then have "guar_M nr (m,\<sigma>) (m',\<sigma>')" unfolding guar_M_def by simp
  moreover have "Mut_inv (m',\<sigma>')"
  proof -
    have "free \<sigma> \<inter> reach (roots \<sigma>) ((hp \<sigma>)((ma m, mi m) := None)) = {}" using Rsub disj by blast
    with inv' nr0 s' m' show ?thesis unfolding Mut_inv_def Mut_pre_def by simp
  qed
  ultimately show "guar_M nr (m,\<sigma>) (m',\<sigma>') \<and> Mut_inv (m',\<sigma>')" by blast
qed

subsection \<open>The Mutator\<close>

text \<open>Thesis: one operation: choose, then perform the operation chosen.\<close>

lemma Mut_op_sat:
  "mut_sat Mut_inv (Mut_op :: ('a::finite,'i::finite) mcom) (guar_M nr) (\<lambda>k0 k. Mut_inv k)"
proof -
  have BH: "\<And>opn k. is_op opn (hupd no_hist k) = is_op opn k"
    by (simp add: is_op_def no_hist_def hupd_def split_beta)
  have Inner: "mut_sat (\<lambda>k. Mut_chosen k \<and> \<not> is_op Op_Redirect k) (Cond (is_op Op_Malloc) Malloc Zap :: ('a,'i) mcom)
                 (guar_M nr) (\<lambda>k0 k. Mut_inv k)"
  proof (rule rule_cond)
    show "mut_sat (\<lambda>k. (Mut_chosen k \<and> \<not> is_op Op_Redirect k) \<and> is_op Op_Malloc k) (Malloc :: ('a,'i) mcom)
            (guar_M nr) (\<lambda>k0 k. Mut_inv k)"
      by (rule rule_weaken[OF Malloc_sat]) simp_all
    show "mut_sat (\<lambda>k. (Mut_chosen k \<and> \<not> is_op Op_Redirect k) \<and> \<not> is_op Op_Malloc k) (Zap :: ('a,'i) mcom)
            (guar_M nr) (\<lambda>k0 k. Mut_inv k)"
    proof (rule rule_weaken[OF Zap_sat])
      fix k :: "('a,'i) mconf" assume A: "(Mut_chosen k \<and> \<not> is_op Op_Redirect k) \<and> \<not> is_op Op_Malloc k"
      obtain m \<sigma> where k: "k = (m,\<sigma>)" by (cases k)
      from A k have "oper m \<noteq> Op_Redirect" "oper m \<noteq> Op_Malloc" by (simp_all add: is_op_def)
      then have "oper m = Op_Zap" by (cases "oper m") simp_all
      with A k show "Mut_chosen k \<and> is_op Op_Zap k" by (simp add: is_op_def)
    qed simp_all
    show "stable no_hist rely_M (\<lambda>k::('a,'i) mconf. Mut_chosen k \<and> \<not> is_op Op_Redirect k)"
    proof (rule stableM)
      fix m and \<sigma> \<sigma>' :: "('a,'i) state"
      assume P: "Mut_chosen (m,\<sigma>) \<and> \<not> is_op Op_Redirect (m,\<sigma>)" and R: "rely_M m \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
      have "Mut_chosen (m,\<sigma>')" by (rule stableD[OF Mut_chosen_stable conjunct1[OF P]]) (simp add: no_hist_def R)
      with P show "Mut_chosen (m,\<sigma>') \<and> \<not> is_op Op_Redirect (m,\<sigma>')" unfolding is_op_def by simp
    qed
  qed (rule BH, simp)
  have Disp: "mut_sat Mut_chosen (Cond (is_op Op_Redirect) Redirect (Cond (is_op Op_Malloc) Malloc Zap) :: ('a,'i) mcom)
                (guar_M nr) (\<lambda>k0 k. Mut_inv k)"
  proof (rule rule_cond[OF _ Inner Mut_chosen_stable])
    show "mut_sat (\<lambda>k. Mut_chosen k \<and> is_op Op_Redirect k) (Redirect :: ('a,'i) mcom) (guar_M nr) (\<lambda>k0 k. Mut_inv k)"
      by (rule Redirect_sat)
  qed (rule BH, simp)
  have "mut_sat Mut_inv (Mut_op :: ('a,'i) mcom) (guar_M nr) (seq_post (\<lambda>k0 k. Mut_chosen k) (\<lambda>k0 k. Mut_inv k))"
    unfolding Mut_op_def by (rule rule_seq[OF Mut_choose_sat Disp]) simp
  then show ?thesis by (rule rule_weaken) (auto simp: seq_post_def)
qed

text \<open>Thesis: the Mutator meets its specification,
    {new-risk = {}, guar-Collector} Mutator {guar-Mutator, true},
  by the while rule with inv = the pre condition and a so-far relation that
  says nothing (the loop does not terminate).  Each step of the Mutator is a
  step of one of its operations allowed by that operation's guarantee.\<close>

theorem Mutator_sat:
  "mut_sat Mut_pre (Mutator :: ('a::finite,'i::finite) mcom) (guar_M nr) (\<lambda>k0 k. True)"
  unfolding Mutator_def
proof (rule rule_while[where I = Mut_inv and sofar = "\<lambda>k0 k. True"])
  fix k :: "('a,'i) mconf" assume "Mut_pre k" then show "Mut_inv k" by (simp add: Mut_inv_def)
next
  show "mut_sat (\<lambda>k. Mut_inv k \<and> True) (Mut_op :: ('a,'i) mcom) (guar_M nr) (\<lambda>k0 k. Mut_inv k \<and> True)"
    by (rule rule_weaken[OF Mut_op_sat]) simp_all
next
  show "stable no_hist rely_M (Mut_inv :: ('a,'i) mconf \<Rightarrow> bool)" by (rule Mut_inv_stable)
next
  show "tolerates no_hist rely_M Mut_inv (\<lambda>k0 k::('a,'i) mconf. True)" unfolding tolerates_def by simp
qed simp_all


end
