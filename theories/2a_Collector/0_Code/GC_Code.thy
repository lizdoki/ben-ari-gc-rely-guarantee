(*  GC_Code: the Collector's code (Appendix C) and its private variables.

    The code of Algorithms 15-20, with Mark written as Algorithm 7, in the
    language of RG_VDM.  Also here, labelled "Mechanisation only:", are the
    Collector's record of the possible values of free (Section 2.3) and facts
    about interference that the proofs in GC_Mark_Sat to GC_Collector use.

    HOW TO READ THE LABELS.  Each definition and theorem below, or each group
    of them, has a text block saying how it relates to the thesis:
      "Thesis:"             it is that part of the thesis;
      "Beyond the thesis:"  the thesis states or argues it informally or not
                            at all; the label says which part of the thesis
                            it makes precise or supports;
      "Mechanisation only:" a helper needed only for the Isabelle proof.
    Section, lemma and theorem numbers are those of the thesis.

      thesis                                        Isabelle
      ------------------------------------------    ------------------------
      the private variables (owns clauses, App. C)  record cvars
      Mark-kids, Propagate, Mark (Alg. 18, 17, 7)   MarkKids, Propagate, Mark
      Unmark (Algorithm 15)                         Unmark
      Add-to-free, Sweep (Algorithms 20, 19)        AddToFree, Sweep
      the Collector: Unmark; Mark; Sweep            Collector
      possible values of free (Section 2.3)         Fv, hC, pv, hist_ok      *)

theory GC_Code
  imports GC_Collector_Spec RG_VDM GC_Invariant
begin

section \<open>The Collector's private variables\<close>

text \<open>Thesis: the Collector's private variables: the owns variables of Appendix
  C (consid, s, checked, and mc of Algorithm 7), and the variables bound by
  "let x \<in> ..." and "let i \<in> ...", and by the parameter of Mark-kids(x) and
  Add-to-free(x).  cleared is the loop variable of the for-loop of
  Add-to-free (Algorithm 20, line 1), which is written below as a while-loop
  over the indices already visited.  Fv is a history variable (Section 2.3):
  the values taken by free, one per step, oldest first, so that the possible
  values of free over an interval can be read off it (pv below).\<close>

record ('a,'i) cvars =
  consid  :: "'a set"
  checked :: "'i set"
  mc      :: nat
  s       :: "('a \<times> 'i) set"
  x       :: 'a
  i       :: 'i
  cleared :: "'i set"
  Fv      :: "'a set list"

text \<open>Mechanisation only: a configuration of the Collector (its private
  variables and the shared state), and a program of the Collector.\<close>

type_synonym ('a,'i) cconf = "(('a,'i) cvars, ('a,'i) state) rg_conf"

type_synonym ('a,'i) ccom = "(('a,'i) cvars, ('a,'i) state) com"

text \<open>Thesis: possible values (Section 2.3): after every step, by either
  process, the current value of free is recorded.\<close>

definition hC :: "(('a,'i) cvars, ('a,'i) state) rg_hist" where
  "hC l \<sigma> = l\<lparr>Fv := Fv l @ [free \<sigma>]\<rparr>"

lemma hC_sel [simp]:
  "consid (hC l \<sigma>) = consid l" "checked (hC l \<sigma>) = checked l" "mc (hC l \<sigma>) = mc l"
  "s (hC l \<sigma>) = s l" "x (hC l \<sigma>) = x l" "i (hC l \<sigma>) = i l" "cleared (hC l \<sigma>) = cleared l"
  "Fv (hC l \<sigma>) = Fv l @ [free \<sigma>]"
  by (simp_all add: hC_def)

text \<open>Thesis: {p, rely-Collector} c {g, q}, for an operation c of the
  Collector: every operation in Appendix C has rely condition
  rely-Collector.\<close>

abbreviation coll_sat :: "(('a,'i) cconf \<Rightarrow> bool) \<Rightarrow> ('a,'i) ccom \<Rightarrow>
                          (('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool) \<Rightarrow>
                          (('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool) \<Rightarrow> bool" where
  "coll_sat P c G Q \<equiv> vdm hC P (rely_C s) c G Q"

text \<open>Mechanisation only: an environment step, seen by the Collector.\<close>

abbreviation envC :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "envC \<equiv> renv hC (rely_C s)"

lemma envC_iff: "envC (l,\<sigma>) (l',\<sigma>') \<longleftrightarrow> (env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>) \<and> l' = hC l \<sigma>'"
  by (simp add: rely_C_def)

section \<open>The code (Appendix C)\<close>

text \<open>Thesis: the atomic statements of the code.  Each is a relation between
  the configuration before and after it.  Statements that only change
  private variables leave the shared state alone.\<close>

text \<open>Thesis: consid \<leftarrow> {} (Algorithms 15, 17 and 19, line 1).\<close>

definition consid_reset :: "('a,'i) ccom" where
  "consid_reset = Basic (\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l\<lparr>consid := {}\<rparr> \<and> \<sigma>' = \<sigma>)"

text \<open>Thesis: the test of the loops of Algorithms 15, 17 and 19 (line 2):
  consid \<noteq> Addr.\<close>

definition consid_test :: "('a,'i) cconf \<Rightarrow> bool" where
  "consid_test = (\<lambda>(l,\<sigma>). consid l \<noteq> UNIV)"

text \<open>Thesis: let x \<in> (Addr - consid) in ... (Algorithms 15, 17 and 19, line 3).\<close>

definition pick_x :: "('a,'i) ccom" where
  "pick_x = Basic (\<lambda>(l,\<sigma>) (l',\<sigma>'). (\<exists>y. y \<notin> consid l \<and> l' = l\<lparr>x := y\<rparr>) \<and> \<sigma>' = \<sigma>)"

text \<open>Thesis: consid \<leftarrow> consid \<union> {x} (Algorithms 15, 17 and 19, line 6).\<close>

definition consid_add :: "('a,'i) ccom" where
  "consid_add = Basic (\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l\<lparr>consid := consid l \<union> {x l}\<rparr> \<and> \<sigma>' = \<sigma>)"

subsection \<open>Mark-kids (Algorithm 18)\<close>

text \<open>Thesis: Algorithm 18, line 1: checked \<leftarrow> {}.\<close>

definition MK_init :: "('a,'i) ccom" where
  "MK_init = Basic (\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l\<lparr>checked := {}\<rparr> \<and> \<sigma>' = \<sigma>)"

text \<open>Thesis: Algorithm 18, line 2: the test checked \<noteq> Index.\<close>

definition MK_test :: "('a,'i) cconf \<Rightarrow> bool" where
  "MK_test = (\<lambda>(l,\<sigma>). checked l \<noteq> UNIV)"

text \<open>Thesis: Algorithm 18, line 3: let i \<in> (Index - checked).\<close>

definition MK_pick :: "('a,'i) ccom" where
  "MK_pick = Basic (\<lambda>(l,\<sigma>) (l',\<sigma>'). (\<exists>j. j \<notin> checked l \<and> l' = l\<lparr>i := j\<rparr>) \<and> \<sigma>' = \<sigma>)"

text \<open>Thesis: Algorithm 18, line 4, one atomic step:
    \<langle>marked, s \<leftarrow> marked \<union> {hp(x, i) | (x, i) \<in> dom hp}, s \<union> {(x, i)}\<rangle>.\<close>

definition MK_mark :: "('a,'i) ccom" where
  "MK_mark = Basic (\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l\<lparr>s := s l \<union> {(x l, i l)}\<rparr> \<and>
                      \<sigma>' = \<sigma>\<lparr>marked := marked \<sigma> \<union> {b. hp \<sigma> (x l, i l) = Some b}\<rparr>)"

text \<open>Thesis: Algorithm 18, line 5: checked \<leftarrow> checked \<union> {i}.\<close>

definition MK_add :: "('a,'i) ccom" where
  "MK_add = Basic (\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l\<lparr>checked := checked l \<union> {i l}\<rparr> \<and> \<sigma>' = \<sigma>)"

text \<open>Thesis: Mark-kids(x), Algorithm 18.\<close>

definition MK_body :: "('a,'i) ccom" where
  "MK_body = Seq MK_pick (Seq MK_mark MK_add)"

definition MarkKids :: "('a,'i) ccom" where
  "MarkKids = Seq MK_init (While MK_test MK_body)"

subsection \<open>Propagate (Algorithm 17)\<close>

text \<open>Thesis: Algorithm 17, lines 3-6.\<close>

definition P_body :: "('a,'i) ccom" where
  "P_body = Seq pick_x (Seq (IfThen (\<lambda>(l,\<sigma>). x l \<in> marked \<sigma>) MarkKids) consid_add)"

definition Propagate :: "('a,'i) ccom" where
  "Propagate = Seq consid_reset (While consid_test P_body)"

subsection \<open>Mark (Algorithm 7)\<close>

text \<open>Thesis: Algorithm 7, lines 1 and 4: mc \<leftarrow> card marked.\<close>

definition mc_count :: "('a,'i) ccom" where
  "mc_count = Basic (\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l\<lparr>mc := card (marked \<sigma>)\<rparr> \<and> \<sigma>' = \<sigma>)"

text \<open>Thesis: Algorithm 7, line 3: the test card marked \<noteq> mc.\<close>

definition M_test :: "('a,'i) cconf \<Rightarrow> bool" where
  "M_test = (\<lambda>(l,\<sigma>). card (marked \<sigma>) \<noteq> mc l)"

text \<open>Thesis: Algorithm 7, line 6: s \<leftarrow> {}.\<close>

definition s_reset :: "('a,'i) ccom" where
  "s_reset = Basic (\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l\<lparr>s := {}\<rparr> \<and> \<sigma>' = \<sigma>)"

text \<open>Thesis: Mark, Algorithm 7: the body (mc \<leftarrow> card marked; Propagate), then
  the loop, then s \<leftarrow> {}.\<close>

definition M_body :: "('a,'i) ccom" where
  "M_body = Seq mc_count Propagate"

definition Mark :: "('a,'i) ccom" where
  "Mark = Seq (Seq M_body (While M_test M_body)) s_reset"

subsection \<open>Unmark (Algorithm 15)\<close>

text \<open>Thesis: Algorithm 15, line 5: marked \<leftarrow> marked - {x}.\<close>

definition unmark_x :: "('a,'i) ccom" where
  "unmark_x = Basic (\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l \<and> \<sigma>' = \<sigma>\<lparr>marked := marked \<sigma> - {x l}\<rparr>)"

text \<open>Thesis: Algorithm 15, line 4: the test x \<notin> (roots \<union> free).\<close>

definition U_test :: "('a,'i) cconf \<Rightarrow> bool" where
  "U_test = (\<lambda>(l,\<sigma>). x l \<notin> roots \<sigma> \<union> free \<sigma>)"

definition U_body :: "('a,'i) ccom" where
  "U_body = Seq pick_x (Seq (IfThen U_test unmark_x) consid_add)"

definition Unmark :: "('a,'i) ccom" where
  "Unmark = Seq consid_reset (While consid_test U_body)"

subsection \<open>Add-to-free (Algorithm 20) and Sweep (Algorithm 19)\<close>

text \<open>Thesis: Algorithm 20, line 1, "for i \<in> Index do": cleared \<leftarrow> {}, the
  test cleared \<noteq> Index, let i \<in> (Index - cleared), and cleared \<leftarrow>
  cleared \<union> {i}.\<close>

definition cleared_reset :: "('a,'i) ccom" where
  "cleared_reset = Basic (\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l\<lparr>cleared := {}\<rparr> \<and> \<sigma>' = \<sigma>)"

definition A_test :: "('a,'i) cconf \<Rightarrow> bool" where
  "A_test = (\<lambda>(l,\<sigma>). cleared l \<noteq> UNIV)"

definition A_pick :: "('a,'i) ccom" where
  "A_pick = Basic (\<lambda>(l,\<sigma>) (l',\<sigma>'). (\<exists>j. j \<notin> cleared l \<and> l' = l\<lparr>i := j\<rparr>) \<and> \<sigma>' = \<sigma>)"

definition cleared_add :: "('a,'i) ccom" where
  "cleared_add = Basic (\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l\<lparr>cleared := cleared l \<union> {i l}\<rparr> \<and> \<sigma>' = \<sigma>)"

text \<open>Thesis: Algorithm 20, line 2: hp(x, i) \<leftarrow> null.\<close>

definition null_ptr :: "('a,'i) ccom" where
  "null_ptr = Basic (\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l \<and> \<sigma>' = \<sigma>\<lparr>hp := (hp \<sigma>)((x l, i l) := None)\<rparr>)"

text \<open>Thesis: Algorithm 20, lines 3 and 4: marked \<leftarrow> marked \<union> {x} and
  free \<leftarrow> free \<union> {x}.\<close>

definition mark_x :: "('a,'i) ccom" where
  "mark_x = Basic (\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l \<and> \<sigma>' = \<sigma>\<lparr>marked := marked \<sigma> \<union> {x l}\<rparr>)"

definition free_x :: "('a,'i) ccom" where
  "free_x = Basic (\<lambda>(l,\<sigma>) (l',\<sigma>'). l' = l \<and> \<sigma>' = \<sigma>\<lparr>free := free \<sigma> \<union> {x l}\<rparr>)"

definition A_body :: "('a,'i) ccom" where
  "A_body = Seq A_pick (Seq null_ptr cleared_add)"

text \<open>Thesis: Add-to-free(x), Algorithm 20.\<close>

definition AddToFree :: "('a,'i) ccom" where
  "AddToFree = Seq (Seq (Seq cleared_reset (While A_test A_body)) mark_x) free_x"

text \<open>Thesis: Algorithm 19, line 4: the test x \<notin> marked.\<close>

definition S_test :: "('a,'i) cconf \<Rightarrow> bool" where
  "S_test = (\<lambda>(l,\<sigma>). x l \<notin> marked \<sigma>)"

definition S_body :: "('a,'i) ccom" where
  "S_body = Seq pick_x (Seq (IfThen S_test AddToFree) consid_add)"

text \<open>Thesis: Sweep, Algorithm 19.\<close>

definition Sweep :: "('a,'i) ccom" where
  "Sweep = Seq consid_reset (While consid_test S_body)"

subsection \<open>The Collector\<close>

text \<open>Thesis: Collector \<triangleq> Unmark; Mark; Sweep (Section 4.8).\<close>

definition Collector :: "('a,'i) ccom" where
  "Collector = Seq Unmark (Seq Mark Sweep)"

section \<open>Possible values of free\<close>

text \<open>Thesis: free~ between two configurations (Section 2.3, and footnote 3 of
  Section 4.8.3): the values taken by free in the states between them,
  inclusive.  The values after the first configuration are those recorded in
  Fv since it.\<close>

definition pv :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> 'a set set" where
  "pv k0 k = insert (free (snd k0)) (set (drop (length (Fv (fst k0))) (Fv (fst k))))"

text \<open>Mechanisation only: the history recorded since k0 extends that of k0, and
  the current value of free is among the possible values.\<close>

definition hist_ok :: "('a,'i) cconf \<Rightarrow> ('a,'i) cconf \<Rightarrow> bool" where
  "hist_ok k0 k \<longleftrightarrow> (\<exists>ys. Fv (fst k) = Fv (fst k0) @ ys) \<and> free (snd k) \<in> pv k0 k"

lemma pv_pair: "pv (l0,\<sigma>0) (l,\<sigma>) = insert (free \<sigma>0) (set (drop (length (Fv l0)) (Fv l)))"
  by (simp add: pv_def)

lemma hist_ok_refl: "hist_ok k k"
  unfolding hist_ok_def pv_def by simp

text \<open>Mechanisation only: a step that records the new value of free (an
  environment step, or a program step that does not write Fv) keeps hist_ok
  and only adds possible values.\<close>

lemma hist_ok_step:
  assumes H: "hist_ok k0 (l,\<sigma>)" and F: "Fv l' = Fv l"
  shows "hist_ok k0 (hC l' \<sigma>', \<sigma>') \<and> pv k0 (l,\<sigma>) \<subseteq> pv k0 (hC l' \<sigma>', \<sigma>') \<and> free \<sigma>' \<in> pv k0 (hC l' \<sigma>', \<sigma>')"
proof -
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  from H k0 obtain ys where ys: "Fv l = Fv l0 @ ys" unfolding hist_ok_def by auto
  have Fv': "Fv (hC l' \<sigma>') = Fv l0 @ (ys @ [free \<sigma>'])" using F ys by simp
  have P1: "pv k0 (l,\<sigma>) = insert (free \<sigma>0) (set ys)" using ys k0 by (simp add: pv_def)
  have P2: "pv k0 (hC l' \<sigma>', \<sigma>') = insert (free \<sigma>0) (set ys \<union> {free \<sigma>'})" using Fv' k0 by (simp add: pv_def)
  show ?thesis using Fv' P1 P2 k0 unfolding hist_ok_def by auto
qed

lemma hist_ok_env:
  assumes "hist_ok k0 k" and "envC k k'"
  shows "hist_ok k0 k' \<and> pv k0 k \<subseteq> pv k0 k'"
proof -
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
  from assms(2) k k' have l': "l' = hC l \<sigma>'" by (simp add: rely_C_def)
  from hist_ok_step[OF assms(1)[unfolded k] refl, of \<sigma>'] show ?thesis using k k' l' by simp
qed

lemma hist_ok_trans:
  assumes "hist_ok k0 k1" and "hist_ok k1 k2"
  shows "hist_ok k0 k2 \<and> pv k0 k1 \<subseteq> pv k0 k2 \<and> pv k1 k2 \<subseteq> pv k0 k2"
proof -
  obtain l0 \<sigma>0 where k0: "k0 = (l0,\<sigma>0)" by (cases k0)
  obtain l1 \<sigma>1 where k1: "k1 = (l1,\<sigma>1)" by (cases k1)
  obtain l2 \<sigma>2 where k2: "k2 = (l2,\<sigma>2)" by (cases k2)
  from assms(1) k0 k1 obtain ys1 where y1: "Fv l1 = Fv l0 @ ys1"
    and f1: "free \<sigma>1 \<in> insert (free \<sigma>0) (set ys1)" unfolding hist_ok_def pv_def by auto
  from assms(2) k1 k2 obtain ys2 where y2: "Fv l2 = Fv l1 @ ys2"
    and f2: "free \<sigma>2 \<in> insert (free \<sigma>1) (set ys2)" unfolding hist_ok_def pv_def by auto
  have y: "Fv l2 = Fv l0 @ (ys1 @ ys2)" using y1 y2 by simp
  have P01: "pv k0 k1 = insert (free \<sigma>0) (set ys1)" using y1 k0 k1 by (simp add: pv_def)
  have P12: "pv k1 k2 = insert (free \<sigma>1) (set ys2)" using y2 k1 k2 by (simp add: pv_def)
  have P02: "pv k0 k2 = insert (free \<sigma>0) (set ys1 \<union> set ys2)" using y k0 k2 by (simp add: pv_def)
  show ?thesis using y f1 f2 P01 P12 P02 k0 k2 unfolding hist_ok_def by auto
qed

text \<open>Mechanisation only: interference before the start only adds possible
  values.\<close>

lemma hist_ok_env_left:
  assumes "envC k0 k0'" and "hist_ok k0' k"
  shows "hist_ok k0 k \<and> pv k0' k \<subseteq> pv k0 k"
proof -
  have "hist_ok k0 k0'" using hist_ok_env[OF hist_ok_refl assms(1)] by blast
  from hist_ok_trans[OF this assms(2)] show ?thesis by blast
qed

section \<open>Interference seen by the Collector\<close>

text \<open>Mechanisation only: what an environment step (or a step that leaves the
  shared state unchanged) does, from rely-Collector (Section 4.5.4).\<close>

lemma envs_marked: "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma> \<Longrightarrow> marked \<sigma> \<subseteq> marked \<sigma>'"
  unfolding env_step_def using rely_marked_mono by blast

lemma envs_roots: "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma> \<Longrightarrow> roots \<sigma>' = roots \<sigma>"
  unfolding env_step_def using rely_roots by blast

lemma envs_free: "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma> \<Longrightarrow> free \<sigma>' \<subseteq> free \<sigma>"
  unfolding env_step_def using rely_free_anti by blast

lemma envs_garbage: "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma> \<Longrightarrow> garbage \<sigma> \<subseteq> garbage \<sigma>'"
  unfolding env_step_def using rely_garbage_mono by blast

lemma envs_inv_state: "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma> \<Longrightarrow> inv_state \<sigma> \<Longrightarrow> inv_state \<sigma>'"
  unfolding env_step_def by blast

lemma envs_new_marks: "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma> \<Longrightarrow> marked \<sigma>' - marked \<sigma> \<subseteq> reach (roots \<sigma>) (hp \<sigma>)"
  unfolding env_step_def rely_Collector_def by auto

text \<open>Mechanisation only: interference never marks garbage.\<close>

lemma envs_garbage_unmarked:
  assumes E: "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>" and G: "y \<in> garbage \<sigma>" and M: "y \<notin> marked \<sigma>"
  shows "y \<notin> marked \<sigma>'"
  using envs_new_marks[OF E] G M unfolding garbage_def by blast

text \<open>Thesis: Lemma 2 (an environment step preserves invB).\<close>

lemma envs_invB:
  fixes \<sigma> \<sigma>' :: "('a::finite,'i::finite) state"
  assumes "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>" and "invB S \<sigma>"
  shows "invB S \<sigma>'"
  using assms lemma2_env_invB by blast

text \<open>Mechanisation only: conjunct (4.1) of rely-Collector: pointers out of
  garbage do not change.\<close>

lemma envs_garbage_edges:
  assumes "env_step S \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>" and "y \<in> garbage \<sigma>"
  shows "hp \<sigma>' (y,j) = hp \<sigma> (y,j)"
  using assms unfolding env_step_def rely_Collector_def by fastforce

text \<open>Mechanisation only: the same facts for an environment step alone.\<close>

lemmas env_marked = envs_marked[OF disjI1]

lemmas env_roots = envs_roots[OF disjI1]

lemmas env_free = envs_free[OF disjI1]

lemmas env_garbage = envs_garbage[OF disjI1]

lemmas env_inv_state = envs_inv_state[OF disjI1]

lemmas env_new_marks = envs_new_marks[OF disjI1]

lemmas env_garbage_unmarked = envs_garbage_unmarked[OF disjI1]

lemmas env_invB = envs_invB[OF disjI1]

lemmas env_garbage_edges = envs_garbage_edges[OF disjI1]

text \<open>Mechanisation only: interference changes only the Collector's history
  variable, so over any number of environment steps the other private
  variables keep their values.\<close>

lemma envC_star_locals:
  assumes "envC\<^sup>*\<^sup>* k0 k"
  shows "\<exists>F. fst k = (fst k0)\<lparr>Fv := F\<rparr>"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  have "fst k0 = (fst k0)\<lparr>Fv := Fv (fst k0)\<rparr>" by simp
  then show ?case by blast
next
  case (step y z)
  obtain ly \<sigma>y where y: "y = (ly,\<sigma>y)" by (cases y)
  obtain lz \<sigma>z where z: "z = (lz,\<sigma>z)" by (cases z)
  from step.hyps(2) y z have lz: "lz = hC ly \<sigma>z" by (simp add: rely_C_def)
  from step.IH y obtain F where F: "ly = (fst k0)\<lparr>Fv := F\<rparr>" by auto
  have "lz = (fst k0)\<lparr>Fv := F @ [free \<sigma>z]\<rparr>" using lz F by (simp add: hC_def)
  then show ?case using z by auto
qed

lemma envC_star_sel:
  assumes "envC\<^sup>*\<^sup>* (l0,\<sigma>0) (l,\<sigma>)"
  shows "consid l = consid l0" "checked l = checked l0" "mc l = mc l0" "s l = s l0"
    "x l = x l0" "i l = i l0" "cleared l = cleared l0"
proof -
  obtain F where L: "l = l0\<lparr>Fv := F\<rparr>" using envC_star_locals[OF assms] by auto
  show "consid l = consid l0" using L by simp
  show "checked l = checked l0" using L by simp
  show "mc l = mc l0" using L by simp
  show "s l = s l0" using L by simp
  show "x l = x l0" using L by simp
  show "i l = i l0" using L by simp
  show "cleared l = cleared l0" using L by simp
qed

text \<open>Mechanisation only: the rules of RG_VDM specialised to the Collector:
  stability and tolerance stated for one environment step of rely-Collector,
  and the rule for an atomic statement stated on explicit pairs.\<close>

lemma stableC:
  assumes "\<And>l \<sigma> \<sigma>'. P (l,\<sigma>) \<Longrightarrow> env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma> \<Longrightarrow> P (hC l \<sigma>', \<sigma>')"
  shows "stable hC (rely_C s) P"
proof (rule stableI)
  fix l \<sigma> \<sigma>' assume "P (l,\<sigma>)" and "rely_C s l \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  then show "P (hC l \<sigma>', \<sigma>')" using assms unfolding rely_C_def by blast
qed

lemma toleratesC:
  assumes R: "\<And>k0 l \<sigma> \<sigma>'. Q k0 (l,\<sigma>) \<Longrightarrow> env_step (s l) \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma> \<Longrightarrow> Q k0 (hC l \<sigma>', \<sigma>')"
    and L: "\<And>l0 \<sigma>0 \<sigma>0' k. I (l0,\<sigma>0) \<Longrightarrow> env_step (s l0) \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0 \<Longrightarrow>
              Q (hC l0 \<sigma>0', \<sigma>0') k \<Longrightarrow> Q (l0,\<sigma>0) k"
  shows "tolerates hC (rely_C s) I Q"
proof (rule toleratesI)
  fix k0 l \<sigma> \<sigma>' assume "Q k0 (l,\<sigma>)" and "rely_C s l \<sigma> \<sigma>' \<or> \<sigma>' = \<sigma>"
  then show "Q k0 (hC l \<sigma>', \<sigma>')" using R unfolding rely_C_def by blast
next
  fix l0 \<sigma>0 \<sigma>0' k assume "I (l0,\<sigma>0)" and "rely_C s l0 \<sigma>0 \<sigma>0' \<or> \<sigma>0' = \<sigma>0" and "Q (hC l0 \<sigma>0', \<sigma>0') k"
  then show "Q (l0,\<sigma>0) k" using L unfolding rely_C_def by blast
qed

lemma rule_basicC:
  assumes PS: "stable hC (rely_C s) P" and QT: "tolerates hC (rely_C s) P Q"
    and S: "\<And>l \<sigma> l' \<sigma>'. P (l,\<sigma>) \<Longrightarrow> r (l,\<sigma>) (l',\<sigma>') \<Longrightarrow> G (l,\<sigma>) (l',\<sigma>') \<and> Q (l,\<sigma>) (hC l' \<sigma>', \<sigma>')"
  shows "coll_sat P (Basic r) G Q"
proof (rule rule_basic[OF PS QT])
  fix k k' assume P: "P k" and r: "r k k'"
  obtain l \<sigma> where k: "k = (l,\<sigma>)" by (cases k)
  obtain l' \<sigma>' where k': "k' = (l',\<sigma>')" by (cases k')
  from S[OF P[unfolded k] r[unfolded k k']] show "G k k' \<and> Q k (hupd hC k')" using k k' by simp
qed

text \<open>Mechanisation only: over interference alone (the else branch of an
  "if" that does nothing), the private variables other than Fv keep their
  values and hist_ok holds.\<close>

lemma envC_star_hist:
  assumes "envC\<^sup>*\<^sup>* k0 k"
  shows "hist_ok k0 k"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  show ?case by (rule hist_ok_refl)
next
  case (step y z)
  from hist_ok_env[OF step.IH step.hyps(2)] show ?case by blast
qed

end
