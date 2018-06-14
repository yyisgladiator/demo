theory USpec_Comp
  imports USpec  "inc/CPOFix"
begin

(****************************************************)
section\<open>Definitions\<close>
(****************************************************)   
  

(* from here on only lemma on composition *)
default_sort ufuncl_comp

(* General Composition  *)
definition uspec_compwell :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspec_compwell S1 S2 \<equiv> \<forall> f1 \<in> (Rep_rev_uspec S1). \<forall> f2 \<in> (Rep_rev_uspec S2). ufunclCompWell f1 f2"

abbreviation uspecCompDom:: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> channel set" where
"uspecCompDom S1 S2 \<equiv> (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2) - (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2)"

abbreviation uspecRanUnion:: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> channel set" where
"uspecRanUnion S1 S2 \<equiv> uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2"

abbreviation uspecDomUnion:: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> channel set" where
"uspecDomUnion S1 S2 \<equiv> uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2"

definition uspecComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<Otimes>" 50) where
"uspecComp S1 S2 \<equiv> 
let Comp_set = {f1 \<otimes> f2 | f1 f2. f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)};
    Cin = (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2) - (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2);
    Cout = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2
in Abs_rev_uspec Comp_set Cin Cout"

(* Parallel Composition *)
definition uspec_parcompwell :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspec_parcompwell S1 S2 \<equiv> \<forall> f1 \<in> (Rep_rev_uspec S1). \<forall> f2 \<in> (Rep_rev_uspec S2). ufunclParCompWell f1 f2"  

definition uspecParComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<parallel>" 50) where
"uspecParComp S1 S2 \<equiv>
let Comp_set = {f1 \<parallel> f2 | f1 f2.  f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)};
    Cin = (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2);
    Cout = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2
in Abs_rev_uspec Comp_set Cin Cout"
(* Serial Composition *)
definition uspec_sercompwell :: "'m uspec \<Rightarrow> 'm uspec \<Rightarrow> bool" where
"uspec_sercompwell S1 S2 \<equiv> \<forall> f1 \<in> (Rep_rev_uspec S1). \<forall> f2 \<in> (Rep_rev_uspec S2). ufunclSerCompWell f1 f2"

definition uspecSerComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<circle>" 50) where
"uspecSerComp S1 S2 \<equiv>
let Comp_set = {f1 \<circ> f2 | f1 f2.  f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)};
    Cin = uspecDom\<cdot>S1;
    Cout = uspecRan\<cdot>S2
in Abs_rev_uspec Comp_set Cin Cout"

(* Feedback Composition *)
definition uspecFeedbackComp :: "'m uspec \<Rightarrow> 'm uspec" where
"uspecFeedbackComp S1 \<equiv> 
let Comp_set = {ufunclFeedbackComp f1 | f1.  f1\<in>(Rep_rev_uspec S1)};
    Cin = uspecDom\<cdot>S1 - uspecRan\<cdot>S1;
    Cout = uspecRan\<cdot>S1
in Abs_rev_uspec Comp_set Cin Cout"


(* Smallest possible USpec: Smallest means "least specified", i.e. ALL ufuns with I/O property *)
definition uspecLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> 'm uspec" where
"uspecLeast cin cout = Abs_rev_uspec {f. ufclDom\<cdot>f = cin \<and> ufclRan\<cdot>f = cout} cin cout"

definition uspecFix ::"channel set \<Rightarrow> channel set \<Rightarrow> ('a uspec \<rightarrow> 'a uspec) \<rightarrow> 'a uspec" where
"uspecFix cin cout \<equiv> (\<Lambda> F.  fixg (uspecLeast cin cout)\<cdot>F)"

definition uspecImage::  "('m \<Rightarrow> 'n) \<Rightarrow> 'm uspec \<Rightarrow> 'n uspec" where
"uspecImage f \<equiv>  \<lambda> S.
Abs_uspec ((setrevImage f (uspecRevSet\<cdot>S)), 
  Discr (ufclDom\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))),
  Discr (ufclRan\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))))"

(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)   

subsection \<open>uspecLeast\<close>

lemma uspecLeast_well[simp]: "uspecWell (Rev {f. ufclDom\<cdot>f = cin \<and> ufclRan\<cdot>f = cout}) (Discr cin) (Discr cout)"
  by auto

lemma uspecLeast_contains_ufLeast: "ufunclLeast cin cout \<in> Rep_rev_uspec(uspecLeast cin cout)"
  by (simp add: inv_rev_rev ufuncldom_least_dom ufuncldom_least_ran uspecLeast_def)

lemma uspecLeast_consistent: "uspecIsConsistent (uspecLeast cin cout)"
  using not_uspec_consisten_empty_eq uspecLeast_contains_ufLeast by auto    

lemma uspecLeast_dom: "uspecDom\<cdot>(uspecLeast cin cout) = cin"
  by (simp add: uspecLeast_def uspecdom_insert)

lemma uspecLeast_ran: "uspecRan\<cdot>(uspecLeast cin cout) = cout"
  by (simp add: uspecLeast_def uspecran_insert)

lemma uspecLeast_min: assumes "uspecDom\<cdot>S = In"
                          and "uspecRan\<cdot>S = Out"
                        shows "uspecLeast In Out \<sqsubseteq> S"
  proof -
    have "\<And>f. f \<in> (Rep_rev_uspec S) \<Longrightarrow> ufclDom\<cdot>f = In \<and> ufclRan\<cdot>f = Out"
      by (simp add: assms rep_rev_revset uspec_allDom uspec_allRan)
    moreover have "\<And>f. ufclDom\<cdot>f = In \<and> ufclRan\<cdot>f = Out \<Longrightarrow> f \<in> Rep_rev_uspec (uspecLeast In Out)"
      by (metis (mono_tags, lifting) CollectI rep_abs_rev_simp uspecLeast_def uspecLeast_well)
    ultimately have "\<And>f. f \<in> (Rep_rev_uspec S) \<Longrightarrow> f \<in> Rep_rev_uspec (uspecLeast In Out)"
      by auto
    then have "Rep_rev_uspec S \<subseteq> Rep_rev_uspec (uspecLeast In Out)"
      by(simp add: subsetI)
    then show ?thesis
      by (simp add: assms revBelowNeqSubset uspecLeast_dom uspecLeast_ran uspec_belowI uspecrevset_insert)
  qed

lemma uspecLeast_min2: "(uspecLeast (uspecDom\<cdot>S) (uspecRan\<cdot>S)) \<sqsubseteq> S"
  using uspecLeast_min by auto

lemma uspecLeast_union: "uspecUnion\<cdot>f\<cdot>(uspecLeast (uspecDom\<cdot>f) (uspecRan\<cdot>f)) = (uspecLeast (uspecDom\<cdot>f) (uspecRan\<cdot>f))"
  apply(rule uspec_eqI2)
  apply(rule setrev_eqI)
  apply(rule set_eqI)
  apply auto
  apply(metis (mono_tags, lifting) CollectI rep_abs_rev_simp uspecLeast_def uspecLeast_well uspecUnion_setrev_condition uspec_allDom uspec_allRan uspecrevset_insert)
  apply(simp add: uspecLeast_dom uspecLeast_ran uspecUnion_setrev_condition uspec_allDom uspec_allRan)
  by (simp add: uspecLeast_consistent uspecLeast_dom uspecLeast_ran uspecUnion_consistent2)

lemma uspecLeast_union_consistent: "uspecIsConsistent(uspecUnion\<cdot>f\<cdot>(uspecLeast (uspecDom\<cdot>f) (uspecRan\<cdot>f)))"
  by(simp add: uspecLeast_union uspecLeast_consistent)

subsection \<open>uspecFix\<close>

abbreviation uspec_io_eq :: "('m uspec \<rightarrow> 'm uspec) \<Rightarrow> channel set \<Rightarrow> channel set \<Rightarrow> bool" where
"uspec_io_eq F cin cout \<equiv> uspecDom\<cdot>(F\<cdot>(uspecLeast cin cout)) = cin \<and> 
                          uspecRan\<cdot>(F\<cdot>(uspecLeast cin cout)) = cout"


lemma uspecfix_insert: "uspecFix cin cout\<cdot>F = fixg (uspecLeast cin cout)\<cdot>F"
  by (simp add: uspecFix_def)


lemma uspecfix_insert2: assumes "uspec_io_eq F cin cout" 
  shows "uspecFix cin cout\<cdot>F = (\<Squnion>i::nat. iterate i\<cdot>F\<cdot>(uspecLeast cin cout))"
  apply (simp add: uspecFix_def fixg_def)
  apply (subst Abs_cfun_inverse2)
   apply (rule fixg_cont)
   apply (metis (no_types, lifting) uspecLeast_dom uspecLeast_min uspecLeast_ran uspecdom_eq uspecran_eq)
  by (simp add: assms uspecLeast_min)

lemma uspecfix_mono: "monofun (\<lambda> F.  fixg (uspecLeast cin cout)\<cdot>F)"
  by (simp add: monofun_Rep_cfun2)

lemma uspecfix_cont[simp]: "cont (\<lambda> F.  fixg (uspecLeast cin cout)\<cdot>F)"
  by simp

lemma uspecfix_eq: assumes "uspec_io_eq F cin cout"
  shows "uspecFix cin cout\<cdot>F =  F\<cdot>(uspecFix cin cout\<cdot>F)"
  apply (simp add: uspecfix_insert)
  apply (rule fixg_fix)
   apply (simp add: assms uspecLeast_min)
  by (metis (no_types, hide_lams) uspecLeast_dom uspecLeast_min2 uspecLeast_ran uspecdom_eq uspecran_eq)

lemma uspecfix_least_below: assumes "uspec_io_eq F cin cout" and "uspecDom\<cdot>x = cin" and "uspecRan\<cdot>x = cout"
  shows "F\<cdot>x \<sqsubseteq> x \<Longrightarrow> (uspecFix cin cout\<cdot>F) \<sqsubseteq> x"
  apply (simp add: uspecFix_def)
  apply (rule fixg_least_below)
     apply (simp add: assms(1) uspecLeast_min)
    apply (metis (no_types, hide_lams) uspecLeast_dom uspecLeast_min uspecLeast_ran uspecdom_eq uspecran_eq)
   apply (simp add: assms(2) assms(3) uspecLeast_min)
  by simp

lemma uspecfix_least: assumes "uspec_io_eq F cin cout" and "uspecDom\<cdot>x = cin" and "uspecRan\<cdot>x = cout"
                    and "F\<cdot>x = x"
                  shows "(uspecFix cin cout\<cdot>F) \<sqsubseteq> x"
  by (simp add: assms(1) assms(2) assms(3) assms(4) uspecfix_least_below)

lemma uspecfix_eqI: 
  assumes fp: "F\<cdot>x = x" and
    lst: "\<And>z. uspecDom\<cdot>z = cin \<and> uspecRan\<cdot>z=cout \<Longrightarrow> F\<cdot>z = z \<Longrightarrow> x \<sqsubseteq> z"
    and "uspec_io_eq F cin cout" and "uspecDom\<cdot>x = cin" and "uspecRan\<cdot>x = cout"
  shows "(uspecFix cin cout\<cdot>F) = x"
proof -
  have f1: "\<And>c u. c\<cdot>(u::'a uspec) \<notsqsubseteq> u \<or> 
    uspecRan\<cdot> (c\<cdot>(uspecLeast (uspecDom\<cdot>u) (uspecRan\<cdot>u))) \<noteq> uspecRan\<cdot>u \<or> 
    uspecDom\<cdot> (c\<cdot>(uspecLeast (uspecDom\<cdot>u) (uspecRan\<cdot>u))) \<noteq> uspecDom\<cdot>u \<or> 
    Abs_cfun (Rep_cfun (fixg (uspecLeast (uspecDom\<cdot>u) (uspecRan\<cdot>u))))\<cdot> c \<sqsubseteq> u"
    by (metis uspecFix_def uspecfix_least_below)
  then have f2: "Abs_cfun (Rep_cfun (fixg (uspecLeast cin cout)))\<cdot>F \<sqsubseteq> x"
using assms(3) assms(4) assms(5) fp po_eq_conv by blast
  then have "uspecDom\<cdot>(Abs_cfun (Rep_cfun (fixg (uspecLeast cin cout)))\<cdot>F) = cin"
    using assms(4) by auto
  then have "x \<sqsubseteq> Abs_cfun (Rep_cfun (fixg (uspecLeast cin cout)))\<cdot>F"
using f2 by (metis assms(3) assms(5) lst uspecFix_def uspecfix_eq uspecran_eq)
  then show ?thesis
    using f1 by (metis (no_types) assms(3) assms(4) assms(5) fp po_eq_conv uspecFix_def)
qed

lemma uspecfix_least_iff: assumes "uspec_io_eq F cin cout"
  shows "((uspecFix cin cout\<cdot>F) = uspecLeast cin cout) = 
            (F\<cdot>(uspecLeast cin cout) = uspecLeast cin cout)"
  by (metis assms uspecLeast_min uspecfix_eq uspecfix_eqI)

lemma uspecfix_strict: assumes "uspec_io_eq F cin cout" and "F\<cdot>(uspecLeast cin cout) = (uspecLeast cin cout)"
  shows "(uspecFix cin cout\<cdot>F) = uspecLeast cin cout"
  using assms(1) assms(2) uspecfix_least_iff by blast

lemma uspecfix_defined: assumes "uspec_io_eq F cin cout" 
  and "F\<cdot>(uspecLeast cin cout) \<noteq> (uspecLeast cin cout)"
  shows "(uspecFix cin cout\<cdot>F) \<noteq> uspecLeast cin cout"
  by (simp add: assms(1) assms(2) uspecfix_least_iff)

lemma uspecfix_id: "(uspecFix cin cout\<cdot>(\<Lambda> x. x)) = (uspecLeast cin cout)"
  by (simp add: uspecLeast_dom uspecLeast_ran uspecfix_least_iff)

lemma uspecfix_const: assumes "uspecDom\<cdot>c = cin" and "uspecRan\<cdot>c = cout"
  shows "(uspecFix cin cout\<cdot>(\<Lambda> x. c)) = c"
  apply (rule uspecfix_eqI)
  by (simp add: assms(1) assms(2)) +

lemma uspec_iterate_chain: assumes "uspec_io_eq F cin cout"
  shows "chain (\<lambda>i. iterate i\<cdot>F\<cdot>(uspecLeast cin cout))"
  apply (rule chainI, subst iterate_Suc2)
  apply(rule Cfun.monofun_cfun_arg)
  by (simp add: assms uspecLeast_min)

lemma iter_uspecfix_dom: assumes "uspec_io_eq F cin cout" 
  shows "uspecDom\<cdot>( iterate i\<cdot>F\<cdot>(uspecLeast cin cout)) = cin"
  apply (induction i)
   apply (simp add: uspecLeast_dom)
  by (metis (mono_tags, lifting) assms po_class.chain_def uspec_iterate_chain uspecdom_eq)

lemma iter_upecfix_ran: assumes "uspec_io_eq F cin cout" 
  shows "uspecRan\<cdot>( iterate i\<cdot>F\<cdot>(uspecLeast cin cout)) = cout"
  apply (induction i)
   apply (simp add: uspecLeast_dom)
   apply (simp add: uspecLeast_ran)
  by (metis (mono_tags, lifting) assms po_class.chain_def uspec_iterate_chain uspecran_eq)

lemma uspecfix_ind: assumes "uspec_io_eq F cin cout" 
                  and "adm P" and "P (uspecLeast cin cout)"
                  and "\<And> x. \<lbrakk>uspecDom\<cdot>x = cin; uspecRan\<cdot>x = cout; P x\<rbrakk> \<Longrightarrow> P (F\<cdot>x)"
                shows "P (uspecFix cin cout\<cdot>F)"
  apply (simp add: assms(1) uspecfix_insert2)
  apply (subst admD, simp_all add: assms)
   apply (metis assms(1) iter_fixg_chain uspecLeast_min2)
  apply (rule nat_induct)
   apply (simp add: assms(3)) +
  by (simp add: assms(1) assms(4) iter_upecfix_ran iter_uspecfix_dom)


lemma cont_uspecfix_ind: assumes "cont F" and  "uspec_io_eq (Abs_cfun F) cin cout" 
                  and "adm P" and "P (uspecLeast cin cout)"
                  and "\<And> x. \<lbrakk>uspecDom\<cdot>x = cin; uspecRan\<cdot>x = cout; P x\<rbrakk> \<Longrightarrow> P (F x)"
                shows "P (uspecFix cin cout\<cdot>(Abs_cfun F))"
  by (metis Abs_cfun_inverse2 assms(1) assms(2) assms(3) assms(4) assms(5) uspecfix_ind)

lemma uspecfix_ind2:  assumes "uspec_io_eq F cin cout" 
                  and "adm P" and s0:"P (uspecLeast cin cout)" and s1: "P (F\<cdot>(uspecLeast cin cout))"
                    and s2: "\<And> x. \<lbrakk>uspecDom\<cdot>x = cin; uspecRan\<cdot>x = cout; P x; P (F\<cdot>x)\<rbrakk> \<Longrightarrow> P (F\<cdot>(F\<cdot>x))"
                  shows "P (uspecFix cin cout\<cdot>F)"
  apply (simp add: assms(1) uspecfix_insert2)
  apply (subst admD, simp_all add: assms)
   apply (simp add: assms(1) uspec_iterate_chain)
  apply (rule nat_less_induct)
  apply (case_tac n)
   apply (simp add: s0)
  apply (case_tac nat)
   apply (simp add: s1)
  apply (frule_tac x=nat in spec)
  by (simp add: assms(1) iter_upecfix_ran iter_uspecfix_dom s2)

subsection \<open>UspecComp\<close>

(*   *)
lemma uspec_compwell_commu: "uspec_compwell S1 S2 =  uspec_compwell S2 S1"
  using ufunclCompWell_commute uspec_compwell_def by blast

lemma uspec_compwell2ufunclcompwell: assumes "uspec_compwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. ufunclCompWell f1 f2"
  using assms uspec_compwell_def by blast

lemma uspec_comp_well[simp]: assumes "uspec_compwell S1 S2"
  shows "uspecWell (Rev {f1 \<otimes> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2})
              (Discr (uspecCompDom S1 S2)) (Discr (uspecRanUnion S1 S2))"
  apply (rule uspec_wellI)
   apply (smt CollectD assms ufuncl_comp_dom uspec_allDom uspec_allRan uspec_compwell2ufunclcompwell uspecrevset_insert)
  by (smt CollectD assms ufuncl_comp_ran uspec_allRan uspec_compwell2ufunclcompwell uspecrevset_insert)

(*   *)
lemma uspec_comp_commu: assumes "uspec_compwell S1 S2"
  shows "(S1 \<Otimes> S2) = (S2 \<Otimes> S1)"
proof - 
  have "{f1 \<otimes> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} = 
             {f1 \<otimes> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S2 \<and> f2 \<in> Rep_rev_uspec S1}" (is "?L = ?R")
    apply auto
    using  assms comp_commute uspec_compwell_def by metis +
  then show ?thesis
    unfolding uspecComp_def apply simp
    apply (rule uspec_eqI)
    by (simp add: sup_commute) +
qed


lemma uspec_comp_rep[simp]: assumes "uspec_compwell S1 S2"
shows "{f1 \<otimes> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} 
          = Rep_rev_uspec (S1 \<Otimes> S2)"
  apply (simp add: uspecComp_def)
  using assms(1) rep_abs_rev_simp uspec_comp_well by blast

lemma uspec_comp_ele_ex: assumes "uspec_compwell S1 S2"
and "uspecIsConsistent (S1 \<Otimes> S2)"
shows "\<forall> f \<in> Rep_rev_uspec (S1 \<Otimes> S2). \<exists> f1 \<in> Rep_rev_uspec S1. \<exists> f2 \<in> Rep_rev_uspec S2. f = f1 \<otimes> f2"
  using assms uspec_comp_rep by fastforce

lemma uspec_comp_not_empty:  assumes "uspec_compwell S1 S2"
"f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
shows "(f1 \<otimes> f2) \<in> Rep_rev_uspec (S1 \<Otimes> S2)"
  by (metis (mono_tags, lifting) assms(1) assms(2) f2_def mem_Collect_eq rep_abs_rev_simp uspecComp_def uspec_comp_well)

lemma uspec_comp_consistent2: assumes "uspecIsConsistent (S1 \<Otimes> S2)"
  shows "uspecIsConsistent S1 \<and> uspecIsConsistent S2"
  by (metis assms emptyE not_uspec_consisten_empty_eq uspec_comp_ele_ex uspec_compwell_def uspec_consist_f_ex)

lemma uspec_comp_dom: assumes "uspec_compwell S1 S2"
shows "uspecDom\<cdot>(S1 \<Otimes> S2) = (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2) - (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2)" (*UFun_Comp \<rightarrow> dom*)
  apply (simp add: uspecComp_def)
  apply (subst uspecdom_insert)
  apply (simp only: uspec_comp_well assms rep_abs_uspec)
  by simp

subsection \<open>UspecParComp\<close>

(*   *)
lemma uspec_parcompwell_commu: "uspec_parcompwell S1 S2 = uspec_parcompwell S2 S1"
  using ufunclParCompWell_commute uspec_parcompwell_def by blast

lemma uspec_parcompwell2ufunclparcompwell: assumes "uspec_parcompwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. ufunclParCompWell f1 f2"
  using assms uspec_parcompwell_def by auto

(*   *)
lemma uspec_parcomp_well[simp]: assumes "uspec_parcompwell S1 S2"
  shows "uspecWell (Rev {f1 \<parallel> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2})
              (Discr (uspecDomUnion S1 S2)) (Discr (uspecRanUnion S1 S2))"
  apply (rule uspec_wellI)
   apply (smt CollectD assms ufuncl_parcomp_dom uspec_allDom uspec_parcompwell2ufunclparcompwell uspecrevset_insert) 
  by (smt CollectD assms ufuncl_parcomp_ran uspec_allRan uspec_parcompwell2ufunclparcompwell uspecrevset_insert)

(*   *)
lemma uspec_parcomp_rep[simp]: assumes "uspec_parcompwell S1 S2"
shows "{f1 \<parallel> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} 
          = Rep_rev_uspec (S1 \<parallel> S2)"
  apply (simp add: uspecParComp_def)
  using assms(1) rep_abs_rev_simp uspec_parcomp_well by blast

(*   *)
lemma uspec_parcomp_not_empty:  assumes "uspec_parcompwell S1 S2"
"f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
shows "(f1 \<parallel> f2) \<in> Rep_rev_uspec (S1 \<parallel> S2)"
  by (metis (mono_tags, lifting) assms(1) assms(2) f2_def mem_Collect_eq rep_abs_rev_simp 
      uspecParComp_def uspec_parcomp_well)

(*   *)
lemma uspec_parcomp_consistent: assumes "uspec_parcompwell S1 S2"
  and "uspecIsConsistent S1" and "uspecIsConsistent S2"
shows "uspecIsConsistent (S1 \<parallel> S2)"
  by (metis assms(1) assms(2) assms(3) emptyE some_in_eq uspecIsConsistent_def uspec_parcomp_not_empty)

(*   *)
lemma uspec_parcomp_consistent2: assumes "uspec_parcompwell S1 S2" and "uspecIsConsistent (S1 \<parallel> S2)"
  shows "uspecIsConsistent S1 \<and> uspecIsConsistent S2"
proof (rule)
  have f1: "{a \<parallel> aa |a aa. a \<in> Rep_rev_uspec S1 \<and> aa \<in> Rep_rev_uspec S2} \<noteq> {}"
    using assms(1) assms(2) uspecIsConsistent_def by auto
  then have "Rep_rev_uspec S1 \<noteq> {}"
    by blast
  then show "uspecIsConsistent S1"
    by (meson uspecIsConsistent_def)
  have "Rep_rev_uspec S2 \<noteq> {}"
    using f1 by blast
  then show "uspecIsConsistent S2"
    by (meson uspecIsConsistent_def)
qed

(*   *)
lemma uspec_parcomp_dom: assumes "uspec_parcompwell S1 S2"
  shows "uspecDom\<cdot>(S1 \<parallel> S2) = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2"
  apply (simp add: uspecParComp_def)
  apply (subst uspecdom_insert)
  apply (simp only: uspec_parcomp_well assms rep_abs_uspec)
  by simp

(*   *)
lemma uspec_parcomp_ran: assumes "uspec_parcompwell S1 S2"
  shows "uspecRan\<cdot>(S1 \<parallel> S2) = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2"
  apply (simp add: uspecParComp_def)
  apply (subst uspecran_insert)
  apply (simp only: uspec_parcomp_well assms rep_abs_uspec)
  by simp

lemma uspec_parcomp_h1: assumes "uspec_parcompwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. f1 \<parallel> f2 \<in> Rep_rev_uspec (S1 \<parallel> S2)"
  by (simp add: assms uspec_parcomp_not_empty)

lemma uspec_parcomp_h2: assumes "uspec_parcompwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. ufunclParCompWell f1 f2"
  using assms uspec_parcompwell_def by auto

(* if the composition of 2 uspecs is consistent then those uspecs are consistent themselves  *)
lemma uspec_parcomp_ele_ex: assumes "uspec_parcompwell S1 S2"
shows "\<forall> f \<in> Rep_rev_uspec (S1 \<parallel> S2). \<exists> f1 \<in> Rep_rev_uspec S1. \<exists> f2 \<in> Rep_rev_uspec S2. f = f1 \<parallel> f2"
  using assms(1) uspec_parcomp_rep by fastforce

(* uspec parcomp is commutative  *)
lemma uspec_parcomp_commu: assumes "uspec_parcompwell S1 S2"
  shows "(uspecParComp S1 S2) = (uspecParComp S2 S1)"
proof -
  have f1: "{f1 \<parallel> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} = 
                {f1 \<parallel> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S2 \<and> f2 \<in> Rep_rev_uspec S1}" (is "?L = ?R")
    apply auto
    using assms parcomp_commute uspec_parcompwell_def by metis +
  show ?thesis
    apply (rule uspec_eqI)
      apply (simp add: uspecParComp_def)
      apply (simp add: f1 sup_commute) 
     apply (simp add: assms sup_commute uspec_parcomp_dom uspec_parcompwell_commu) 
    by (simp add: assms sup_commute uspec_parcomp_ran uspec_parcompwell_commu)
qed

(* uspec parcomp is associative  *)
lemma uspec_parcomp_asso: assumes "uspec_parcompwell S1 S2"
and "uspec_parcompwell S1 S3"
and "uspec_parcompwell S2 S3"
shows "uspecParComp (uspecParComp S1 S2) S3 = uspecParComp S1 (uspecParComp S2 S3)"
proof -
  have f0: "uspec_parcompwell (S1 \<parallel> S2) S3"
    apply (simp add: uspec_parcompwell_def, auto)
    by (metis (no_types, hide_lams) assms(1) assms(2) assms(3) parcompwell_asso ufunclParCompWell_commute 
        uspec_parcomp_ele_ex uspec_parcompwell2ufunclparcompwell uspec_parcompwell_def)
  have f1: "uspec_parcompwell S1 (S2 \<parallel> S3)"
    apply (simp add: uspec_parcompwell_def, auto)
    by (metis assms(1) assms(2) assms(3) parcompwell_asso uspec_parcomp_ele_ex uspec_parcompwell2ufunclparcompwell)
  have f2: "uspecRevSet\<cdot>((S1 \<parallel> S2) \<parallel> S3) = 
      Rev {f1 \<parallel> f2 |f1 f2. f1 \<in> Rep_rev_uspec (S1 \<parallel> S2) \<and> f2 \<in> Rep_rev_uspec S3}"
    apply (simp add: uspecrevset_insert)
    apply (subst uspec_parcomp_rep)
     apply (smt assms(1) assms(2) assms(3) parcompwell_asso ufunclParCompWell_commute uspec_parcomp_ele_ex uspec_parcompwell2ufunclparcompwell uspec_parcompwell_def)
    by (simp add: rev_inv_rev)
  have f3: "uspecRevSet\<cdot>(S1 \<parallel> (S2 \<parallel> S3)) = 
      Rev {f1 \<parallel> f2 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec (S2 \<parallel> S3)}"
    apply (simp add: uspecrevset_insert)
    apply (simp add: f1)
    by (simp add: rev_inv_rev)
  have f10: "{f1 \<parallel> f2 |f1 f2. f1 \<in> Rep_rev_uspec (S1 \<parallel> S2) \<and> f2 \<in> Rep_rev_uspec S3} =
               {f1 \<parallel> f2 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec (S2 \<parallel> S3)}"
  proof (auto)
    show "\<And>(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec (S1 \<parallel> S2) \<Longrightarrow> f2 \<in> Rep_rev_uspec S3 \<Longrightarrow> \<exists>(f1a::'a) f2a::'a. f1 \<parallel> f2 = f1a \<parallel> f2a \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec (S2 \<parallel> S3)"
    proof -
      fix f1::'a and f2::'a
      assume f1_def: "f1 \<in> Rep_rev_uspec (S1 \<parallel> S2)" and f2_def: "f2 \<in> Rep_rev_uspec S3"
      obtain f3 f4 where f3_def: "f3 \<in> Rep_rev_uspec S1" and f4_def: "f4 \<in> Rep_rev_uspec S2" and f1_eq_f3_f4: "f1 = f3 \<parallel> f4"
        by (metis assms(1) empty_iff f1_def uspecIsConsistent_def uspec_parcomp_ele_ex)
      then show "\<exists>(f1a::'a) f2a::'a. f1 \<parallel> f2 = f1a \<parallel> f2a \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec (S2 \<parallel> S3)"
        by (metis (no_types, lifting) assms(1) assms(2) assms(3) f2_def parcomp_asso uspec_parcomp_not_empty uspec_parcompwell_def)
    qed
  next
    show "\<And>(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<Longrightarrow> f2 \<in> Rep_rev_uspec (S2 \<parallel> S3) \<Longrightarrow> 
              \<exists>(f1a::'a) f2a::'a. f1 \<parallel> f2 = f1a \<parallel> f2a \<and> f1a \<in> Rep_rev_uspec (S1 \<parallel> S2) \<and> f2a \<in> Rep_rev_uspec S3"
    proof -
      fix f1::'a and f2::'a
      assume f1_def: "f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec (S2 \<parallel> S3)"
      obtain f3 f4 where f3_def: "f3 \<in> Rep_rev_uspec S2" and f4_def: "f4 \<in> Rep_rev_uspec S3" and f2_eq_f3_f4: "f2 = f3 \<parallel> f4"
        by (metis assms(3) empty_iff f2_def uspecIsConsistent_def uspec_parcomp_ele_ex)
      then show "\<exists>(f1a::'a) f2a::'a. f1 \<parallel> f2 = f1a \<parallel> f2a \<and> f1a \<in> Rep_rev_uspec (S1 \<parallel> S2) \<and> f2a \<in> Rep_rev_uspec S3"
        by (meson assms(1) assms(2) assms(3) f1_def parcomp_asso uspec_parcomp_not_empty uspec_parcompwell_def)
    qed
  qed
  have f11: "uspecRevSet\<cdot>(S1 \<parallel> S2 \<parallel> S3) = uspecRevSet\<cdot>(S1 \<parallel> (S2 \<parallel> S3))"
    apply (subst f2)
    apply (subst f3)
    by (simp add: f10)
  show ?thesis
    apply (rule uspec_eqI)
      apply (simp add: f11)
     apply (simp add: assms(1) assms(3) f0 f1 sup_assoc uspec_parcomp_dom)
    by (simp add: assms(1) assms(3) f0 f1 sup_assoc uspec_parcomp_ran)
qed

(*   *)
lemma uspec_parcompwell_asso_h: assumes "uspec_parcompwell S1 S2" and "uspec_parcompwell S1 S3"
and "uspec_parcompwell S2 S3" shows "uspec_parcompwell S1 (S2 \<parallel> S3)"
  apply (simp add: uspec_parcompwell_def, auto)
  by (metis assms(1) assms(2) assms(3) parcompwell_asso uspec_parcomp_ele_ex uspec_parcompwell2ufunclparcompwell)

(* the new component is uspecwell  *) 
lemma uspec_parcompwell_asso: assumes "uspec_parcompwell S1 S2" and "uspec_parcompwell S1 S3"
and "uspec_parcompwell S2 S3" 
shows "uspecWell  (Rev {f1 \<parallel> f2 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec (S2 \<parallel> S3)})
      (Discr (uspecDomUnion S1 (S2 \<parallel> S3))) (Discr (uspecRanUnion S1 (S2 \<parallel> S3)))"
  using assms(1) assms(2) assms(3) uspec_parcomp_well uspec_parcompwell_asso_h by blast

subsection \<open>UspecSerComp\<close>

(*   *)
lemma uspec_sercomp_well[simp]: assumes "uspec_sercompwell S1 S2"
  shows "uspecWell (Rev {f1 \<circ> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2})
         (Discr (uspecDom\<cdot>S1)) (Discr (uspecRan\<cdot>S2))"
  apply (rule uspec_wellI)
   apply (smt CollectD assms ufuncl_sercomp_dom uspec_allDom uspec_sercompwell_def uspecrevset_insert)
  by (smt CollectD assms ufuncl_sercomp_ran uspec_allRan uspec_sercompwell_def uspecrevset_insert)

lemma uspec_sercompwell2ufunclsercompwell: assumes "uspec_sercompwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. ufunclSerCompWell f1 f2"
  using assms uspec_sercompwell_def by blast

(*   *)
lemma uspec_sercomp_rep[simp]: assumes "uspec_sercompwell S1 S2"
shows "{f1 \<circ> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} 
          = Rep_rev_uspec (S1 \<circle> S2)"
  apply (simp add: uspecSerComp_def)
  by (metis (mono_tags, lifting) assms mem_Collect_eq rep_abs_rev_simp uspecWell.simps uspec_sercomp_well)
(*   *)
lemma uspec_sercomp_not_empty:  assumes "uspec_sercompwell S1 S2"
"f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
shows "(f1 \<circ> f2) \<in> Rep_rev_uspec (S1 \<circle> S2)"
  using assms(1) assms(2) f2_def uspec_sercomp_rep by fastforce

(*   *)
lemma uspec_sercomp_consistent: assumes "uspec_sercompwell S1 S2"
  and "uspecIsConsistent S1" and "uspecIsConsistent S2"
shows "uspecIsConsistent (S1 \<circle> S2)"
  by (metis assms(1) assms(2) assms(3) ex_in_conv uspecIsConsistent_def uspec_sercomp_not_empty)

(*   *)
lemma uspec_sercomp_consistent2: assumes "uspecIsConsistent (S1 \<circle> S2)"
  shows "uspecIsConsistent S1 \<and> uspecIsConsistent S2"
  by (smt Collect_empty_eq assms emptyE uspecIsConsistent_def uspec_sercomp_rep uspec_sercompwell_def)

(*   *)
lemma uspec_sercomp_dom: assumes "uspec_sercompwell S1 S2"
  shows "uspecDom\<cdot>(S1 \<circle> S2) = uspecDom\<cdot>S1"
  apply (simp add: uspecSerComp_def)
  apply (subst uspecdom_insert)
  apply (simp only: uspec_sercomp_well assms rep_abs_uspec)
  by simp

(*   *)
lemma uspec_sercomp_ran: assumes "uspec_sercompwell S1 S2"
  shows "uspecRan\<cdot>(S1 \<circle> S2) = uspecRan\<cdot>S2"
  apply (simp add: uspecSerComp_def)
  apply (subst uspecran_insert)
  apply (simp only: uspec_sercomp_well assms rep_abs_uspec)
  by simp

(* if the composition of 2 uspecs is consistent then those uspecs are consistent themselves  *)
lemma uspec_sercomp_ele_ex: assumes "uspec_sercompwell S1 S2"
and "f \<in> Rep_rev_uspec (S1 \<circle> S2)"
shows "\<exists> f1 \<in> Rep_rev_uspec S1. \<exists> f2 \<in> Rep_rev_uspec S2. f = f1 \<circ> f2"
  using assms(1) assms(2) uspec_sercomp_rep by fastforce

lemma uspec_sercomp_h1: assumes "uspec_sercompwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. f1 \<circ> f2 \<in> Rep_rev_uspec (S1 \<circle> S2)"
  by (simp add: assms uspec_sercomp_not_empty)

lemma uspec_sercomp_h2: assumes "uspec_sercompwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. ufunclSerCompWell f1 f2"
  using assms uspec_sercompwell_def by blast

(* sercomp of uspec is associative  *)
lemma uspec_sercomp_asso: assumes "uspec_sercompwell S1 S2" and "uspec_sercompwell S2 S3"
and "uspecDom\<cdot>S1 \<inter> uspecRan\<cdot>S2 = {}" 
and "uspecDom\<cdot>S2 \<inter> uspecRan\<cdot>S3 = {}" 
shows "((S1 \<circle> S2) \<circle> S3) = (S1 \<circle> (S2 \<circle> S3))"
proof -
  have f0: "uspec_sercompwell (S1 \<circle> S2) S3"
  proof (simp add: uspec_sercompwell_def, auto)
    fix f1::'a and f2::'a 
    assume a1: "f1 \<in> Rep_rev_uspec (S1 \<circle> S2)"
    assume a2: "f2 \<in> Rep_rev_uspec S3"
    obtain f3 f4 where f3_def: "f3 \<in> Rep_rev_uspec S1" and f4_def: "f4 \<in> Rep_rev_uspec S2" 
        and f1_eq_f3_f4: "f1 = f3 \<circ> f4"
      by (metis assms(1) empty_iff a1 uspecIsConsistent_def uspec_sercomp_ele_ex)
    have f1: "ufunclSerCompWell f3 f4"
      using assms(1) f3_def f4_def uspec_sercompwell2ufunclsercompwell by blast
    have f2: "ufunclSerCompWell f4 f2"
      using a2 assms(2) f4_def uspec_sercompwell_def by blast
    have f3: "ufclDom\<cdot>f3 \<inter> ufclRan\<cdot>f4 = {}"
      by (metis assms(3) f3_def f4_def uspec_allDom uspec_allRan uspecrevset_insert)
    have f4: "ufclDom\<cdot>f4 \<inter> ufclRan\<cdot>f2 = {}"
      by (metis a2 assms(4) f4_def uspec_allDom uspec_allRan uspecrevset_insert)
    show "ufunclSerCompWell f1 f2"
      by (simp add: f1 f1_eq_f3_f4 f2 f3 f4 sercompwell_asso2)
  qed
  have f1: "uspec_sercompwell S1 (S2 \<circle> S3)"
  proof (simp add: uspec_sercompwell_def, auto)
    fix f1::'a and f2::'a 
    assume a1: "f1 \<in> Rep_rev_uspec S1"
    assume a2: "f2 \<in> Rep_rev_uspec (S2 \<circle> S3)"
    obtain f3 f4 where f3_def: "f3 \<in> Rep_rev_uspec S2" and f4_def: "f4 \<in> Rep_rev_uspec S3" 
        and f1_eq_f3_f4: "f2 = f3 \<circ> f4"
        using assms(2) a2 uspec_sercomp_rep by blast
    have f1: "ufunclSerCompWell f3 f4"
      using assms(2) f3_def f4_def uspec_sercompwell_def by auto
    have f2: "ufunclSerCompWell f1 f3"
      using a1 assms(1) f3_def uspec_sercompwell2ufunclsercompwell by blast
    have f3: "ufclDom\<cdot>f1 \<inter> ufclRan\<cdot>f3 = {}"
      by (metis a1 assms(3) f3_def uspec_allDom uspec_allRan uspecrevset_insert)
    have f4: "ufclDom\<cdot>f3 \<inter> ufclRan\<cdot>f4 = {}"
      by (metis assms(4) f3_def f4_def uspec_allDom uspec_allRan uspecrevset_insert)
    show "ufunclSerCompWell f1 f2"
      by (simp add: f1 f1_eq_f3_f4 f2 f3 f4 sercompwell_asso1)
  qed
  have f2: "uspecRevSet\<cdot>(S1 \<circle> S2 \<circle> S3) = 
      Rev {f1 \<circ> f2 |f1 f2. f1 \<in> Rep_rev_uspec (S1 \<circle> S2) \<and> f2 \<in> Rep_rev_uspec S3}"
    apply (simp add: uspecrevset_insert)
    apply (subst uspec_sercomp_rep)
     apply (simp add: f0)
    by (simp add: rev_inv_rev)
  have f3: "uspecRevSet\<cdot>(S1 \<circle> (S2 \<circle> S3)) = 
      Rev {f1 \<circ> f2 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec (S2 \<circle> S3)}"
    apply (simp add: uspecrevset_insert)
    apply (subst uspec_sercomp_rep)
     apply (simp add: f1)
    by (simp add: rev_inv_rev)
  have f10: "{f1 \<circ> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec (S1 \<circle> S2) \<and> f2 \<in> Rep_rev_uspec S3} =
              {f1 \<circ> f2 |(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec (S2 \<circle> S3)}"
    apply (rule subset_antisym)
     apply (rule subsetI)
  proof auto
    show "\<And>(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec (S1 \<circle> S2) \<Longrightarrow> f2 \<in> Rep_rev_uspec S3 \<Longrightarrow> \<exists>(f1a::'a) f2a::'a. f1 \<circ> f2 = f1a \<circ> f2a \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec (S2 \<circle> S3)"
    proof -
      fix f1::'a and f2::'a
      assume f1_def: "f1 \<in> Rep_rev_uspec (S1 \<circle> S2)" and f2_def: "f2 \<in> Rep_rev_uspec S3"
      obtain f3 f4 where f3_def: "f3 \<in> Rep_rev_uspec S1" and f4_def: "f4 \<in> Rep_rev_uspec S2" 
        and f1_eq_f3_f4: "f1 = f3 \<circ> f4"
        by (metis assms(1) empty_iff f1_def uspecIsConsistent_def uspec_sercomp_ele_ex)
      have f1: " f1 \<circ> f2 = f3 \<circ> (f4 \<circ> f2)"
        apply (subst f1_eq_f3_f4)
        by (metis assms(1) assms(2) f2_def f3_def f4_def sercomp_asso uspec_sercompwell2ufunclsercompwell)
      then show "\<exists>(f1a::'a) f2a::'a. f1 \<circ> f2 = f1a \<circ> f2a \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec (S2 \<circle> S3)"
        using assms(2) f2_def f3_def f4_def uspec_sercomp_h1 by blast
    qed
  next
    show "\<And>(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<Longrightarrow> f2 \<in> Rep_rev_uspec (S2 \<circle> S3) \<Longrightarrow> \<exists>(f1a::'a) f2a::'a. f1 \<circ> f2 = f1a \<circ> f2a \<and> f1a \<in> Rep_rev_uspec (S1 \<circle> S2) \<and> f2a \<in> Rep_rev_uspec S3"
    proof -
      fix f1::'a and f2::'a
      assume f1_def: "f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec (S2 \<circle> S3)"
      obtain f3 f4 where f3_def: "f3 \<in> Rep_rev_uspec S2" and f4_def: "f4 \<in> Rep_rev_uspec S3" 
                    and f2_eq_f3_f4: "f2 = f3 \<circ> f4"
        using assms(2) f2_def uspec_sercomp_rep by blast
      have f1: "f1 \<circ> f2 = (f1 \<circ> f3) \<circ> f4"
        apply (subst f2_eq_f3_f4)
        using assms(1) assms(2) f1_def f3_def f4_def sercomp_asso uspec_sercompwell2ufunclsercompwell by blast
      then show "\<exists>(f1a::'a) f2a::'a. f1 \<circ> f2 = f1a \<circ> f2a \<and> f1a \<in> Rep_rev_uspec (S1 \<circle> S2) \<and> f2a \<in> Rep_rev_uspec S3"
        using assms(1) f1_def f3_def f4_def uspec_sercomp_not_empty by blast
    qed
  qed
  have f11: "uspecRevSet\<cdot>(S1 \<circle> S2 \<circle> S3) = uspecRevSet\<cdot>(S1 \<circle> (S2 \<circle> S3))"
    by (simp add: f10 f2 f3)
  show ?thesis
    apply (rule uspec_eqI)
      apply (simp add: f11)
     apply (simp add: assms(1) f0 f1 uspec_sercomp_dom)
    by (simp add: assms(2) f0 f1 uspec_sercomp_ran)
qed

subsection \<open>UspecFeedbackComp\<close>

lemma uspec_feedbackcomp_well: "uspecWell (Rev {ufunclFeedbackComp f1 | f1.  f1\<in>(Rep_rev_uspec S1)})
  (Discr (uspecDom\<cdot>S1 - uspecRan\<cdot>S1)) (Discr (uspecRan\<cdot>S1))"
  apply (rule uspec_wellI)
   apply (smt CollectD ufuncl_feedbackcomp_dom uspec_allDom uspec_allRan uspecrevset_insert)
  by (smt CollectD ufuncl_feedbackcomp_ran uspec_allRan uspecrevset_insert)

lemma uspec_feedbackcomp_insert: "uspecFeedbackComp S1 = 
  Abs_rev_uspec  {ufunclFeedbackComp f1 | f1.  f1\<in>(Rep_rev_uspec S1)}
  (uspecDom\<cdot>S1 - uspecRan\<cdot>S1) (uspecRan\<cdot>S1)"
  by (simp add: uspecFeedbackComp_def)

lemma uspec_feedbackcomp_consistent_iff: "uspecIsConsistent (uspecFeedbackComp S) = uspecIsConsistent S"
  apply (simp add: uspecIsConsistent_def uspecFeedbackComp_def)
  apply (subst rep_abs_rev_simp)
   apply (simp only: uspec_feedbackcomp_well)
  apply rule
  by simp+

lemma uspec_feecbackcomp_dom: "uspecDom\<cdot>(uspecFeedbackComp S) = uspecDom\<cdot>S - uspecRan\<cdot>S"
  apply (simp add: uspecFeedbackComp_def)
  apply (subst uspecdom_insert)
  apply (simp only: uspec_feedbackcomp_well rep_abs_uspec)
  by simp

lemma uspec_feecbackcomp_ran: "uspecRan\<cdot>(uspecFeedbackComp S) = uspecRan\<cdot>S"
  apply (simp add: uspecFeedbackComp_def)
  apply (subst uspecran_insert)
  apply (simp only: uspec_feedbackcomp_well rep_abs_uspec)
  by simp

lemma uspec_feedbackcomp_f_ex: assumes "f \<in> Rep_rev_uspec (uspecFeedbackComp S)"
  shows "\<exists> f1 \<in> Rep_rev_uspec S. f = ufunclFeedbackComp f1"
proof -
  have "Rep_uspec (Abs_rev_uspec {(\<mu>) a |a. a \<in> Rep_rev_uspec S} (uspecDom\<cdot>S - uspecRan\<cdot>S) (uspecRan\<cdot>S)) = (Rev {(\<mu>) a |a. a \<in> Rep_rev_uspec S}, Discr (uspecDom\<cdot>S - uspecRan\<cdot>S), Discr (uspecRan\<cdot>S))"
    using rep_abs_uspec uspec_feedbackcomp_well by blast
  then have "{(\<mu>) a |a. a \<in> Rep_rev_uspec S} = Rep_rev_uspec (uspecFeedbackComp S)"
    by (simp add: inv_rev_rev uspec_feedbackcomp_insert)
  then have "\<exists>a. f = (\<mu>) a \<and> a \<in> Rep_rev_uspec S"
    using assms by blast
  then show ?thesis
    by blast
qed



lemma  uspecimage_well:
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  shows "uspecWell (setrevImage f (uspecRevSet\<cdot>S)) 
  (Discr (ufclDom\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))))
  (Discr (ufclRan\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))))"
  by (simp add: assms setrevImage_def ufuncldom_least_dom ufuncldom_least_ran uspec_allDom uspec_allRan)

lemma uspecimage_useful_uspecrevset:
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  shows  "uspecRevSet\<cdot>(uspecImage f S) = setrevImage f (uspecRevSet\<cdot>S)"
  by (smt assms uspecimage_well rep_abs_rev_simp rev_inv_rev setrevImage_def uspecImage_def uspecrevset_insert)

lemma uspecimage_useful_dom:
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  shows  "uspecDom\<cdot>(uspecImage f S) = ufclDom\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))"
 by (smt assms fst_conv uspecimage_well rep_abs_uspec snd_conv undiscr_Discr uspecImage_def uspecdom_insert)

lemma uspecimage_useful_ran:
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  shows "uspecRan\<cdot>(uspecImage f S) = ufclRan\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))"
 by (smt assms fst_conv uspecimage_well rep_abs_uspec snd_conv undiscr_Discr uspecImage_def uspecran_insert)

lemma  uspecimage_mono: 
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>((f::('m::ufuncl_comp \<Rightarrow> 'n::ufuncl_comp)) x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
shows "monofun (uspecImage f)"
proof (rule monofunI)
  have b0:  "\<And>(x::'m uspec) y::'m uspec. x \<sqsubseteq> y 
  \<Longrightarrow> (setrevImage f (uspecRevSet\<cdot>x))  \<sqsubseteq> (setrevImage f (uspecRevSet\<cdot>y))"
    by (metis image_mono inv_rev_rev monofun_cfun_arg revBelowNeqSubset setrevImage_def)
  have b1: "\<And>(x::'m uspec) y::'m uspec. x \<sqsubseteq> y 
  \<Longrightarrow> (uspecRevSet\<cdot>(uspecImage f x)) \<sqsubseteq> (uspecRevSet\<cdot>(uspecImage f y))"
    by (metis (full_types) assms b0 uspecimage_useful_uspecrevset)
  show "\<And>(x::'m uspec) y::'m uspec. x \<sqsubseteq> y \<Longrightarrow> uspecImage f x \<sqsubseteq> uspecImage f y"
    by (smt assms b1 uspecimage_useful_dom uspecimage_useful_ran uspec_belowI uspecdom_eq uspecran_eq)
qed 

lemma  uspecimage_cont_uspecrevset:
 assumes "inj (f::('m::ufuncl_comp \<Rightarrow> 'n::ufuncl_comp))"
  and "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  and "chain Y"
  and "chain (\<lambda>i::nat. uspecImage f (Y i))"
shows "uspecRevSet\<cdot>(uspecImage f (\<Squnion>i::nat. Y i)) \<sqsubseteq> uspecRevSet\<cdot>((\<Squnion>i::nat. uspecImage f (Y i)))"
proof -
  have b0: "\<And>S. uspecRevSet\<cdot>(uspecImage f S) = setrevImage f (uspecRevSet\<cdot>S)"
    by (metis assms(2) uspecimage_useful_uspecrevset)
  have b1: "uspecRevSet\<cdot>(uspecImage f (\<Squnion>i::nat. Y i)) = setrevImage f (uspecRevSet\<cdot>(\<Squnion>i::nat. Y i))"
    by (simp add: b0)
  have b2: "setrevImage f (uspecRevSet\<cdot>(\<Squnion>i::nat. Y i)) = setrevImage f (\<Squnion>i::nat. uspecRevSet\<cdot>(Y i))"
    by (metis assms(3) contlub_cfun_arg)
  have b3: "setrevImage f (\<Squnion>i::nat. uspecRevSet\<cdot>(Y i)) \<sqsubseteq> (\<Squnion>i::nat. setrevImage f (uspecRevSet\<cdot>(Y i)))"
    using image_cont_rev assms(1) assms(3) ch2ch_Rep_cfunR cont2contlubE eq_imp_below by blast
  have b4: "(\<Squnion>i::nat. setrevImage f (uspecRevSet\<cdot>(Y i))) = (\<Squnion>i::nat. uspecRevSet\<cdot>(uspecImage f (Y i)))"
    using b0 by auto
  have b5: "(\<Squnion>i::nat. uspecRevSet\<cdot>(uspecImage f (Y i))) = uspecRevSet\<cdot>((\<Squnion>i::nat. uspecImage f (Y i)))"
    by (simp add: assms(4) cont2contlubE)
  show ?thesis
    using b1 b2 b3 b4 b5 by auto
qed

lemma uspecimage_cont_helper: 
  assumes "inj (f::('m::ufuncl_comp \<Rightarrow> 'n::ufuncl_comp))"
  and "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
shows "cont (uspecImage f)"
  apply (rule Cont.contI2)
  subgoal
    using assms(1) assms(2) uspecimage_mono by blast
  subgoal
  proof -
    have b0: "\<And>Y. chain Y \<Longrightarrow> chain (\<lambda>i::nat. uspecImage f (Y i)) 
      \<Longrightarrow> uspecDom\<cdot>(uspecImage f (\<Squnion>i::nat. Y i)) = uspecDom\<cdot>(\<Squnion>i::nat. uspecImage f (Y i))"
      by (metis (no_types) \<open>monofun (uspecImage (f::'m::ufuncl_comp \<Rightarrow> 'n::ufuncl_comp))\<close> 
        is_ub_thelub monofun_def uspecdom_eq)
    have b1: "\<And>Y. chain Y \<Longrightarrow> chain (\<lambda>i::nat. uspecImage f (Y i)) 
      \<Longrightarrow> uspecRan\<cdot>(uspecImage f (\<Squnion>i::nat. Y i)) = uspecRan\<cdot>(\<Squnion>i::nat. uspecImage f (Y i))"
      by (metis (no_types) \<open>monofun (uspecImage (f::'m::ufuncl_comp \<Rightarrow> 'n::ufuncl_comp))\<close> 
        is_ub_thelub monofun_def uspecran_eq)
    show  "\<And>Y. chain Y \<Longrightarrow> chain (\<lambda>i::nat. uspecImage f (Y i)) 
      \<Longrightarrow> uspecImage f (\<Squnion>i::nat. Y i) \<sqsubseteq> (\<Squnion>i::nat. uspecImage f (Y i))"
proof -
fix Ya :: "nat \<Rightarrow> 'm uspec"
assume a1: "chain Ya"
  assume a2: "chain (\<lambda>i. uspecImage f (Ya i))"
  have "\<forall>f fa. (inj fa \<and> (\<forall>m ma. ufclDom\<cdot>(m::'m) = ufclDom\<cdot>ma \<and> ufclRan\<cdot>m = ufclRan\<cdot>ma \<longrightarrow> ufclDom\<cdot>(fa m::'n) = ufclDom\<cdot>(fa ma) 
    \<and> ufclRan\<cdot>(fa m) = ufclRan\<cdot>(fa ma)) \<and> chain f \<and> chain (\<lambda>n. uspecImage fa (f n)) \<longrightarrow> uspecRevSet\<cdot>(uspecImage fa (Lub f)) 
    \<sqsubseteq> uspecRevSet\<cdot>(\<Squnion>n. uspecImage fa (f n))) = ((\<not> inj fa \<or> (\<exists>m ma. (ufclDom\<cdot>m = ufclDom\<cdot>ma \<and> ufclRan\<cdot>m = ufclRan\<cdot>ma) 
    \<and> (ufclDom\<cdot>(fa m) \<noteq> ufclDom\<cdot>(fa ma) \<or> ufclRan\<cdot>(fa m) \<noteq> ufclRan\<cdot>(fa ma))) \<or> \<not> chain f \<or> \<not> chain (\<lambda>n. uspecImage fa (f n))) 
    \<or> uspecRevSet\<cdot>(uspecImage fa (Lub f)) \<sqsubseteq> uspecRevSet\<cdot>(\<Squnion>n. uspecImage fa (f n)))"
  by meson
  then have f3: "\<forall>f fa. (\<not> inj f \<or> (\<exists>m ma. (ufclDom\<cdot>(m::'m) = ufclDom\<cdot>ma \<and> ufclRan\<cdot>m = ufclRan\<cdot>ma) \<and> (ufclDom\<cdot>(f m::'n) 
    \<noteq> ufclDom\<cdot>(f ma) \<or> ufclRan\<cdot>(f m) \<noteq> ufclRan\<cdot>(f ma))) \<or> \<not> chain fa \<or> \<not> chain (\<lambda>n. uspecImage f (fa n))) \<or> 
    uspecRevSet\<cdot>(uspecImage f (Lub fa)) \<sqsubseteq> uspecRevSet\<cdot>(\<Squnion>n. uspecImage f (fa n))"
    by (metis uspecimage_cont_uspecrevset)
  have f4: "\<forall>f. ((ufclDom\<cdot>(v2_3 f::'m) \<noteq> ufclDom\<cdot>(v3_2 f) \<or> ufclRan\<cdot>(v2_3 f) \<noteq> ufclRan\<cdot>(v3_2 f)) \<or> ufclDom\<cdot>(f (v2_3 f)::'n) 
    = ufclDom\<cdot>(f (v3_2 f)) \<and> ufclRan\<cdot>(f (v2_3 f)) = ufclRan\<cdot>(f (v3_2 f))) = ((ufclDom\<cdot>(v2_3 f) \<noteq> ufclDom\<cdot>(v3_2 f) \<or> ufclRan\<cdot>(v2_3 f) 
    \<noteq> ufclRan\<cdot>(v3_2 f)) \<or> ufclDom\<cdot>(f (v2_3 f)) = ufclDom\<cdot>(f (v3_2 f)) \<and> ufclRan\<cdot>(f (v2_3 f)) = ufclRan\<cdot>(f (v3_2 f)))"
    by metis
  obtain nn :: "(nat \<Rightarrow> 'n uspec) \<Rightarrow> nat" where
    "\<forall>f. (\<not> chain f \<or> (\<forall>n. f n \<sqsubseteq> f (Suc n))) \<and> (chain f \<or> f (nn f) \<notsqsubseteq> f (Suc (nn f)))"
    using po_class.chain_def by moura
  then obtain mm :: "('m \<Rightarrow> 'n) \<Rightarrow> 'm" and mma :: "('m \<Rightarrow> 'n) \<Rightarrow> 'm" where
    f5: "ufclDom\<cdot>(mm f) = ufclDom\<cdot>(mma f) \<and> ufclRan\<cdot>(mm f) = ufclRan\<cdot>(mma f) \<and> (ufclDom\<cdot>(f (mm f)) \<noteq> ufclDom\<cdot>(f (mma f)) 
    \<or> ufclRan\<cdot>(f (mm f)) \<noteq> ufclRan\<cdot>(f (mma f))) \<or> uspecRevSet\<cdot>(uspecImage f (Lub Ya)) \<sqsubseteq> uspecRevSet\<cdot>(\<Squnion>n. uspecImage f (Ya n))"
    using f4 f3 a2 a1 by (meson assms(1))
  have f6: "uspecDom\<cdot>(uspecImage f (Lub Ya)) = uspecDom\<cdot>(\<Squnion>n. uspecImage f (Ya n))"
    using a2 a1 b0 by presburger
  have "uspecRevSet\<cdot>(uspecImage f (Lub Ya)) \<sqsubseteq> uspecRevSet\<cdot>(\<Squnion>n. uspecImage f (Ya n))"
    using f5 by (meson assms(2))
  then show "uspecImage f (\<Squnion>n. Ya n) \<sqsubseteq> (\<Squnion>n. uspecImage f (Ya n))"
    using f6 a2 a1 by (metis (no_types) b1 uspec_belowI)
qed

qed
done


lemma uspecimage_inj_cont: 
  assumes "inj f"
      and "\<And>x y. ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y \<Longrightarrow>
          ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)"
    shows "cont (uspecImage f)"
  using assms uspecimage_cont_helper by blast

lemma uspecimage_helper:
  assumes "\<And>x. ufclDom\<cdot>x =  ufclDom\<cdot> (f x)"
    and "\<And>x. ufclRan\<cdot>x =  ufclRan\<cdot> (f x)"
  shows "ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y \<Longrightarrow>
          ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)"
  by (simp add: assms(1) assms(2))
  
lemma uspecimage_dom1 [simp]:
  assumes "\<And>x. ufclDom\<cdot>x =  ufclDom\<cdot> (f x)"
    and "\<And>x. ufclRan\<cdot>x =  ufclRan\<cdot> (f x)"
  shows "uspecDom\<cdot>(uspecImage f S) = uspecDom\<cdot>S"
  using assms
  by (metis ufuncldom_least_dom uspecimage_useful_dom) 

lemma uspecimage_ran1 [simp]:
  assumes "\<And>x. ufclDom\<cdot>x =  ufclDom\<cdot> (f x)"
    and "\<And>x. ufclRan\<cdot>x =  ufclRan\<cdot> (f x)"
  shows "uspecRan\<cdot>(uspecImage f S) = uspecRan\<cdot>S"
  using assms
  by (metis ufuncldom_least_ran uspecimage_useful_ran) 

end
