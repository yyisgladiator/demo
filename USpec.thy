(*  Title:        USpec
    Author:       Stüber, Jens, Marc
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "universal specification" 
*)

theory USpec
  imports UnivClasses
begin

default_sort ufuncl

(****************************************************)
section\<open>Data type\<close>
(****************************************************) 
  
definition uspecWell :: "'m set \<Rightarrow> bool" where
"uspecWell S \<equiv> \<exists>In Out. \<forall> f\<in>S . (ufclDom\<cdot>f = In \<and> ufclRan\<cdot>f=Out) "
(* define a Set of 'm SPF's. all SPS in a set must have the same In/Out channels *)

lemma uspecwell_adm: "adm (\<lambda>x::'m set rev. x \<in> {S::'m set rev. uspecWell (inv Rev S)})"
proof (rule admI)
  fix Y::"nat \<Rightarrow> 'm set rev"
  assume assm1: "chain Y" 
  assume assm2: "\<forall>i::nat. Y i \<in> {S::'m set rev. uspecWell (inv Rev S)} "
  obtain lub_x where lub_x_def: "Rev lub_x = Lub Y"
    by (metis rev.exhaust)
  obtain x_i where x_i_def: "Rev x_i = Y 0"
    by (metis rev.exhaust)
  have f0: "inv Rev (Lub Y) = lub_x"
    by (metis UNIV_I f_inv_into_f lub_x_def rev.exhaust rev.inject surj_def)
  have f00: "inv Rev (Y 0) = x_i"
    by (metis UNIV_I f_inv_into_f x_i_def rev.exhaust rev.inject surj_def)
  have f5: "\<And> f . f \<in> lub_x \<Longrightarrow> f \<in> x_i"
    by (metis SetPcpo.less_set_def assm1 below_rev.simps contra_subsetD is_ub_thelub lub_x_def x_i_def)
  have f8: "inv Rev (Lub Y) \<sqsubseteq> inv Rev (Y 0)"
    by (simp add: SetPcpo.less_set_def f0 f00 f5 subsetI)
  have "uspecWell(inv Rev (\<Squnion>i::nat. Y i))"
    by (metis (full_types) assm2 f0 f00 f5 mem_Collect_eq uspecWell_def)
  then  show "(\<Squnion>i::nat. Y i) \<in> {S::'m set rev. uspecWell (inv Rev S)}"
    by simp
qed

cpodef 'm uspec = "{S :: 'm set rev. uspecWell (inv Rev S) }"
   apply(simp add: uspecWell_def)
   apply (rule_tac x="Rev {}" in exI)
   apply (metis UNIV_I empty_iff f_inv_into_f rev.exhaust rev.inject surj_def)
  using uspecwell_adm by simp

setup_lifting type_definition_uspec

(****************************************************)
section\<open>Definitions\<close>
(****************************************************) 
  
(* abbreviations should be defined in the classes or ufun.thy *)
subsection\<open>abbreviations\<close>

abbreviation Rep_rev_uspec:: "'m uspec \<Rightarrow> 'm set" where
"Rep_rev_uspec uspec \<equiv> inv Rev (Rep_uspec uspec)"

abbreviation Abs_rev_uspec:: "'m set \<Rightarrow> 'm uspec" where
"Abs_rev_uspec spec \<equiv> Abs_uspec (Rev spec)"

definition uspecDom :: "'m uspec \<Rightarrow> channel set" where
"uspecDom S = ufclDom\<cdot>(SOME f. f\<in>  ((inv Rev) (Rep_uspec S)))"

definition uspecRan :: "'m uspec \<Rightarrow> channel set" where
"uspecRan S = ufclRan\<cdot>(SOME f. f\<in> ((inv Rev) (Rep_uspec S)))"


(****************************************************)
section\<open>Predicates\<close>
(****************************************************) 

definition uspecIsConsistent :: "'m uspec \<Rightarrow> bool" where
"uspecIsConsistent S \<equiv> (((inv Rev) (Rep_uspec S)) \<noteq> {})"


(****************************************************)
section\<open>Lemmas\<close>
(****************************************************) 
subsection \<open>General Lemmas\<close>

lemma uspec_wellI: assumes "\<forall> f \<in> S. ufclDom\<cdot>f = In" and "\<forall> f \<in> S. ufclRan\<cdot>f = Out"
  shows "uspecWell S"
  apply (simp add: uspecWell_def)
  apply (rule_tac x= "In" in exI)
  apply (rule_tac x= "Out" in exI)
  using assms(1) assms(2) by auto


(* rule to prove the equality of uspec *)
lemma uspec_eqI: assumes "((inv Rev) (Rep_uspec S1)) = ((inv Rev) (Rep_uspec S2))"
  shows "S1 = S2"
  by (metis Rep_uspec_inverse UNIV_I assms f_inv_into_f image_eqI rev.exhaust)

lemma uspec_eqI2: assumes "\<And>f1 . f1\<in>((inv Rev) (Rep_uspec S1)) \<Longrightarrow> f1\<in>((inv Rev) (Rep_uspec S2))" 
      and "\<And>f2 . f2\<in>((inv Rev) (Rep_uspec S2)) \<Longrightarrow> f2\<in>((inv Rev) (Rep_uspec S1))"
  shows "S1 = S2" 
  apply (rule uspec_eqI, auto)
  by (simp_all add: assms)

(* rep abs subtitution  *)
lemma rep_abs_uspec [simp]: assumes "uspecWell x" 
  shows "Rep_uspec (Abs_uspec (Rev x)) = (Rev x)"
  by (metis Abs_uspec_inverse CollectI assms f_inv_into_f rangeI rev.inject)

(*   *)
lemma [simp]: "uspecWell (inv Rev (Rep_uspec x))"
  using Rep_uspec by auto

(* rep_uspec is a monofun *)
lemma uspec_rep_mono [simp]: "monofun Rep_uspec"
  apply(rule monofunI)
  by (simp add: below_uspec_def)

(* rep_uspec is a cont function  *)
lemma uspec_rep_cont [simp]: "cont Rep_uspec"
  by (metis (mono_tags, lifting) Abs_uspec_inverse Cont.contI2 Rep_uspec 
        adm_def adm_uspec lub_eq lub_uspec po_eq_conv uspec_rep_mono)

(* rule to prove that below relation between uspecs  *)
lemma rep_uspec_belowI: assumes "S1 \<sqsubseteq> S2"
  shows "(Rep_uspec S1) \<sqsubseteq> (Rep_uspec S2)"
  by (meson assms below_uspec_def)

lemma uspec_belowI: assumes "inv Rev (Rep_uspec S2) \<sqsubseteq> inv Rev (Rep_uspec S1)"
  shows "S1 \<sqsubseteq> S2"
  by (metis assms below_rev.simps below_uspec_def rev.exhaust surj_def surj_f_inv_f)

(* kill me and change the name of this lemma *)
lemma inv_rev_rep_upsec_below: assumes "(Rep_uspec S1) \<sqsubseteq> (Rep_uspec S2)"
  shows "inv Rev (Rep_uspec S2) \<sqsubseteq> inv Rev (Rep_uspec S1)"
  by (metis assms below_rev.simps f_inv_into_f rangeI rev.exhaust)

(*  *)
lemma rep_abs_simp[simp]: assumes "uspecWell S1" shows "Rev S1 = Rep_uspec (Abs_uspec (Rev S1))"
  by (simp add: assms)

(*  *)
lemma abs_rep_simp[simp]: "S1 = Abs_uspec (Rep_uspec S1)"
  by (simp add: Rep_uspec_inverse)


lemma rep_abs_rev_simp[simp]: assumes "uspecWell S1"
  shows "Rep_rev_uspec (Abs_rev_uspec S1) = S1"
  by (metis UNIV_I assms f_inv_into_f image_iff rep_abs_uspec rev.inject)


lemma abs_rep_rev_simp[simp]: "Abs_rev_uspec (Rep_rev_uspec S1) = S1"
  by (metis UNIV_I abs_rep_simp f_inv_into_f rev.exhaust surj_def)


(* if the upper uspec is consistent then the lower uspec is also consistent  *)
lemma uspec_isconsistent_below: assumes "S1\<sqsubseteq>S2" and "uspecIsConsistent S2"
  shows "uspecIsConsistent S1"
  by (metis UU_eq_empty assms(1) assms(2) below_bottom_iff 
        below_uspec_def inv_rev_rep_upsec_below uspecIsConsistent_def)

(* simple rule to check the below relation  *)
lemma uspec_ele_below: assumes "S1\<sqsubseteq>S2"  shows "\<And> f. f\<in>inv Rev (Rep_uspec S2) \<Longrightarrow> f \<in> inv Rev (Rep_uspec S1)"
    by (metis (mono_tags, lifting) SetPcpo.less_set_def assms(1) contra_subsetD inv_rev_rep_upsec_below rep_uspec_belowI)


lemma empty_uspecwell[simp]:  "uspecWell {}"
  by (simp add: uspecWell_def)

lemma empty_max: "\<And> uspec. uspec \<sqsubseteq> (Abs_uspec (Rev {}))"
  apply (rule uspec_belowI)
  apply (subst rep_abs_rev_simp, simp)
  by (simp add: SetPcpo.less_set_def)

lemma not_uspec_consisten_empty_eq: assumes "\<not> uspecIsConsistent S"
  shows "Rep_rev_uspec S = {}"
  using assms by (simp add: uspecIsConsistent_def assms)

lemma uspec_consist_f_ex: assumes "uspecIsConsistent S" shows "\<exists> f. f \<in> Rep_rev_uspec S"
  using assms uspecIsConsistent_def by auto

subsection \<open>Dom and Ran\<close>

(* dom of of two consitent uspec is eq  *)
lemma uspecdom_eq: assumes "S1\<sqsubseteq>S2" and "uspecIsConsistent S2"
  shows "uspecDom S1 = uspecDom S2"
proof -
  have f1: "inv Rev (Rep_uspec S2) \<sqsubseteq> inv Rev (Rep_uspec S1)"
    by (simp add: assms(1) inv_rev_rep_upsec_below rep_uspec_belowI)
  obtain f where f_def: "f \<in> inv Rev (Rep_uspec S2)" 
    using assms(2) uspecIsConsistent_def by auto
  have f3: "f \<in> inv Rev (Rep_uspec S1)"
    by (metis SetPcpo.less_set_def contra_subsetD f1 f_def)
  show ?thesis
    apply (simp add: uspecDom_def)
    by (metis (mono_tags, lifting) Quotient_rel_rep Quotient_to_Domainp Quotient_uspec SetPcpo.less_set_def contra_subsetD 
          f1 f_def some_eq_ex uspec.domain_eq uspec.pcr_cr_eq uspecWell_def)
qed

(* ran of of two consitent uspec is eq  *)
lemma uspecran_eq: assumes "S1\<sqsubseteq>S2" and "uspecIsConsistent S2"
  shows "uspecRan S1 = uspecRan S2"
proof -
  obtain f where f_def: "f \<in> inv Rev (Rep_uspec S2)" 
    using assms(2) uspecIsConsistent_def by auto
  have f3: "f \<in> inv Rev (Rep_uspec S1)"
    using assms(1) assms(2) f_def uspec_ele_below by blast
  show ?thesis
    by (metis Rep_uspec empty_iff f3 f_def mem_Collect_eq some_in_eq uspecRan_def uspecWell_def)
qed

(* all element in uspec have the same dom  *)
lemma uspec_allDom: "\<exists>In. \<forall>f\<in>inv Rev (Rep_uspec S1). ufclDom\<cdot>f=In"
  using uspecWell_def by fastforce

(* all element in uspec have the same ran  *)
lemma uspec_allRan: "\<exists>Out. \<forall>f\<in>inv Rev (Rep_uspec S1). ufclRan\<cdot>f=Out"
  using uspecWell_def by fastforce

(* *)
lemma uspec_dom_eq: assumes "f \<in> (inv Rev) (Rep_uspec S)" shows "ufclDom\<cdot>f = uspecDom S"
  by (metis (full_types) assms empty_iff some_in_eq uspec_allDom uspecDom_def)

lemma uspec_dom_eq2: assumes "uspecIsConsistent S" shows "\<forall> f \<in> Rep_rev_uspec S. ufclDom\<cdot>f = uspecDom S"
  by (simp add: uspec_dom_eq)

(* *)
lemma uspec_ran_eq: assumes "f \<in> (inv Rev) (Rep_uspec S)" shows "ufclRan\<cdot>f = uspecRan S"
  by (metis (mono_tags, lifting) Quotient_rel_rep Quotient_to_Domainp Quotient_uspec 
      assms some_eq_ex uspec.domain_eq uspec.pcr_cr_eq uspecRan_def uspecWell_def)

lemma uspec_ran_eq2: assumes "uspecIsConsistent S" shows "\<forall> f \<in> Rep_rev_uspec S. ufclRan\<cdot>f = uspecRan S"
  by (simp add: uspec_ran_eq)

lemma revBelowNeqSubset: "\<And>A:: 'a set rev. \<forall>B:: 'a set rev. A \<sqsubseteq> B \<longleftrightarrow> (inv Rev B \<subseteq> inv Rev A)"
  by (smt SetPcpo.less_set_def below_rev.elims(2) below_rev.elims(3) inv_rev_rev)

lemma SLEI_help1:  "\<And>Y::nat \<Rightarrow> 'a set rev. 
  chain Y \<Longrightarrow> Rev (\<Inter>{x. \<exists>i. x = inv Rev (Y i)}) \<sqsubseteq> (\<Squnion>i. Y i)" 
proof -
fix Y :: "nat \<Rightarrow> 'a set rev"
  assume a1: "chain Y"
  obtain AA :: "'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
    "\<forall>x0 x1. (\<exists>v2. v2 \<in> x0 \<and> \<not> x1 \<subseteq> v2) = (AA x0 x1 \<in> x0 \<and> \<not> x1 \<subseteq> AA x0 x1)"
  by moura
  then have f2: "(\<not> inv Rev (Lub Y) \<subseteq> \<Inter>{A. \<exists>n. A = inv Rev (Y n)} \<or> 
    (\<forall>A. A \<notin> {A. \<exists>n. A = inv Rev (Y n)} \<or> inv Rev (Lub Y) \<subseteq> A)) \<and> (inv Rev (Lub Y) \<subseteq> 
    \<Inter>{A. \<exists>n. A = inv Rev (Y n)} \<or> AA {A. \<exists>n. A = inv Rev (Y n)} (inv Rev (Lub Y)) \<in> 
    {A. \<exists>n. A = inv Rev (Y n)} \<and> \<not> inv Rev (Lub Y) \<subseteq> AA {A. \<exists>n. A = inv Rev (Y n)} 
    (inv Rev (Lub Y)))"
  by (meson le_Inf_iff)
  obtain nn :: "'a set \<Rightarrow> nat" where
    f3: "((\<nexists>n. AA {A. \<exists>n. A = inv Rev (Y n)} (inv Rev (Lub Y)) = inv Rev (Y n)) \<or> 
    AA {A. \<exists>n. A = inv Rev (Y n)} (inv Rev (Lub Y)) = inv Rev (Y (nn (AA {A. \<exists>n. A = inv Rev (Y n)} 
    (inv Rev (Lub Y)))))) \<and> ((\<exists>n. AA {A. \<exists>n. A = inv Rev (Y n)} (inv Rev (Lub Y)) = inv Rev (Y n)) \<or> 
    (\<forall>n. AA {A. \<exists>n. A = inv Rev (Y n)} (inv Rev (Lub Y)) \<noteq> inv Rev (Y n)))"
    by meson
  { assume "AA {A. \<exists>n. A = inv Rev (Y n)} (inv Rev (Lub Y)) \<noteq> 
    inv Rev (Y (nn (AA {A. \<exists>n. A = inv Rev (Y n)} (inv Rev (Lub Y)))))"
    then have "inv Rev (Lub Y) \<subseteq> \<Inter>{A. \<exists>n. A = inv Rev (Y n)}"
  using f3 f2 by auto }
  then have "inv Rev (Lub Y) \<subseteq> \<Inter>{A. \<exists>n. A = inv Rev (Y n)}"
using a1 is_ub_thelub revBelowNeqSubset by blast
  then show "Rev (\<Inter>{A. \<exists>n. A = inv Rev (Y n)}) \<sqsubseteq> (\<Squnion>n. Y n)"
    by (simp add: inv_rev_rev revBelowNeqSubset)
qed

lemma SLEI_help2:  "\<And>Y::nat \<Rightarrow> 'a set rev. 
  chain Y \<Longrightarrow> (\<Squnion>i. Y i) \<sqsubseteq> Rev (\<Inter>{x. \<exists>i. x = inv Rev (Y i)})"
proof -
  have a0: "\<And>Y::nat \<Rightarrow> 'a set rev. 
  chain Y \<Longrightarrow>{y} \<subseteq> (\<Inter>{x. \<exists>i. x = inv Rev (Y i)}) \<longrightarrow> (\<forall>z. (Y z) \<sqsubseteq> Rev {y})"
    by (metis (mono_tags, lifting) CollectI revBelowNeqSubset insert_subset inv_rev_rev mem_simps(11)
      rev_bot_top set_cpo_simps(3))
  have a1:  "\<And>Y::nat \<Rightarrow> 'a set rev. chain Y \<Longrightarrow> (\<forall>z. (Y z) \<sqsubseteq> Rev {y}) \<longrightarrow> (\<Squnion>i. Y i) \<sqsubseteq> Rev {y}"
    by (simp add: lub_below)
  show  "\<And>Y::nat \<Rightarrow> 'a set rev. 
  chain Y \<Longrightarrow> (\<Squnion>i. Y i) \<sqsubseteq> Rev (\<Inter>{x. \<exists>i. x = inv Rev (Y i)})"
    by (smt CollectI below_rev.elims(3) inv_rev_rev le_Inf_iff lub_below order_refl set_cpo_simps(1))
qed

lemma setrevLubEqInter:  "\<And>Y::nat \<Rightarrow> 'a set rev. 
  chain Y \<Longrightarrow> (\<Squnion>i. Y i) = Rev (\<Inter>{x. \<exists>i. x = inv Rev (Y i)})"
  using SLEI_help1 SLEI_help2 po_eq_conv by blast                               

end