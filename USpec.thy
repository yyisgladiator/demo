(*  Title:        USpec
    Author:       Stüber, Jens, Marc
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "universal specification" 
*)

theory USpec
  imports UnivClasses UFun_Comp (* TODO ufclLeast bräuchte ich, dann kann das UFun weg *)
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



(* TODO Welche Theory und welche Section? *)

definition uspecLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> 'm uspec" where
"uspecLeast cin cout = Abs_uspec (Rev {f. ufclDom\<cdot>f = cin \<and> ufclRan\<cdot>f = cout})"

lemma uspecLeast_well: "uspecWell {f. ufclDom\<cdot>f = cin \<and> ufclRan\<cdot>f = cout}"
  sorry

lemma uspecLeast_elem: "ufLeast cin cout \<in> Rep_rev_uspec(uspecLeast cin cout)"
  sorry

lemma uspecLeast_consistent: "uspecIsConsistent (uspecLeast cin cout)"
  sorry

lemma ver: "\<forall>f \<in> {f. ufclDom\<cdot>f = cin \<and> ufclRan\<cdot>f = cout}. ufclDom\<cdot>f = cin"
  by auto

lemma uspecLeast_dom: "uspecDom (uspecLeast cin cout) = cin" (is "?L = ?R")
  proof -
    have a1: "?L = ufclDom\<cdot>(SOME f::'a. ufclDom\<cdot>f = cin \<and> ufclRan\<cdot>f = cout)"
      apply(simp add: uspecDom_def)
      apply(simp add: uspecLeast_def)
      apply(simp only: uspecLeast_well rep_abs_uspec)
      by(simp add: inv_rev_rev)
    moreover have "ufclDom\<cdot>(SOME f::'a. ufclDom\<cdot>f = cin \<and> ufclRan\<cdot>f = cout) = ufclDom\<cdot>(ufLeast cin cout)"
      by (metis (mono_tags, lifting) a1 rep_abs_rev_simp ufclDom_ufun_def ufleast_ufdom uspecLeast_consistent uspecLeast_def uspecLeast_well uspec_consist_f_ex uspec_dom_eq2 ver)
    moreover have "ufclDom\<cdot>(ufLeast cin cout) = cin"
      by (simp add: ufclDom_ufun_def)
    ultimately show ?thesis
      by blast
  qed

end