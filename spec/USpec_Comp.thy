theory USpec_Comp
  imports USpec  inc.CPOFix
begin

default_sort ufuncl_comp

(****************************************************)
section\<open>Definitions\<close>
(****************************************************)   

(* Lemma require the assumption: 
"\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
*)
definition uspecImage::  "('m \<Rightarrow> 'n) \<Rightarrow> 'm uspec \<Rightarrow> 'n uspec" where
"uspecImage f \<equiv>  \<lambda> S.
Abs_uspec ((f` (uspecSet\<cdot>S)), 
  Discr (ufclDom\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))),
  Discr (ufclRan\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))))"

(* Cont version of uspecImage *)
definition uspecImageC::  "('m \<rightarrow> 'n) \<Rightarrow> 'm uspec \<rightarrow> 'n uspec" where
"uspecImageC f \<equiv>  \<Lambda> S. uspecImage (Rep_cfun f) S"

(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)   

subsection\<open>uspecImage\<close>


lemma  uspecimage_well:
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  shows "uspecWell (f ` (uspecSet\<cdot>S)) 
  (Discr (ufclDom\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))))
  (Discr (ufclRan\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))))"
  by (simp add: assms ufuncldom_least_dom ufuncldom_least_ran)

lemma uspecimage_set:
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  shows  "uspecSet\<cdot>(uspecImage f S) = f `(uspecSet\<cdot>S)"
  by (simp add: assms ufuncldom_least_dom ufuncldom_least_ran uspecImage_def uspec_abs_set)

lemma uspecimage_dom:
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  shows  "uspecDom\<cdot>(uspecImage f S) = ufclDom\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))"
 by (smt assms fst_conv uspecimage_well rep_abs_uspec snd_conv undiscr_Discr uspecImage_def uspecdom_insert)

lemma uspecimage_ran:
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  shows "uspecRan\<cdot>(uspecImage f S) = ufclRan\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))"
 by (smt assms fst_conv uspecimage_well rep_abs_uspec snd_conv undiscr_Discr uspecImage_def uspecran_insert)

lemma  uspecimage_mono: 
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>((f::('m::ufuncl_comp \<Rightarrow> 'n::ufuncl_comp)) x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  shows "monofun (uspecImage f)"
  apply(rule monofunI)
  apply(rule uspec_belowI)
  apply (smt assms uspecdom_eq uspecimage_dom uspecran_eq)
   apply (smt assms uspecdom_eq uspecimage_ran uspecran_eq)
  apply(subst uspecimage_set)
  using assms apply blast
  apply(subst uspecimage_set)
  using assms apply blast
  by (metis SetPcpo.less_set_def image_mono monofun_cfun_arg)

lemma setimage_cont[simp]: "cont (\<lambda>s. f ` s)"
  apply(rule contI2, rule monofunI)
  apply(simp_all add: less_set_def lub_eq_Union)
   apply (simp add: image_mono)
  by auto

lemma uspecimage_cont: 
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
shows "cont (uspecImage f)"
  apply (rule Cont.contI2)
  using assms uspecimage_mono apply blast

  apply(rule uspec_belowI)
  apply (smt assms uspecdom_lub_chain uspecimage_dom uspecran_lub_chain)
  apply (smt assms uspecdom_lub_chain uspecimage_ran uspecran_lub_chain)
 apply(subst uspecimage_set)
  using assms apply blast
  apply(simp add: less_set_def contlub_cfun_arg lub_eq_Union)
  by (smt Sup.SUP_cong assms eq_iff image_UN uspecimage_set)

lemma uspecimage_dom1 [simp]:
  assumes "\<And>x. ufclDom\<cdot>(f x) =  ufclDom\<cdot> (x)"
    and "\<And>x. ufclRan\<cdot>(f x) =  ufclRan\<cdot> ( x)"
  shows "uspecDom\<cdot>(uspecImage f S) = uspecDom\<cdot>S"
  by (metis assms(1) assms(2) ufuncldom_least_dom uspecimage_dom)


lemma uspecimage_ran1 [simp]:
  assumes "\<And>x. ufclDom\<cdot>(f x) =  ufclDom\<cdot> (x)"
    and "\<And>x. ufclRan\<cdot>(f x) =  ufclRan\<cdot> (x)"
  shows "uspecRan\<cdot>(uspecImage f S) = uspecRan\<cdot>S"
  using assms
  by (metis ufuncldom_least_ran uspecimage_ran)

lemma urs_img_inj:
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
      and "uspecSet\<cdot>(uspecImage f S1) = uspecSet\<cdot>(uspecImage f S2)"
      and "inj f"
    shows "uspecSet\<cdot>S1 = uspecSet\<cdot>S2"
  by (metis (no_types, lifting) assms(1) assms(2) assms(3) inj_image_eq_iff uspecimage_set)

lemma uspecimage_least: assumes 
        "\<And>x. ufclDom\<cdot> (f x) = ufclDom\<cdot>x"
    and "\<And>x. ufclRan\<cdot> (f x) = ufclRan\<cdot>x"
  shows "uspecImage f (uspecLeast In Out) = uspecLeast In Out"
  by (metis (no_types, lifting) assms(1) assms(2) empty_is_image ufuncldom_least_dom ufuncldom_least_ran uspecImage_def uspecIsConsistent_def uspecLeast.abs_eq uspecleast_consistent uspecleast_dom uspecleast_ran)


lemma uspecimage_not_max: assumes "uspecIsConsistent S"
and  "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
shows "uspecIsConsistent (uspecImage f S)"
  apply(simp add: uspecIsConsistent_def )
  by (metis assms(1) assms(2) empty_is_image uspecIsConsistent_def uspecimage_set)


lemma uspecimage_const[simp]: assumes  "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
    shows "uspecImage f (uspecConst uf) = uspecConst (f uf)"
  apply(rule uspec_eqI)
  apply(simp_all)
  apply (metis (no_types, lifting) assms image_empty image_insert uspecconst_set uspecimage_set)
  apply (metis assms ufuncldom_least_dom ufuncldom_least_ran uspecconst_dom uspecconst_ran uspecimage_dom)
  by (smt assms ufuncldom_least_dom ufuncldom_least_ran uspecconst_dom uspecconst_ran uspecimage_ran)

lemma uspecforall_image:
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  shows "\<And>S. uspecForall (\<lambda>x. uspecExists (\<lambda>y. f y = x) S) (uspecImage f S)"
  apply (simp add: uspecForall_def uspecExists_def)
  by (smt assms image_iff uspecimage_set)



subsection \<open>uspecImageC\<close>

lemma uspecimagec_insert: "uspecImageC f\<cdot>S = uspecImage  (Rep_cfun f) S"
  apply(simp add: uspecImageC_def)
  apply(subst Abs_cfun_inverse2)
  apply(subst uspecimage_cont)
    apply (smt monofun_cfun_arg ufclDom_fix ufclRan_fix ufuncldom_least)
  by auto

lemma uspecimagec_set: "uspecSet\<cdot>(uspecImageC f\<cdot>S) = (Rep_cfun f) `(uspecSet\<cdot>S)"
  apply(simp add: uspecimagec_insert)
  by (smt monofun_Rep_cfun2 monofun_def ufclDom_fix ufclRan_fix ufuncldom_least uspecimage_set)

lemma uspecimagec_dom:
  shows  "uspecDom\<cdot>(uspecImageC f\<cdot>S) = ufclDom\<cdot> (f\<cdot>(ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))"
  apply(simp add: uspecimagec_insert)
  by (smt monofun_Rep_cfun2 monofun_def ufclDom_fix ufclRan_fix ufuncldom_least uspecimage_dom)

lemma uspecimagec_ran:
  shows "uspecRan\<cdot>(uspecImageC f\<cdot>S) = ufclRan\<cdot> (f\<cdot>(ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))"
  by (smt monofun_Rep_cfun2 monofun_def ufclDom_fix ufclRan_fix ufuncldom_least uspecimage_ran uspecimagec_insert)


lemma uspecimagec_least[simp]: assumes "\<And>x. ufclDom\<cdot> (f\<cdot>x) = ufclDom\<cdot>x"
    and "\<And>x. ufclRan\<cdot> (f\<cdot>x) = ufclRan\<cdot>x"
    shows "uspecImageC f\<cdot>(uspecLeast In Out) = uspecLeast In Out"
  by (simp add: assms(1) assms(2) uspecimage_least uspecimagec_insert)

lemma uspecimagec_consistent[simp]: assumes "uspecIsConsistent S"
  shows "uspecIsConsistent (uspecImageC f\<cdot>S)"
  apply(simp add: uspecimagec_insert)
  by (metis (no_types) assms empty_is_image uspecIsConsistent_def uspecimagec_insert uspecimagec_set)

lemma uspecimagec_const [simp]: "uspecImageC f\<cdot>(uspecConst uf) = uspecConst (f\<cdot>uf)"
  by (simp add: uspec_eqI2 uspecimagec_set)

subsection \<open>Size\<close>

lemma uspec_least_infinite: assumes "Y \<noteq> {}"
  shows "uspecSize (uspecMax X Y) = \<infinity>"
  oops

end