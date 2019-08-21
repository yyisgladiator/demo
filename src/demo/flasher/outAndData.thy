theory outAndData

imports Data_inc
begin


typedef outAnd="{cout}"
  by auto



instance outAnd::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_outAnd typedef_finite_UNIV by fastforce

instantiation outAnd::somechan
begin
definition Rep_outAnd_def: "Rep = Rep_outAnd"

lemma repand_range[simp]: "range (Rep::outAnd \<Rightarrow> channel) = {cout}"
  apply(subst Rep_outAnd_def)
  using type_definition.Rep_range type_definition_outAnd by fastforce

instance
  apply(intro_classes)
  apply clarsimp
  unfolding Rep_outAnd_def by (meson Rep_outAnd_inject injI)
end

lemma outAnd_chdom[simp]: "chDom TYPE (outAnd) = {cout}"
  by (simp add: somechandom)



section \<open>Constructors\<close>

definition "Andoutout \<equiv> Abs_outAnd cout"

free_constructors outAnd for Andoutout
  apply auto?  (* TODO: kann man das "auto" entfernen? *)
  unfolding Andoutout_def
  apply (metis Rep_outAnd Rep_outAnd_inverse empty_iff insert_iff)
  apply (simp add: Abs_outAnd_inject)?
  done

lemma Andoutout_rep [simp]: "Rep Andoutout = cout"
  unfolding Rep_outAnd_def Andoutout_def
  by (simp add: Abs_outAnd_inverse)



section \<open>Preperation for locale instantiation\<close>

(* Tuple:
      1. Value should go to port cout. It is of type "bool"
*)

(* The first parameter is the converter from user-type (here bool) to "M" 

  for every type in the tuple such a function must be in the parameter. So if the tuple
  would consist of (nat\<times>bool) there are 2 converters required *)

fun outAndChan::"('bool \<Rightarrow> 'a) \<Rightarrow> ('bool) \<Rightarrow> outAnd \<Rightarrow> 'a" where
"outAndChan boolConv  (port_cout) Andoutout = boolConv port_cout" 

(* Helper Function for lemmata (mostly surj). Should be hidden from the user! *)
definition outAndChan_inv::"('bool \<Rightarrow> 'a) \<Rightarrow> (outAnd \<Rightarrow> 'a) \<Rightarrow> ('bool)" where
"outAndChan_inv boolConv f = ((inv boolConv) (f Andoutout))" 

lemma outAndChan_surj_helper: 
    assumes "f Andoutout \<in> range boolConv"
  shows "outAndChan boolConv (outAndChan_inv boolConv f) = f"
  unfolding outAndChan_inv_def
  apply(rule ext, rename_tac "c")
  apply(case_tac c; simp)
  by (auto simp add: assms f_inv_into_f)

lemma outAndChan_surj: 
    assumes "f Andoutout \<in> range boolConv"
      shows "f \<in> range (outAndChan boolConv)"
  by (metis UNIV_I image_iff assms outAndChan_surj_helper)


lemma outAndChan_inj: assumes "inj boolConv"
  shows "inj (outAndChan boolConv)"
  apply (auto simp add: inj_def)
   by (metis assms outAndChan.simps injD)+


lemma rangecout[simp]:"range (Tsyn o (map_option) \<B>) = ctype cout"
  apply(auto simp add: ctype_def)
 by (metis option.simps(9) range_eqI)




subsection \<open>SBE\<close>
(* Dieses Beispiel ist zeitsychron, daher das "Tsyn" *)
abbreviation "buildAndOutSBE \<equiv> outAndChan (Tsyn o map_option \<B>)" 
(* Die Signatur lautet: "bool option \<times> bool option \<Rightarrow> outAnd \<Rightarrow> M"
    Das "option" kommt aus der Zeit. "None" = keine Nachricht *)


lemma buildandin_ctype: "buildAndOutSBE a c \<in> ctype (Rep c)"
  apply(cases c; cases a)
  by(auto simp add: ctype_def)


lemma buildandin_inj: "inj buildAndOutSBE"
  apply(rule outAndChan_inj)
  by simp


lemma buildandin_range: "range (\<lambda>a. buildAndOutSBE a c) = ctype (Rep c)"
  apply(cases c)
  apply(auto simp add: image_iff ctype_def)
  by (metis option.simps(9))+

lemma buildandin_surj: assumes "\<And>c. sbe c \<in> ctype (Rep c)"
  shows "sbe \<in> range buildAndOutSBE"
  apply(rule outAndChan_surj)
   apply (metis Andoutout_rep assms rangecout) (* Die metis-Sachen kann man bestimmt in einen 1-Zeiler umwandeln *)
  done



interpretation andOutSBE: sbeGen "buildAndOutSBE"
  apply(unfold_locales)
  apply(simp add: buildandin_ctype)
  apply (simp add: buildandin_inj)
  apply (simp add: buildandin_surj)
  by simp


subsection \<open>SB\<close>

abbreviation "buildAndOutSB \<equiv> outAndChan (Rep_cfun (smap (Tsyn o map_option \<B>)))" 

lemma buildAndOutSB_ctype: "sValues\<cdot>(buildAndOutSB a c) \<subseteq> ctype (Rep c)"
  apply(cases c; cases a)
  by (auto simp add: ctype_def smap_sValues)

lemma buildAndOutSB_inj: "inj buildAndOutSB"
  apply(rule outAndChan_inj, rule smap_inj)
  by (simp)

lemma smap_rang2values: assumes "sValues\<cdot>s \<subseteq> range f"
    shows "s \<in> range (Rep_cfun (smap f))"
  using assms smap_well by force

lemma buildAndOutSB_surj: assumes "sb_well sb"
  shows "sb \<in> range buildAndOutSB"
  apply(rule outAndChan_surj; rule smap_rang2values; rule sbwellD)
  apply (simp_all add: assms)
  using rangecout apply simp
  done



interpretation andOutSB: sbGen "buildAndOutSB"
  apply(unfold_locales)
  apply (simp add: buildAndOutSB_ctype) 
  apply (simp add: buildAndOutSB_inj)
  by (simp add: buildAndOutSB_surj)


end