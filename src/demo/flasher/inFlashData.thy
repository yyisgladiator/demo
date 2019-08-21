theory inFlashData

imports Data_inc
begin

typedef inFlash="{cin1}"
  by auto


instance inFlash::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_inFlash typedef_finite_UNIV by fastforce

instantiation inFlash::somechan
begin
definition Rep_inFlash_def:"Rep = Rep_inFlash"

lemma repflash_range[simp]:"range (Rep::inFlash\<Rightarrow>channel) = {cin1}"
  apply(subst Rep_inFlash_def)
  using type_definition.Rep_range type_definition_inFlash by fastforce

instance
  apply(intro_classes)
  apply clarsimp
  unfolding Rep_inFlash_def by (meson Rep_inFlash_inject injI)
end

lemma inFlash_chdom[simp]: "chDom TYPE (inFlash) = {cin1}"
  by (simp add: somechandom)



section \<open>Constructors\<close>

definition "Flashinin1 \<equiv> Abs_inFlash cin1"

free_constructors inFlash for Flashinin1
  apply auto?  (* TODO: kann man das "auto" entfernen? *)
  unfolding Flashinin1_def
  apply (metis Rep_inFlash Rep_inFlash_inverse empty_iff insert_iff)
  apply (simp add: Abs_inFlash_inject)?
  done

lemma Flashinin1_rep [simp]: "Rep Flashinin1 = cin1"
  unfolding Rep_inFlash_def Flashinin1_def
  by (simp add: Abs_inFlash_inverse)



section \<open>Preperation for locale instantiation\<close>

(* Tuple:
      1. Value should go to port cin1. It is of type "bool"
*)

(* The first parameter is the converter from user-type (here bool) to "M" 

  for every type in the tuple such a function must be in the parameter. So if the tuple
  would consist of (nat\<times>bool) there are 2 converters required *)

fun inFlashChan::"('bool \<Rightarrow> 'a) \<Rightarrow> ('bool) \<Rightarrow> inFlash \<Rightarrow> 'a" where
"inFlashChan boolConv  (port_cin1) Flashinin1 = boolConv port_cin1" 

(* Helper Function for lemmata (mostly surj). Should be hidden from the user! *)
definition inFlashChan_inv::"('bool \<Rightarrow> 'a) \<Rightarrow> (inFlash \<Rightarrow> 'a) \<Rightarrow> ('bool)" where
"inFlashChan_inv boolConv f = ((inv boolConv) (f Flashinin1))" 

lemma inFlashChan_surj_helper: 
    assumes "f Flashinin1 \<in> range boolConv"
  shows "inFlashChan boolConv (inFlashChan_inv boolConv f) = f"
  unfolding inFlashChan_inv_def
  apply(rule ext, rename_tac "c")
  apply(case_tac c; simp)
  by (auto simp add: assms f_inv_into_f)

lemma inFlashChan_surj: 
    assumes "f Flashinin1 \<in> range boolConv"
      shows "f \<in> range (inFlashChan boolConv)"
  by (metis UNIV_I image_iff assms inFlashChan_surj_helper)


lemma inFlashChan_inj: assumes "inj boolConv"
  shows "inj (inFlashChan boolConv)"
  apply (auto simp add: inj_def)
   by (metis assms inFlashChan.simps injD)+


lemma rangecin1[simp]:"range (Tsyn o (map_option) \<B>) = ctype cin1"
  apply(auto simp add: ctype_def)
 by (metis option.simps(9) range_eqI)




subsection \<open>SBE\<close>
(* Dieses Beispiel ist zeitsychron, daher das "Tsyn" *)
abbreviation "buildFlashInSBE \<equiv> inFlashChan (Tsyn o map_option \<B>)" 
(* Die Signatur lautet: "bool option \<times> bool option \<Rightarrow> inFlash \<Rightarrow> M"
    Das "option" kommt aus der Zeit. "None" = keine Nachricht *)


lemma buildandin_ctype: "buildFlashInSBE a c \<in> ctype (Rep c)"
  apply(cases c; cases a)
  by(auto simp add: ctype_def)


lemma buildandin_inj: "inj buildFlashInSBE"
  apply(rule inFlashChan_inj)
  by simp


lemma buildandin_range: "range (\<lambda>a. buildFlashInSBE a c) = ctype (Rep c)"
  apply(cases c)
  apply(auto simp add: image_iff ctype_def)
  by (metis option.simps(9))+

lemma buildandin_surj: assumes "\<And>c. sbe c \<in> ctype (Rep c)"
  shows "sbe \<in> range buildFlashInSBE"
  apply(rule inFlashChan_surj)
   apply (metis Flashinin1_rep assms rangecin1) (* Die metis-Sachen kann man bestimmt in einen 1-Zeiler umwandeln *)
  done



interpretation inFlashSBE: sbeGen "buildFlashInSBE"
  apply(unfold_locales)
  apply(simp add: buildandin_ctype)
  apply (simp add: buildandin_inj)
  apply (simp add: buildandin_surj)
  by simp


subsection \<open>SB\<close>

abbreviation "buildFlashInSB \<equiv> inFlashChan (Rep_cfun (smap (Tsyn o map_option \<B>)))" 

lemma buildFlashInSB_ctype: "sValues\<cdot>(buildFlashInSB a c) \<subseteq> ctype (Rep c)"
  apply(cases c; cases a)
  by (auto simp add: ctype_def smap_sValues)

lemma buildFlashInSB_inj: "inj buildFlashInSB"
  apply(rule inFlashChan_inj, rule smap_inj)
  by (simp)

lemma smap_rang2values: assumes "sValues\<cdot>s \<subseteq> range f"
    shows "s \<in> range (Rep_cfun (smap f))"
  using assms smap_well by force

lemma buildFlashInSB_surj: assumes "sb_well sb"
  shows "sb \<in> range buildFlashInSB"
  apply(rule inFlashChan_surj; rule smap_rang2values; rule sbwellD)
  apply (simp_all add: assms)
  using rangecin1 apply simp
  done



interpretation inFlashSB: sbGen "buildFlashInSB"
  apply(unfold_locales)
  apply (simp add: buildFlashInSB_ctype) 
  apply (simp add: buildFlashInSB_inj)
  by (simp add: buildFlashInSB_surj)



end