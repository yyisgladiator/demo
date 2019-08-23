theory outFlashData

imports Data_inc
begin

typedef outFlash="{cout,cintern}"
  by auto


instance outFlash::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_outFlash typedef_finite_UNIV by fastforce

instantiation outFlash::somechan
begin
definition Rep_outFlash_def: "Rep = Rep_outFlash"

lemma repand_range[simp]: "range (Rep::outFlash \<Rightarrow> channel) = {cout,cintern}"
  apply(subst Rep_outFlash_def)
  using type_definition.Rep_range type_definition_outFlash by fastforce

instance
  apply(intro_classes)
  apply clarsimp
  unfolding Rep_outFlash_def by (meson Rep_outFlash_inject injI)
end

lemma outFlash_chdom[simp]: "chDom TYPE (outFlash) = {cout,cintern}"
  by (simp add: somechandom)



section \<open>Constructors\<close>

definition "Flashout \<equiv> Abs_outFlash cout"
definition "Flashin2 \<equiv> Abs_outFlash cintern"

free_constructors outFlash for Flashout | Flashin2
  apply auto?  (* TODO: kann man das "auto" entfernen? *)
  unfolding Flashout_def Flashin2_def
  apply (metis Rep_outFlash Rep_outFlash_inverse empty_iff insert_iff)
  apply (simp add: Abs_outFlash_inject)?
  done

lemma flashout_rep [simp]: "Rep Flashout = cout"
  unfolding Rep_outFlash_def Flashout_def
  by (simp add: Abs_outFlash_inverse)

lemma flashin2_rep [simp]: "Rep Flashin2 = cintern"
  unfolding Rep_outFlash_def Flashin2_def
  by (simp add: Abs_outFlash_inverse)


section \<open>Preperation for locale instantiation\<close>

(* Tuple:
      1. Value should go to port c1. It is of type "bool"
      2. Value should go to port c2. It is of type "bool" 
*)

(* The first parameter is the converter from user-type (here bool) to "M" 

  for every type in the tuple such a function must be in the parameter. So if the tuple
  would consist of (nat\<times>bool) there are 2 converters required *)

fun outFlashChan::"('bool \<Rightarrow> 'a) \<Rightarrow> ('bool\<times>'bool) \<Rightarrow> outFlash \<Rightarrow> 'a" where
"outFlashChan boolConv  (port_c1,   _    ) Flashout = boolConv port_c1" |
"outFlashChan boolConv  (   _   , port_c2) Flashin2 = boolConv port_c2"

(* Helper Function for lemmata (mostly surj). Should be hidden from the user! *)
definition outFlashChan_inv::"('bool \<Rightarrow> 'a) \<Rightarrow> (outFlash \<Rightarrow> 'a) \<Rightarrow> ('bool\<times>'bool)" where
"outFlashChan_inv boolConv f = ((inv boolConv) (f Flashout), (inv boolConv) (f Flashin2))" 

lemma outFlashChan_surj_helper: 
    assumes "f Flashout \<in> range boolConv"
        and "f Flashin2 \<in> range boolConv"
  shows "outFlashChan boolConv (outFlashChan_inv boolConv f) = f"
  unfolding outFlashChan_inv_def
  apply(rule ext, rename_tac "c")
  apply(case_tac c; simp)
  by (auto simp add: assms f_inv_into_f)

lemma outFlashChan_surj: 
    assumes "f Flashout \<in> range boolConv"
        and "f Flashin2 \<in> range boolConv"
      shows "f \<in> range (outFlashChan boolConv)"
  by (metis UNIV_I image_iff assms outFlashChan_surj_helper)


lemma outFlashChan_inj: assumes "inj boolConv"
  shows "inj (outFlashChan boolConv)"
  apply (auto simp add: inj_def)
   by (metis assms outFlashChan.simps injD)+


subsection \<open>SBE\<close>
(* Dieses Beispiel ist zeitsychron, daher das "Tsyn" *)
abbreviation "buildFlashOutSBE \<equiv> outFlashChan (Tsyn o map_option \<B>)" 
(* Die Signatur lautet: "bool option \<times> bool option \<Rightarrow> outFlash \<Rightarrow> M"
    Das "option" kommt aus der Zeit. "None" = keine Nachricht *)



lemma buildflashout_ctype: "buildFlashOutSBE a c \<in> ctype (Rep c)"
  apply(cases c; cases a)
  by(auto simp add: ctype_def)


lemma buildflashout_inj: "inj buildFlashOutSBE"
  apply(rule outFlashChan_inj)
  by simp


lemma buildflashout_range: "range (\<lambda>a. buildFlashOutSBE a c) = ctype (Rep c)"
  apply(cases c)
  apply(auto simp add: image_iff ctype_def)
  by (metis option.simps(9))+

lemma buildflashout_surj: assumes "\<And>c. sbe c \<in> ctype (Rep c)"
  shows "sbe \<in> range buildFlashOutSBE"
  apply(rule outFlashChan_surj)
  apply (metis flashout_rep assms rangecout) (* Die metis-Sachen kann man bestimmt in einen 1-Zeiler umwandeln *)
  by (metis flashin2_rep assms rangecintern)



interpretation andInSBE: sbeGen "buildFlashOutSBE"
  apply(unfold_locales)
  apply(simp add: buildflashout_ctype)
  apply (simp add: buildflashout_inj)
  apply (simp add: buildflashout_surj)
  by simp


subsection \<open>SB\<close>

abbreviation "buildFlashOutSB \<equiv> outFlashChan (Rep_cfun (smap (Tsyn o map_option \<B>)))" 

lemma buildflashoutsb_ctype: "sValues\<cdot>(buildFlashOutSB a c) \<subseteq> ctype (Rep c)"
  apply(cases c; cases a)
  by (auto simp add: ctype_def smap_sValues)

lemma buildflashoutsb_inj: "inj buildFlashOutSB"
  apply(rule outFlashChan_inj, rule smap_inj)
  by (simp)

lemma smap_rang2values: assumes "sValues\<cdot>s \<subseteq> range f"
    shows "s \<in> range (Rep_cfun (smap f))"
  using assms smap_well by force

lemma buildflashoutsb_surj: assumes "sb_well sb"
  shows "sb \<in> range buildFlashOutSB"
  apply(rule outFlashChan_surj; rule smap_rang2values; rule sbwellD)
  apply (simp_all add: assms)
  using rangecout apply simp
  using rangecintern apply simp
  done



interpretation andInSB: sbGen "buildFlashOutSB"
  apply(unfold_locales)
  apply (simp add: buildflashoutsb_ctype) 
  apply (simp add: buildflashoutsb_inj)
  by (simp add: buildflashoutsb_surj)

end
