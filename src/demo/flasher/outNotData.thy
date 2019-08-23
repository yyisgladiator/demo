theory outNotData

imports Data_inc
  begin

typedef outNot = "{cintern}"
  by auto


instance outNot::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_outNot typedef_finite_UNIV by fastforce

instantiation outNot::somechan
begin
definition Rep_outNot_def: "Rep = Rep_outNot"

lemma repand_range[simp]: "range (Rep::outNot \<Rightarrow> channel) = {cintern}"
  apply(subst Rep_outNot_def)
  using type_definition.Rep_range type_definition_outNot by fastforce

instance
  apply(intro_classes)
  apply clarsimp
  unfolding Rep_outNot_def by (meson Rep_outNot_inject injI)
end

lemma outNot_chdom[simp]: "chDom TYPE (outNot) = {cintern}"
  by (simp add: somechandom)



section \<open>Constructors\<close>

definition "Notout \<equiv> Abs_outNot cintern"

free_constructors outNot for Notout
  apply auto?  (* TODO: kann man das "auto" entfernen? *)
  unfolding Notout_def
  apply (metis Rep_outNot Rep_outNot_inverse empty_iff insert_iff)
  apply (simp add: Abs_outNot_inject)?
  done

lemma notout_rep [simp]: "Rep Notout = cintern"
  unfolding Rep_outNot_def Notout_def
  by (simp add: Abs_outNot_inverse)



section \<open>Preperation for locale instantiation\<close>

(* Tuple:
      1. Value should go to port cintern. It is of type "bool"
*)

(* The first parameter is the converter from user-type (here bool) to "M" 

  for every type in the tuple such a function must be in the parameter. So if the tuple
  would consist of (nat\<times>bool) there are 2 converters required *)

fun outNotChan::"('bool \<Rightarrow> 'a) \<Rightarrow> ('bool) \<Rightarrow> outNot \<Rightarrow> 'a" where
"outNotChan boolConv  (port_cintern) Notout = boolConv port_cintern" 

(* Helper Function for lemmata (mostly surj). Should be hidden from the user! *)
definition outNotChan_inv::"('bool \<Rightarrow> 'a) \<Rightarrow> (outNot \<Rightarrow> 'a) \<Rightarrow> ('bool)" where
"outNotChan_inv boolConv f = ((inv boolConv) (f Notout))" 

lemma outNotChan_surj_helper: 
    assumes "f Notout \<in> range boolConv"
  shows "outNotChan boolConv (outNotChan_inv boolConv f) = f"
  unfolding outNotChan_inv_def
  apply(rule ext, rename_tac "c")
  apply(case_tac c; simp)
  by (auto simp add: assms f_inv_into_f)

lemma outNotChan_surj: 
    assumes "f Notout \<in> range boolConv"
      shows "f \<in> range (outNotChan boolConv)"
  by (metis UNIV_I image_iff assms outNotChan_surj_helper)


lemma outNotChan_inj: assumes "inj boolConv"
  shows "inj (outNotChan boolConv)"
  apply (auto simp add: inj_def)
   by (metis assms outNotChan.simps injD)+


subsection \<open>SBE\<close>
(* Dieses Beispiel ist zeitsychron, daher das "Tsyn" *)
abbreviation "buildNotOutSBE \<equiv> outNotChan (Tsyn o map_option \<B>)" 
(* Die Signatur lautet: "bool option \<times> bool option \<Rightarrow> outNot \<Rightarrow> M"
    Das "option" kommt aus der Zeit. "None" = keine Nachricht *)


lemma buildandin_ctype: "buildNotOutSBE a c \<in> ctype (Rep c)"
  apply(cases c; cases a)
  by(auto simp add: ctype_def)


lemma buildandin_inj: "inj buildNotOutSBE"
  apply(rule outNotChan_inj)
  by simp


lemma buildandin_range: "range (\<lambda>a. buildNotOutSBE a c) = ctype (Rep c)"
  apply(cases c)
  apply(auto simp add: image_iff ctype_def)
  by (metis option.simps(9))+

lemma buildandin_surj: assumes "\<And>c. sbe c \<in> ctype (Rep c)"
  shows "sbe \<in> range buildNotOutSBE"
  apply(rule outNotChan_surj)
   apply (metis notout_rep assms rangecintern) (* Die metis-Sachen kann man bestimmt in einen 1-Zeiler umwandeln *)
  done



interpretation notOutSBE: sbeGen "buildNotOutSBE"
  apply(unfold_locales)
  apply(simp add: buildandin_ctype)
  apply (simp add: buildandin_inj)
  apply (simp add: buildandin_surj)
  by simp


subsection \<open>SB\<close>

abbreviation "buildNotOutSB \<equiv> outNotChan (Rep_cfun (smap (Tsyn o map_option \<B>)))" 

lemma buildNotOutSB_ctype: "sValues\<cdot>(buildNotOutSB a c) \<subseteq> ctype (Rep c)"
  apply(cases c; cases a)
  by (auto simp add: ctype_def smap_sValues)

lemma buildNotOutSB_inj: "inj buildNotOutSB"
  apply(rule outNotChan_inj, rule smap_inj)
  by (simp)

lemma smap_rang2values: assumes "sValues\<cdot>s \<subseteq> range f"
    shows "s \<in> range (Rep_cfun (smap f))"
  using assms smap_well by force

lemma buildNotOutSB_surj: assumes "sb_well sb"
  shows "sb \<in> range buildNotOutSB"
  apply(rule outNotChan_surj; rule smap_rang2values; rule sbwellD)
  apply (simp_all add: assms)
  using rangecintern apply simp
  done



interpretation notOutSB: sbGen "buildNotOutSB"
  apply(unfold_locales)
  apply (simp add: buildNotOutSB_ctype) 
  apply (simp add: buildNotOutSB_inj)
  by (simp add: buildNotOutSB_surj)


end