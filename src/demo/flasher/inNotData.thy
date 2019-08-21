theory inNotData

imports Data_inc
  begin

typedef inNot="{cout}"
  by auto



instance inNot::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_inNot typedef_finite_UNIV by fastforce

instantiation inNot::somechan
begin
definition Rep_inNot_def: "Rep = Rep_inNot"

lemma repnot_range[simp]: "range (Rep::inNot \<Rightarrow> channel) = {cout}"
  apply(subst Rep_inNot_def)
  using type_definition.Rep_range type_definition_inNot by fastforce

instance
  apply(intro_classes)
  apply clarsimp
  unfolding Rep_inNot_def by (meson Rep_inNot_inject injI)
end

lemma inNot_chdom[simp]: "chDom TYPE (inNot) = {cout}"
  by (simp add: somechandom)



section \<open>Constructors\<close>

definition "Notin \<equiv> Abs_inNot cout"

free_constructors inNot for Notin
  apply auto?  (* TODO: kann man das "auto" entfernen? *)
  unfolding Notin_def
  apply (metis Rep_inNot Rep_inNot_inverse empty_iff insert_iff)
  apply (simp add: Abs_inNot_inject)?
  done

lemma notin_rep [simp]: "Rep Notin = cout"
  unfolding Rep_inNot_def Notin_def
  by (simp add: Abs_inNot_inverse)



section \<open>Preperation for locale instantiation\<close>

(* Tuple:
      1. Value should go to port cout. It is of type "bool"
*)

(* The first parameter is the converter from user-type (here bool) to "M" 

  for every type in the tuple such a function must be in the parameter. So if the tuple
  would consist of (nat\<times>bool) there are 2 converters required *)

fun inNotChan::"('bool \<Rightarrow> 'a) \<Rightarrow> ('bool) \<Rightarrow> inNot \<Rightarrow> 'a" where
"inNotChan boolConv  (port_cout) Notin = boolConv port_cout" 

(* Helper Function for lemmata (mostly surj). Should be hidden from the user! *)
definition inNotChan_inv::"('bool \<Rightarrow> 'a) \<Rightarrow> (inNot \<Rightarrow> 'a) \<Rightarrow> ('bool)" where
"inNotChan_inv boolConv f = ((inv boolConv) (f Notin))" 

lemma inNotChan_surj_helper: 
    assumes "f Notin \<in> range boolConv"
  shows "inNotChan boolConv (inNotChan_inv boolConv f) = f"
  unfolding inNotChan_inv_def
  apply(rule ext, rename_tac "c")
  apply(case_tac c; simp)
  by (auto simp add: assms f_inv_into_f)

lemma inNotChan_surj: 
    assumes "f Notin \<in> range boolConv"
      shows "f \<in> range (inNotChan boolConv)"
  by (metis UNIV_I image_iff assms inNotChan_surj_helper)


lemma inNotChan_inj: assumes "inj boolConv"
  shows "inj (inNotChan boolConv)"
  apply (auto simp add: inj_def)
   by (metis assms inNotChan.simps injD)+


lemma rangecout[simp]:"range (Tsyn o (map_option) \<B>) = ctype cout"
  apply(auto simp add: ctype_def)
 by (metis option.simps(9) range_eqI)




subsection \<open>SBE\<close>
(* Dieses Beispiel ist zeitsychron, daher das "Tsyn" *)
abbreviation "buildNotInSBE \<equiv> inNotChan (Tsyn o map_option \<B>)" 
(* Die Signatur lautet: "bool option \<times> bool option \<Rightarrow> inNot \<Rightarrow> M"
    Das "option" kommt aus der Zeit. "None" = keine Nachricht *)


lemma buildnotin_ctype: "buildNotInSBE a c \<in> ctype (Rep c)"
  apply(cases c; cases a)
  by(auto simp add: ctype_def)


lemma buildnotin_inj: "inj buildNotInSBE"
  apply(rule inNotChan_inj)
  by simp


lemma buildnotin_range: "range (\<lambda>a. buildNotInSBE a c) = ctype (Rep c)"
  apply(cases c)
  apply(auto simp add: image_iff ctype_def)
  by (metis option.simps(9))+

lemma buildnotin_surj: assumes "\<And>c. sbe c \<in> ctype (Rep c)"
  shows "sbe \<in> range buildNotInSBE"
  apply(rule inNotChan_surj)
   apply (metis notin_rep assms rangecout) (* Die metis-Sachen kann man bestimmt in einen 1-Zeiler umwandeln *)
  done



interpretation notInSBE: sbeGen "buildNotInSBE"
  apply(unfold_locales)
  apply(simp add: buildnotin_ctype)
  apply (simp add: buildnotin_inj)
  apply (simp add: buildnotin_surj)
  by simp


subsection \<open>SB\<close>

abbreviation "buildNotInSB \<equiv> inNotChan (Rep_cfun (smap (Tsyn o map_option \<B>)))" 

lemma buildNotInSB_ctype: "sValues\<cdot>(buildNotInSB a c) \<subseteq> ctype (Rep c)"
  apply(cases c; cases a)
  by (auto simp add: ctype_def smap_sValues)

lemma buildNotInSB_inj: "inj buildNotInSB"
  apply(rule inNotChan_inj, rule smap_inj)
  by (simp)

lemma smap_rang2values: assumes "sValues\<cdot>s \<subseteq> range f"
    shows "s \<in> range (Rep_cfun (smap f))"
  using assms smap_well by force

lemma buildNotInSB_surj: assumes "sb_well sb"
  shows "sb \<in> range buildNotInSB"
  apply(rule inNotChan_surj; rule smap_rang2values; rule sbwellD)
  apply (simp_all add: assms)
  using rangecout apply simp
  done



interpretation notInSB: sbGen "buildNotInSB"
  apply(unfold_locales)
  apply (simp add: buildNotInSB_ctype) 
  apply (simp add: buildNotInSB_inj)
  by (simp add: buildNotInSB_surj)




end