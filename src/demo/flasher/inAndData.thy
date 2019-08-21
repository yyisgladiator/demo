theory inAndData

imports Data_inc
begin


typedef inAnd="{cin1,cin2}"
  by auto



instance inAnd::finite
  apply (intro_classes)
  using type_definition.Abs_image type_definition_inAnd typedef_finite_UNIV by fastforce

instantiation inAnd::somechan
begin
definition Rep_inAnd_def: "Rep = Rep_inAnd"

lemma repand_range[simp]: "range (Rep::inAnd \<Rightarrow> channel) = {cin1,cin2}"
  apply(subst Rep_inAnd_def)
  using type_definition.Rep_range type_definition_inAnd by fastforce

instance
  apply(intro_classes)
   apply clarsimp
  unfolding Rep_inAnd_def by (meson Rep_inAnd_inject injI)
end

lemma inand_chdom[simp]: "chDom TYPE (inAnd) = {cin1, cin2}"
  by (simp add: somechandom)



section \<open>Constructors\<close>

definition "Andin1 \<equiv> Abs_inAnd cin1"
definition "Andin2 \<equiv> Abs_inAnd cin2"

free_constructors inAnd for Andin1 | Andin2
  apply auto?  (* TODO: kann man das "auto" entfernen? *)
  unfolding Andin1_def Andin2_def
  apply (metis Rep_inAnd Rep_inAnd_inverse empty_iff insert_iff)
  apply (simp add: Abs_inAnd_inject)?
  done  (* Die "?" sind da, weil der Beweis für 1-port Datentypen anders aussieht. 
  Ich kann die "Eisbach" Dokumentation empfehlen! Dort sind methoden beschrieben, um Beweise zu automatisieren *)

lemma andin1_rep [simp]: "Rep Andin1 = cin1"
  unfolding Rep_inAnd_def Andin1_def
  by (simp add: Abs_inAnd_inverse)

lemma andin2_rep [simp]: "Rep Andin2 = cin2"
  unfolding Rep_inAnd_def Andin2_def
  by (simp add: Abs_inAnd_inverse)




section \<open>Preperation for locale instantiation\<close>

(* Tuple:
      1. Value should go to port c1. It is of type "bool"
      2. Value should go to port c2. It is of type "bool" 
*)

(* The first parameter is the converter from user-type (here bool) to "M" 

  for every type in the tuple such a function must be in the parameter. So if the tuple
  would consist of (nat\<times>bool) there are 2 converters required *)

fun inAndChan::"('bool \<Rightarrow> 'a) \<Rightarrow> ('bool\<times>'bool) \<Rightarrow> inAnd \<Rightarrow> 'a" where
"inAndChan boolConv  (port_c1,   _    ) Andin1 = boolConv port_c1" |
"inAndChan boolConv  (   _   , port_c2) Andin2 = boolConv port_c2"

(* Helper Function for lemmata (mostly surj). Should be hidden from the user! *)
definition inAndChan_inv::"('bool \<Rightarrow> 'a) \<Rightarrow> (inAnd \<Rightarrow> 'a) \<Rightarrow> ('bool\<times>'bool)" where
"inAndChan_inv boolConv f = ((inv boolConv) (f Andin1), (inv boolConv) (f Andin2))" 

lemma inAndChan_surj_helper: 
    assumes "f Andin1 \<in> range boolConv"
        and "f Andin2 \<in> range boolConv"
  shows "inAndChan boolConv (inAndChan_inv boolConv f) = f"
  unfolding inAndChan_inv_def
  apply(rule ext, rename_tac "c")
  apply(case_tac c; simp)
  by (auto simp add: assms f_inv_into_f)

lemma inAndChan_surj: 
    assumes "f Andin1 \<in> range boolConv"
        and "f Andin2 \<in> range boolConv"
      shows "f \<in> range (inAndChan boolConv)"
  by (metis UNIV_I image_iff assms inAndChan_surj_helper)


lemma inAndChan_inj: assumes "inj boolConv"
  shows "inj (inAndChan boolConv)"
  apply (auto simp add: inj_def)
   by (metis assms inAndChan.simps injD)+

subsection \<open>SBE\<close>
(* Dieses Beispiel ist zeitsychron, daher das "Tsyn" *)
abbreviation "buildAndInSBE \<equiv> inAndChan (Tsyn o map_option \<B>)" 
(* Die Signatur lautet: "bool option \<times> bool option \<Rightarrow> inAnd \<Rightarrow> M"
    Das "option" kommt aus der Zeit. "None" = keine Nachricht *)



lemma buildandin_ctype: "buildAndInSBE a c \<in> ctype (Rep c)"
  apply(cases c; cases a)
  by(auto simp add: ctype_def)


lemma buildandin_inj: "inj buildAndInSBE"
  apply(rule inAndChan_inj)
  by simp


lemma buildandin_range: "range (\<lambda>a. buildAndInSBE a c) = ctype (Rep c)"
  apply(cases c)
  apply(auto simp add: image_iff ctype_def)
  by (metis option.simps(9))+

lemma buildandin_surj: assumes "\<And>c. sbe c \<in> ctype (Rep c)"
  shows "sbe \<in> range buildAndInSBE"
  apply(rule inAndChan_surj)
   apply (metis andin1_rep assms rangecin1) (* Die metis-Sachen kann man bestimmt in einen 1-Zeiler umwandeln *)
  by (metis andin2_rep assms rangecin2)



interpretation andInSBE: sbeGen "buildAndInSBE"
  apply(unfold_locales)
  apply(simp add: buildandin_ctype)
  apply (simp add: buildandin_inj)
  apply (simp add: buildandin_surj)
  by simp


subsection \<open>SB\<close>

abbreviation "buildAndinSB \<equiv> inAndChan (Rep_cfun (smap (Tsyn o map_option \<B>)))" 

lemma buildandinsb_ctype: "sValues\<cdot>(buildAndinSB a c) \<subseteq> ctype (Rep c)"
  apply(cases c; cases a)
  by (auto simp add: ctype_def smap_sValues)

lemma buildandinsb_inj: "inj buildAndinSB"
  apply(rule inAndChan_inj, rule smap_inj)
  by (simp)

lemma smap_rang2values: assumes "sValues\<cdot>s \<subseteq> range f"
    shows "s \<in> range (Rep_cfun (smap f))"
  using assms smap_well by force

lemma buildandinsb_surj: assumes "sb_well sb"
  shows "sb \<in> range buildAndinSB"
  apply(rule inAndChan_surj; rule smap_rang2values; rule sbwellD)
  apply (simp_all add: assms)
  using rangecin1 apply simp
  using rangecin2 apply simp
  done



interpretation andInSB: sbGen "buildAndinSB"
  apply(unfold_locales)
  apply (simp add: buildandinsb_ctype) 
  apply (simp add: buildandinsb_inj)
  by (simp add: buildandinsb_surj)


end