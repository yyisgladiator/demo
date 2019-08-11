(*<*)(*:maxLineLen=68:*)
theory SPFcomp

imports bundle.SB SPF
begin
(*>*)
section \<open>General Composition Operators\<close>

text\<open>Composing two components\<close> 

subsection \<open>General composition of SPFs\<close>

(*cbot werden nicht verbunden; cbot können nur bei der eingabe 
vorkommen (bei der ausgabe nicht vorgesehen, siehe BDD92 Kap3.4)*)

definition genComp::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) \<rightarrow> 'E\<^sup>\<Omega> \<rightarrow> 'F\<^sup>\<Omega>"
  where "genComp \<equiv> \<Lambda> spf1 spf2 sbIn . 
          fix\<cdot>(\<Lambda> sbOut. spf1\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut) \<uplus>\<^sub>\<star> spf2\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut))"

abbreviation genComp_abbr (infixr "\<otimes>\<^sub>\<star>" 70) where 
"spf1 \<otimes>\<^sub>\<star> spf2 \<equiv> genComp\<cdot>spf1\<cdot>spf2"

abbreviation genComp_nomabbr::
"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>)
 \<Rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>)" 
(infixr "\<otimes>" 70) where "spf1 \<otimes> spf2 \<equiv> genComp\<cdot>spf1\<cdot>spf2"


lemma spfcomp_eql[simp]: "genComp\<cdot>f\<cdot>g = f"
  apply(simp add: genComp_def)
  apply(rule cfun_eqI, simp)
  apply(rule fix_eqI)
  by simp+

theorem spfcomp_commut: 
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
  and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom (TYPE ('fOut)) \<inter> chDom (TYPE ('gOut)) = {}"
  shows  "genComp\<cdot>f\<cdot>g = genComp\<cdot>g\<cdot>f"
  apply(rule cfun_eqI)
  apply(simp add: genComp_def)
  apply(rule arg_cong [of _ _ "Rep_cfun fix"])
  apply(rule cfun_eqI, simp)
  apply(rule ubunion_commu)
  by(simp add: assms)

lemma spfcomp_eqr[simp]:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
  and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom (TYPE ('fOut)) \<inter> chDom (TYPE ('gOut)) = {}"
  shows "genComp\<cdot>f\<cdot>g = g"
  apply(subst spfcomp_commut)
  by(simp add: assms)+

lemma "genComp\<cdot>f\<cdot>g = spfConvert\<cdot>(f \<otimes> g)"
  apply(subst genComp_def)
  apply(simp add: spfConvert_def)
  apply(rule cfun_eqI, simp)
  apply(rule fix_eqI)
  apply auto
  apply(rule sb_eqI)
  oops 

theorem spfcomp_belowI: 
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
  and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  and out::"('fOut \<union> 'gOut)\<^sup>\<Omega>"  
  assumes "chDom (TYPE ('fOut)) \<inter> chDom (TYPE ('gOut)) = {}"
  and "f\<cdot>(sb \<uplus>\<^sub>\<star> out) = (out\<star>\<^sub>1)"
  and "g\<cdot>(sb \<uplus>\<^sub>\<star> out) = (out\<star>\<^sub>2)"
  shows "((f\<otimes>g)\<cdot>sb) \<sqsubseteq> out"
  apply(subst genComp_def)
  apply(simp add: spfConvert_def)
  apply(rule fix_least)
  by(insert assms, simp)

theorem spfcomp_eqI:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
  and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  and out::"('fOut \<union> 'gOut)\<^sup>\<Omega>"
  assumes "chDom (TYPE ('fOut)) \<inter> chDom (TYPE ('gOut)) = {}"
  and "f\<cdot>(sb \<uplus>\<^sub>\<star> out) =(out\<star>\<^sub>1)"
  and "g\<cdot>(sb \<uplus>\<^sub>\<star> out) = (out\<star>\<^sub>2)"
  and "\<And>z. f\<cdot>(sb \<uplus>\<^sub>\<star> z) = (z\<star>\<^sub>1) \<Longrightarrow> g\<cdot>(sb \<uplus>\<^sub>\<star> z) = (z\<star>\<^sub>2) \<Longrightarrow> out \<sqsubseteq> z"
  shows "((f\<otimes>g)\<cdot>sb) = out"
  apply(subst genComp_def)
  apply(simp add: spfConvert_def)
  apply(rule fix_eqI)
  apply (insert assms,simp_all)
  by (metis assms(1) sbunion_fst sbunion_snd)

lemma spfcomp2gencomp  [simp]: 
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
  and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom (TYPE ('fOut)) \<inter> chDom (TYPE ('a)) = {}"
  assumes "chDom (TYPE ('gOut)) \<inter> chDom (TYPE ('a)) = {}"
  shows "spfConvert\<cdot>(f \<otimes> g) = (genComp\<cdot>f\<cdot>g::('a\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>))"
  apply(rule cfun_eqI)
  apply(simp add: spfConvert_def genComp_def)
  apply(rule fix_eqI [symmetric]; auto)
  apply(rule sb_eqI; auto)
  oops


lemma spfcomp_surj_h: 
  fixes  f :: "(('a \<union> 'b) - ('c \<union> 'd))\<^sup>\<Omega> \<rightarrow> ('c \<union> 'd)\<^sup>\<Omega>"
  assumes "chDom (TYPE ('c)) \<inter> chDom (TYPE ('d)) = {}"
  shows "(spfConvert\<cdot>(f)) \<otimes> (spfConvert\<cdot>(f)) = f"
  apply(subst genComp_def)
  apply(simp add: spfConvert_def)
  apply(rule cfun_eqI, simp)
  apply(rule fix_eqI)
  apply auto
  apply(rule sbunion_eqI)
  apply(rule cfun_arg_eqI)+
  subgoal 
  apply(rule sb_rep_eqI)
  apply(simp_all add: sbgetch_insert2 assms Abs_sb_inverse sbunion_rep_eq)
  apply(simp add: sbconvert_insert)
  apply(subst sbgetch_insert,auto)
  apply(simp_all add: Abs_sb_inverse)
  oops
  (* TODO: Wichtig *)
(* Ist aber sehr komisch, gilt glaube ich nicht ... *)


(* TODO: Move to SB.thy *)



definition %invisible fstcomplete:: "((('a \<union> 'b) - ('c \<union> 'd))\<^sup>\<Omega> \<rightarrow> ('c \<union> 'd)\<^sup>\<Omega>) \<rightarrow> 'a\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>" where
"fstcomplete \<equiv> \<Lambda> f input. undefined"

lemma spfcomp_surj:
  fixes  h :: "(('a \<union> 'b) - ('c \<union> 'd))\<^sup>\<Omega> \<rightarrow> ('c \<union> 'd)\<^sup>\<Omega>"
  assumes "chDom (TYPE ('c)) \<inter> chDom (TYPE ('d)) = {}"
  shows"\<exists>f g. f \<otimes> g = h"
  apply(subst genComp_def)
  apply(simp add: spfConvert_def)
  apply rule+
  apply(rule cfun_eqI, simp)
  apply(rule fix_eqI)
  apply auto
  apply(rule sbunion_eqI)
  subgoal

  oops

lemma sercomp:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
  and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE ('fOut) \<subseteq> chDom TYPE ('gIn)"
  and "chDom TYPE ('fOut) \<inter> chDom TYPE ('gOut) = {}"
  and "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
  and "chDom TYPE('fOut) \<inter> chDom TYPE('fIn) = {}"
  shows "(f \<otimes> g)\<cdot>sb = f\<cdot>(sb\<star>) \<uplus> g\<cdot>(f\<cdot>(sb\<star>)\<star>)"
  oops

lemma parcomp:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
  and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE ('fOut) \<inter> chDom TYPE ('gIn) = {}"
  and "chDom TYPE ('fOut) \<inter> chDom TYPE ('gOut) = {}"
  and "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
  and "chDom TYPE('fOut) \<inter> chDom TYPE('fIn) = {}"
  shows "(f \<otimes> g)\<cdot>sb = f\<cdot>(sb\<star>) \<uplus> g\<cdot>(sb\<star>)"
  oops

section\<open>General Composition of SPSs\<close>

definition spsComp::
"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set 
\<Rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>) set"  where
"spsComp F G = {f \<otimes> g | f g. f\<in>F \<and> g\<in>G }"

lemma fixes P::"'I1\<^sup>\<Omega> \<Rightarrow> 'O1\<^sup>\<Omega> \<Rightarrow> bool"
        and H::"'I2\<^sup>\<Omega> \<Rightarrow> 'O2\<^sup>\<Omega> \<Rightarrow> bool"
      assumes "chDom (TYPE ('O1)) \<inter> chDom (TYPE ('O2)) = {}"
      shows  "spsComp {p . \<forall>sb. P sb (p\<cdot>sb)} {h . \<forall>sb. H sb (h\<cdot>sb)} =   
            {g. \<forall>sb. 
                  let all = sb \<uplus> g\<cdot>sb in 
                    P (all\<star>) (all\<star>) \<and> H (all\<star>) (all\<star>)
            }"
  apply (auto simp add: spsComp_def Let_def)
  oops
(*  by (metis spfcomp2gencomp spfcomp_eql spfcomp_eqr spfcomp_surj) *)
(* Gegenbeispiel ... soweit ich sehe: 
    P = H = "ist schwachkausal"
    bleibt nicht unter der feedbackkomposition erhalten *)
(*<*)
end
(*>*)