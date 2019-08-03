theory SPFcomp

imports bundle.SB
begin

section \<open>General composition\<close>

subsection \<open>General composition definition\<close>

(*cbot werden nicht verbunden; cbot können nur bei der eingabe vorkommen (bei der ausgabe nicht vorgesehen, siehe BDD92 Kap3.4)*)
(*now with magic*)
definition genComp :: "('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) \<rightarrow> 'E\<^sup>\<Omega> \<rightarrow> 'F\<^sup>\<Omega>"  where
"genComp \<equiv> \<Lambda> spf1 spf2 sbIn . fix\<cdot>(\<Lambda> sbOut. spf1\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut) \<uplus>\<^sub>\<star> spf2\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut))"

subsection \<open>General composition abbreviation\<close>
abbreviation genComp_abbr ::  "('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) \<Rightarrow> 'E\<^sup>\<Omega> \<rightarrow> 'F\<^sup>\<Omega>" (infixr "\<otimes>\<^sub>\<star>" 70) where 
"spf1 \<otimes>\<^sub>\<star> spf2 \<equiv> genComp\<cdot>spf1\<cdot>spf2"

 (* inifxr \<otimes> ... without magic*)
abbreviation genComp_magicabbr :: "('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) \<Rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>)" (infixr "\<otimes>" 70) where 
"spf1 \<otimes> spf2 \<equiv> genComp\<cdot>spf1\<cdot>spf2"


definition spfConvert::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<rightarrow> ('Ie\<^sup>\<Omega> \<rightarrow> 'Oe\<^sup>\<Omega>)" where
"spfConvert = (\<Lambda> f sb. (f\<cdot>(sb\<star>)\<star>))"   (* TODO: weniger klammern + warnings *)

lemma spfcomp_eql[simp]: "genComp\<cdot>f\<cdot>g = f"
  apply(simp add: genComp_def)
  apply(rule cfun_eqI, simp)
  apply(rule fix_eqI)
  by simp+

lemma sbgetch_empty[simp]: "Rep c\<in>cEmpty \<Longrightarrow> sb \<^enum>\<^sub>\<star> c = \<epsilon>"
  apply(auto simp add: sbGetCh.rep_eq)
  by (metis (full_types)Rep_sb_strict app_strict cnotempty_rule sbtypeepmpty_sbbot)

lemma ubunion_commu:
  fixes sb1 ::"'cs1\<^sup>\<Omega>"
    and sb2 ::"'cs2\<^sup>\<Omega>"
    assumes "chDom (TYPE ('cs1)) \<inter> chDom (TYPE ('cs2)) = {}"
    shows "sb1 \<uplus>\<^sub>\<star> sb2 = ((sb2 \<uplus>\<^sub>\<star> sb1)::'cs3\<^sup>\<Omega>)"
  apply(rule sb_eqI)
  apply(rename_tac c)
  apply(case_tac "Rep c \<in> chDom (TYPE ('cs1))"; case_tac "Rep c \<in> chDom (TYPE ('cs2))"; case_tac "Rep c \<in> chDom (TYPE ('cs3))")
  using assms  by(auto simp add: chDom_def sbGetCh.rep_eq sbunion_rep_eq)

lemma ubunion_fst[simp]:
  fixes sb1 ::"'cs1\<^sup>\<Omega>"
    and sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "chDom (TYPE ('cs2)) \<inter> chDom (TYPE ('cs3)) = {}"
  shows "sb1 \<uplus>\<^sub>\<star> sb2 = (sb1\<star> :: 'cs3\<^sup>\<Omega>)"
  apply(rule sb_eqI)  (* Exakt gleicher beweis wie "ubunion_commu" ... *)
  apply(rename_tac c)
  apply(case_tac "Rep c \<in> chDom (TYPE ('cs1))"; case_tac "Rep c \<in> chDom (TYPE ('cs2))"; case_tac "Rep c \<in> chDom (TYPE ('cs3))")
  apply(case_tac "Rep c \<in> chDom (TYPE ('cs1))"; case_tac "Rep c \<in> chDom (TYPE ('cs2))"; case_tac "Rep c \<in> chDom (TYPE ('cs3))")
  using assms  by(auto simp add: chDom_def sbGetCh.rep_eq sbunion_rep_eq)


(* Solange output disjunkt *)
lemma spfcomp_commut: 
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

lemma spfconvert_eq [simp]: "spfConvert\<cdot>f = f"
  apply(rule cfun_eqI)
  by(simp add: spfConvert_def)

lemma "genComp\<cdot>f\<cdot>g = spfConvert\<cdot>(f \<otimes> g)"
  apply(subst genComp_def)
  apply(simp add: spfConvert_def)
  apply(rule cfun_eqI, simp)
  apply(rule fix_eqI)
   apply auto
  apply(rule sb_eqI)
  oops 

lemma chdom_in: fixes c::"'cs"
  assumes "chDom TYPE('cs) \<noteq> {}"
    shows "Rep c \<in> chDom TYPE('cs)"
  by (metis Diff_eq_empty_iff Diff_triv assms chDom_def chan_botsingle rangeI)

lemma ubunion_id[simp]: "out\<star>\<^sub>1 \<uplus> (out\<star>\<^sub>2) = out"
proof(rule sb_eqI)
  fix c::"'a \<union> 'b"
  assume as:"Rep c \<in> chDom TYPE('a \<union> 'b)"
  have "Rep c \<in> chDom (TYPE ('a)) \<Longrightarrow> out\<star> \<uplus> (out\<star>) \<^enum> c = out \<^enum> c"
    by (metis DiffE chDom_def sbgetch_insert2 sbunion_getch sbunion_rep_eq sbunion_sbconvert_eq)
  moreover have "Rep c \<in> chDom (TYPE ('b)) \<Longrightarrow> out\<star> \<uplus> (out\<star>) \<^enum> c = out \<^enum> c"
    by (metis DiffE chDom_def sbconv_eq sbunion_getch sbunion_rep_eq sbunion_sbconvert_eq)
  moreover have "(Rep c \<in> chDom (TYPE ('a))) \<or> (Rep c \<in> chDom (TYPE ('b)))"
    using as chdom_in by fastforce
  ultimately show  "out\<star> \<uplus> (out\<star>) \<^enum> c = out \<^enum> c" by fastforce
qed

lemma spfcomp_belowI: 
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
  by (simp add: assms)


lemma sbconvert_getch [simp]: "sb \<star> \<^enum> c = sb \<^enum>\<^sub>\<star> c"
  by (simp add: sbgetch_insert2)

lemma sbunion_getch [simp]: "sb1 \<uplus>\<^sub>\<star> sb2  \<^enum>  c = (sb1 \<uplus> sb2) \<^enum>\<^sub>\<star> c"
  apply(auto simp add: sbgetch_insert2 sbunion_rep_eq)
  apply(auto simp add: sbgetch_insert sbunion_rep_eq)
  sorry

lemma sbunion_magic: 
  fixes sb1 ::"'cs1\<^sup>\<Omega>"
    and sb2 ::"'cs2\<^sup>\<Omega>"
  shows "(sb1 \<uplus> sb2)\<star> = sb1 \<uplus>\<^sub>\<star> sb2"
  apply(rule sb_eqI)
  by auto

lemma sbunion_fst[simp]: "(sb1 \<uplus> sb2)\<star>\<^sub>1 = sb1"
  by (simp add: sbunion_magic)

lemma sbunion_snd[simp]:
  fixes sb1 ::"'cs1\<^sup>\<Omega>"
    and sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "chDom (TYPE ('cs1)) \<inter> chDom (TYPE ('cs2)) = {}"
  shows "(sb1 \<uplus> sb2)\<star>\<^sub>2 = sb2"
  by (metis assms sbconv_eq sbunion_magic ubunion_commu ubunion_fst)

lemma sbunion_eqI:
  assumes "sb1 = (sb\<star>\<^sub>1)"
    and "sb2 = (sb\<star>\<^sub>2)"
  shows "sb1 \<uplus> sb2 = sb"
  by (simp add: assms)

lemma spfcomp_eqI:
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
   apply (simp_all add: assms)
  by (metis assms(1) assms(4) sbunion_fst sbunion_snd)

lemma spfcomp2gencomp  [simp]: 
      fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
        and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
      assumes "chDom (TYPE ('fOut)) \<inter> chDom (TYPE ('a)) = {}"
      assumes "chDom (TYPE ('gOut)) \<inter> chDom (TYPE ('a)) = {}"
      shows "spfConvert\<cdot>(f \<otimes> g) = (genComp\<cdot>f\<cdot>g::('a\<^sup>\<Omega> \<rightarrow> 'b\<^sup>\<Omega>))"
  apply(rule cfun_eqI)
  apply(simp add: spfConvert_def genComp_def)
  sorry

lemma sbgetch_empty2[simp]: fixes sb::"'cs\<^sup>\<Omega>"
    assumes "Rep c \<notin> chDom TYPE('cs)"
    shows "sb \<^enum>\<^sub>\<star> c = \<epsilon>"
  apply(simp add: sbgetch_insert assms chDom_def)
  by (metis(full_types) Diff_triv Rep_sb_strict app_strict assms chDom_def chIsEmpty_def chan_botsingle sbtypeepmpty_sbbot)

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
    apply(rule sb_eqI)
    apply auto[1]
    oops
  (* TODO: Wichtig *)
(* Ist aber sehr komisch, gilt glaube ich nicht ... *)


definition fstcomplete:: "((('a \<union> 'b) - ('c \<union> 'd))\<^sup>\<Omega> \<rightarrow> ('c \<union> 'd)\<^sup>\<Omega>) \<rightarrow> 'a\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>" where
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



lemma sercomp:fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
        and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
      assumes "chDom (TYPE ('fOut)) \<subseteq> chDom (TYPE ('gIn))"
      shows "(f \<otimes> g)\<cdot>sb = f\<cdot>(sb\<star>) \<uplus> g\<cdot>(f\<cdot>(sb\<star>)\<star>)"
  oops

definition spsComp::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set \<Rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>) set"  where
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

end