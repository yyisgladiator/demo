(*<*)(*:maxLineLen=68:*)
theory SPFcomp

imports bundle.SB SPF
begin
(*>*)
section \<open>General Composition Operators\<close>

text\<open>Networks of components can be modeled as a composition of the
modular components. A property for the complete network can then be
derived from the properties of the modular components. This section
introduces general composition operators for \Gls{spf} and 
\Gls{sps}. These operators are capable of parallel, sequential and 
feedback composition.\<close> 

subsection \<open>General composition of SPFs\<close>

text\<open>The composition operator over \Gls{spf} maps two \Gls{spf} to
their composition \gls{spf}. The output of its composition is
completely determined by a fixed point. In essence, the composed
\gls{spf} uses its input and previous output to compute the next
output which is equivalent to its sub \Gls{spf} output. This is done
until a fixed point is reached.\<close>

text\<open>Intuitively the resulting \gls{spf} input domain contains all
input channels, that are not internally connected through the 
composition. Else, not only the composition would be able to send 
messages over the internal channels.\<close>

(*cbot werden nicht verbunden; cbot können nur bei der eingabe 
vorkommen (bei der ausgabe nicht vorgesehen, siehe BDD92 Kap3.4)*)

definition genComp::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) \<rightarrow> 'E\<^sup>\<Omega> \<rightarrow> 'F\<^sup>\<Omega>"
  where "genComp \<equiv> \<Lambda> spf1 spf2 sbIn . 
          fix\<cdot>(\<Lambda> sbOut. spf1\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut) \<uplus>\<^sub>\<star> spf2\<cdot>(sbIn \<uplus>\<^sub>\<star> sbOut))"

abbreviation genComp_abbr (infixr "\<otimes>\<^sub>\<star>" 70) where 
"spf1 \<otimes>\<^sub>\<star> spf2 \<equiv> genComp\<cdot>spf1\<cdot>spf2"

text\<open>Hence, we restrict the signature of our general composition 
operator to always obtain a \gls{spf} with desired input and output
domains.\<close>

abbreviation genComp_nomabbr::
"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>)
 \<Rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>)" 
(infixr "\<otimes>" 70) where "spf1 \<otimes> spf2 \<equiv> genComp\<cdot>spf1\<cdot>spf2"


text\<open>The continuity of the composition operator holds by
construction, because it only uses continuous functions.\<close>

lemma spfcomp_unfold: 
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  shows "(f \<otimes> g)\<cdot>sbIn = f\<cdot>(sbIn \<uplus>\<^sub>\<star> ((f \<otimes> g)\<cdot>sbIn)) \<uplus> g\<cdot>(sbIn \<uplus>\<^sub>\<star> ((f \<otimes> g)\<cdot>sbIn))"
  apply(simp add: genComp_def)
  by(subst fix_eq, simp)


lemma spfcomp_eql[simp]: "genComp\<cdot>f\<cdot>g = f"
  apply(simp add: genComp_def)
  apply(rule cfun_eqI, simp)
  apply(rule fix_eqI)
  by simp+


lemma spfcomp_extract_l: 
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  shows "(sb \<uplus> (f \<otimes> g)\<cdot>sb\<star>) = f\<cdot>(sb \<uplus> (f \<otimes> g)\<cdot>sb\<star>)"
  apply(subst spfcomp_unfold)
  apply(subst sbunion_conv_snd)
   apply(simp, blast)
  apply(subst sbunion_conv_fst)
   apply(simp)
  by (simp add: sbunion_magic)

lemma spfcomp_extract_r: 
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE('fOut) \<inter> chDom TYPE('gOut) = {}"
  shows "(sb \<uplus> (f \<otimes> g)\<cdot>sb\<star>) = g\<cdot>(sb \<uplus> (f \<otimes> g)\<cdot>sb\<star>)"
  apply(subst spfcomp_unfold)
  apply(subst sbunion_conv_snd)
   apply(simp, blast)
  apply(subst sbunion_conv_snd)
   apply(simp add: assms)
  by (simp add: sbunion_magic)

text\<open>Its commutativity is also shown in the following theorem.\<close>

theorem spfcomp_commut: 
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
  and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom (TYPE ('fOut)) \<inter> chDom (TYPE ('gOut)) = {}"
  shows  "f \<otimes>\<^sub>\<star> g = g \<otimes>\<^sub>\<star> f"
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

text\<open>The output of the composition depends completely on the output
of is sub components. This is shown in the following theorems.\<close>

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
  apply(simp_all add: sbgetch_insert2 assms Abs_sb_inverse 
        sbunion_rep_eq)
  apply(simp add: sbconvert_insert)
  apply(subst sbgetch_insert,auto)
  apply(simp_all add: Abs_sb_inverse)
  oops
  (* TODO: Wichtig *)
(* Ist aber sehr komisch, gilt glaube ich nicht ... *)


(* TODO: Move to SB.thy *)



definition %invisible fstcomplete::
 "((('a \<union> 'b) - ('c \<union> 'd))\<^sup>\<Omega> \<rightarrow> ('c \<union> 'd)\<^sup>\<Omega>) \<rightarrow> 'a\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>" where
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

(*TODO*)
lemma sercomp:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
    and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE ('fOut) \<subseteq> chDom TYPE ('gIn)"
    and "chDom TYPE ('fOut) \<inter> chDom TYPE ('gOut) = {}"
    and "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
    and "chDom TYPE('fOut) \<inter> chDom TYPE('fIn) = {}"
  shows "(f \<otimes> g)\<cdot>sb = f\<cdot>(sb\<star>) \<uplus> g\<cdot>(f\<cdot>(sb\<star>)\<star>)"
  apply(subst spfcomp_unfold, auto)
  apply(rule arg_cong2 [of "(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1)" "(sb\<star>)" "sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2" "(f\<cdot>(sb\<star>)\<star>)"])
  subgoal
   apply(subst ubunion_fst)
    apply(simp add: assms)
  oops  (* TODO: assumptions/lemma prüfen, denke ist nicht ganz richtig *)

lemma parcomp:
  fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
  and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
  assumes "chDom TYPE ('fOut) \<inter> chDom TYPE ('gOut) = {}"
      and "chDom TYPE ('fOut) \<inter> chDom TYPE ('gIn) = {}"
      and "chDom TYPE ('fOut) \<inter> chDom TYPE ('fIn) = {}"
      and "chDom TYPE('gOut) \<inter> chDom TYPE('gIn) = {}"
      and "chDom TYPE('gOut) \<inter> chDom TYPE('fIn) = {}"
    shows "(f \<otimes> g)\<cdot>sb = f\<cdot>(sb\<star>) \<uplus> g\<cdot>(sb\<star>)"
  apply(subst spfcomp_unfold, auto)
  apply(rule arg_cong2 [of "sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>1" "(sb\<star>)" "(sb \<uplus>\<^sub>- (f \<otimes> g)\<cdot>sb\<star>\<^sub>2)"])
   apply(subst ubunion_fst)
    apply(simp add: assms)
  using assms apply blast
  apply(rule sb_eqI, simp)
  oops
  
subsection\<open>General Composition of SPSs\<close>

text\<open>With our general composition operator for \Gls{spf} we can also
define the general composition operator for \Gls{sps}. It composes
every combination of \Gls{spf} possible from both input \Gls{sps}.\<close> 

definition spsComp::
"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set 
\<Rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>) set"  where
"spsComp F G = {f \<otimes> g | f g. f\<in>F \<and> g\<in>G }"

lemma spscomp_praedicate: 
      fixes P::"'I1\<^sup>\<Omega> \<Rightarrow> 'O1\<^sup>\<Omega> \<Rightarrow> bool"
        and H::"'I2\<^sup>\<Omega> \<Rightarrow> 'O2\<^sup>\<Omega> \<Rightarrow> bool"
      assumes "chDom TYPE ('O1) \<inter> chDom TYPE ('O2) = {}"
      shows  "spsComp {p . \<forall>sb. P sb (p\<cdot>sb)} {h . \<forall>sb. H sb (h\<cdot>sb)} \<subseteq>   
            {g. \<forall>sb. 
                  let all = sb \<uplus> g\<cdot>sb in 
                    P (all\<star>) (all\<star>) \<and> H (all\<star>) (all\<star>)
            }"
  apply (auto simp add: spsComp_def Let_def)
  apply (simp add: spfcomp_extract_l)
  apply (simp add: assms spfcomp_extract_r)
  done


lemma spscomp_praedicate2: 
      fixes P::"'I1\<^sup>\<Omega> \<Rightarrow> 'O1\<^sup>\<Omega> \<Rightarrow> bool"
        and H::"'I2\<^sup>\<Omega> \<Rightarrow> 'O2\<^sup>\<Omega> \<Rightarrow> bool"
      assumes "chDom TYPE ('O1) \<inter> chDom TYPE ('O2) = {}"
      shows  "  
            {g. \<forall>sb. 
                  let all = sb \<uplus> g\<cdot>sb in 
                    P (all\<star>) (all\<star>) \<and> H (all\<star>) (all\<star>)
            } \<subseteq> spsComp {p . \<forall>sb. P sb (p\<cdot>sb)} {h . \<forall>sb. H sb (h\<cdot>sb)}"
  apply (auto simp add: spsComp_def Let_def)
  oops

(* Gegenbeispiel ... soweit ich sehe:
    P = H = "ist schwachkausal"
    bleibt nicht unter der feedbackkomposition erhalten *)


(*<*)
end
(*>*)