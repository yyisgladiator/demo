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
 (* inifxr \<otimes> ... without magic*)
abbreviation genComp_abbr :: "('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) \<Rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>)" (infixr "\<otimes>" 70) where 
"spf1 \<otimes> spf2 \<equiv> genComp\<cdot>spf1\<cdot>spf2"


definition spfConvert::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<rightarrow> ('Ie\<^sup>\<Omega> \<rightarrow> 'Oe\<^sup>\<Omega>)" where
"spfConvert = (\<Lambda> f sb. (f\<cdot>(sb\<star>))\<star>)"   (* TODO: weniger klammern + warnings *)

lemma spfcomp_eql[simp]: "genComp\<cdot>f\<cdot>g = f"
  apply(simp add: genComp_def)
  apply(rule cfun_eqI, simp)
  apply(rule fix_eqI)
  by simp+


(* Solange output disjunkt *)
lemma "genComp\<cdot>f\<cdot>g = genComp\<cdot>g\<cdot>f"
  oops

lemma spfcomp_eqr[simp]: "genComp\<cdot>f\<cdot>g = g"
  oops 

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

lemma spfcomp2gencomp  [simp]: "spfConvert\<cdot>(f \<otimes> g) = genComp\<cdot>f\<cdot>g"
  oops

lemma spfcomp_surj: obtains f g where "f \<otimes> g = x"
  oops

definition spsComp::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set \<Rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>) set"  where
"spsComp F G = {f \<otimes> g | f g. f\<in>F \<and> g\<in>G }"

lemma fixes P::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> bool"
        and H::"('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) \<Rightarrow> bool"
      shows  "spsComp {x. P x} {x. H x} = {x. P (spfConvert\<cdot>x) \<and> H (spfConvert\<cdot>x)}"
  apply (auto simp add: spsComp_def)
  oops
(*  by (metis spfcomp2gencomp spfcomp_eql spfcomp_eqr spfcomp_surj) *)
(* Gegenbeispiel ... soweit ich sehe: 
    P = H = "ist schwachkausal"
    bleibt nicht unter der feedbackkomposition erhalten *)

end