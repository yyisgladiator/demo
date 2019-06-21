theory SPFcompv3

imports bundle.SB
begin

section \<open>General composition\<close>

subsection \<open>General composition definition\<close>

(*cbot werden nicht verbunden; cbot können nur bei der eingabe vorkommen (bei der ausgabe nicht vorgesehen, siehe BDD92 Kap3.4)*)
(*now with magic*)
definition genComp :: "('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) \<rightarrow> (('E)\<^sup>\<Omega> \<rightarrow> ('F)\<^sup>\<Omega>)"  where
"genComp \<equiv> \<Lambda> spf1 spf2.  (\<Lambda> sbIn . fix\<cdot>(\<Lambda> sb. (spf1\<cdot>((sbIn \<uplus> sb))) \<uplus> (spf2\<cdot>((sbIn \<uplus> sb)))))"

lemma genComp_cont[simp]:"cont (\<lambda>spf1 . \<Lambda> spf2 .(\<Lambda> sbIn . fix\<cdot>(\<Lambda> sb. (spf1\<cdot>((sbIn \<uplus> sb))) \<uplus> (spf2\<cdot>((sbIn \<uplus> sb))))))"
  by simp

subsection \<open>General composition abbreviation\<close>
 (* inifxr \<otimes> ... without magic
abbreviation genComp_abbr :: "('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) \<Rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>)" (infixr "\<otimes>" 70) where 
"spf1 \<otimes> spf2 \<equiv> genComp\<cdot>spf1\<cdot>spf2"
*)


end