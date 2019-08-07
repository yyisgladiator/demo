theory EvenAutomat

imports automaton.dAutomaton_causal evenAutomat_inc

begin
(*Even automaton*)
fun dAeven_transition::"S_even \<Rightarrow> (nat) \<Rightarrow> (S_even \<times> bool)"where
"dAeven_transition (S True) (n) = (S (n mod 2 = 0),n mod 2 = 0)" |
"dAeven_transition (S False)(n) = (S (n mod 2 = 1),n mod 2 = 1)"

interpretation even_sscanl:sscanlGen "dAeven_transition" "S True" "buildEveninSBE" "buildEvenoutSBE"
  by(unfold_locales)
  
abbreviation evenStep::"(S_even \<Rightarrow> (inEven\<^sup>\<Omega> \<rightarrow> outEven\<^sup>\<Omega>))"where
"evenStep \<equiv> dawStateSem even_sscanl.da"

definition evenSpf::"(inEven\<^sup>\<Omega> \<rightarrow> outEven\<^sup>\<Omega>)"where
"evenSpf = dawSem even_sscanl.da"

lemma eveningetset_eq:"evenInSBE.getterSB\<cdot>(evenInSBE.setterSB\<cdot>s) = s"
  by(simp)

lemma evenoutgetset_eq:"evenOutSBE.getterSB\<cdot> (evenOutSBE.setterSB\<cdot>s) = s"
  by(simp)

lemma evenstep2sscanl:"evenOutSBE.getterSB\<cdot>(evenStep state\<cdot>(evenInSBE.setterSB\<cdot>input)) = sscanlAsnd dAeven_transition state\<cdot>input"
  by (simp add: even_sscanl.daut2sscanl)

lemma even_step_t1:"sscanlAsnd dAeven_transition (S True)\<cdot>(\<up>(n) \<bullet> s) = \<up>(n mod 2 = 0) \<bullet> sscanlAsnd dAeven_transition (S (n mod 2 = 0))\<cdot>(s)"
  by simp

lemma even_step_t2:"sscanlAsnd dAeven_transition (S False)\<cdot>(\<up>(n) \<bullet> s) = \<up>(n mod 2 = 1) \<bullet> sscanlAsnd dAeven_transition (S (n mod 2 = 1))\<cdot>(s)"
  by simp

lemma tinf_helper:assumes "Fin n < # input" and "\<forall>e\<in>(sValues\<cdot>input). e mod 2 = 0"
      shows"snth n (sscanlAsnd dAeven_transition (S True)\<cdot>input)"
using assms
proof(induction n arbitrary: input)
  case 0
  then show ?case  
    apply(subst scases[of input])
    by simp_all
next
  case (Suc n)
  then show ?case
    apply(subst scases[of input])
    by simp_all
qed

lemma assumes "\<forall>e\<in>(sValues\<cdot>input). e mod 2 = 0"
      and "#input = \<infinity>"  
      shows"evenOutSBE.getterSB\<cdot>(evenStep (S True)\<cdot>(evenInSBE.setterSB\<cdot>input)) = ((\<up>True)\<^sup>\<infinity>)"
  apply(simp add: evenstep2sscanl)
  apply(rule snths_eq,auto simp add: assms) 
  by(rule tinf_helper,simp_all add: assms)

lemma ftinf_step:assumes "Fin (Suc n) < # input" and "\<forall>e\<in>(sValues\<cdot>input). e mod 2 = 1"
      shows"snth (Suc n) (sscanlAsnd dAeven_transition state\<cdot>input) = snth n (sscanlAsnd dAeven_transition state\<cdot>input)"
using assms
proof(induction n arbitrary: input state)
  case 0
  then show ?case  
    sorry
next
  case (Suc n)
  then show ?case
    sorry
qed

lemma ftinf_helper:assumes "Fin n < # input" and "\<forall>e\<in>(sValues\<cdot>input). e mod 2 = 1"
      shows"snth n (sscanlAsnd dAeven_transition (S True)\<cdot>input) = snth n \<up>False \<bullet> \<up>True\<^sup>\<infinity>"
using assms
proof(induction n arbitrary: input)
  case 0
  then show ?case
    sorry
next
  case (Suc n)
  then show ?case
    sorry
qed


lemma assumes "\<forall>e\<in>(sValues\<cdot>input). e mod 2 = 1"
      and "#input = \<infinity>"  
      shows"evenOutSBE.getterSB\<cdot>(evenStep (S True)\<cdot>(evenInSBE.setterSB\<cdot>input)) = ((\<up>False \<bullet> \<up>True)\<^sup>\<infinity>)"
  apply(simp add: evenstep2sscanl)
  apply(rule snths_eq,simp add:assms slen_sinftimes)
  by(subst ftinf_helper,simp_all add: assms)


end