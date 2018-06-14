theory UBundle_Induction
  imports UBundle UBundle_Pcpo UBundle_Conc "untimed/Streams" "untimed/SPF"
begin

  



(****************************************************)
section\<open>MaxLen\<close>
(****************************************************) 


default_sort uscl


definition ubMaxLen :: "lnat \<Rightarrow> 'M\<^sup>\<Omega> \<Rightarrow> bool" where
"ubMaxLen n ub  \<equiv> \<forall>c \<in> ubDom\<cdot>ub. usclLen\<cdot>(ub . c) \<le> n"

lemma ubmaxlen_least: "ubMaxLen 0 (ubLeast cs)"
  sorry


(****************************************************)
section\<open>Induction\<close>
(****************************************************) 

(* Streams:
lemma ind: 
  "\<lbrakk>adm P; P \<epsilon>; \<And>a s. P s  \<Longrightarrow> P (\<up>a \<bullet> s)\<rbrakk> \<Longrightarrow> P x"
apply (unfold adm_def)
apply (erule_tac x="\<lambda>i. stake i\<cdot>x" in allE, auto)
apply (simp add: stakeind)
by (simp add: reach_stream)
*)

default_sort message

lemma sbcases: "\<And>x :: 'a stream\<^sup>\<Omega>. x = (ubLeast (ubDom\<cdot>x)) \<or> (\<exists>a s. ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a \<and> x = ubConc a\<cdot>s)"
  apply(case_tac "x = (ubLeast (ubDom\<cdot>x))")
   apply(simp_all)
proof - 
  fix x :: "'a stream\<^sup>\<Omega>"
  assume "x \<noteq> ubLeast (ubDom\<cdot>x)"
  show "\<exists>a::'a stream\<^sup>\<Omega>. ubDom\<cdot>a = ubDom\<cdot>x \<and> (\<exists>s::'a stream\<^sup>\<Omega>. ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (Suc (0::nat))) a \<and> x = ubConc a\<cdot>s)"
    apply(rule_tac x = "sbTake 1\<cdot>x" in exI)
    apply(simp)
    apply(rule_tac x = "sbRt\<cdot>x" in exI)
    apply(simp)
    apply rule
    
    sorry
qed

lemma sbcases2: "\<And>(x :: 'a stream\<^sup>\<Omega>) P. \<lbrakk>x = (ubLeast (ubDom\<cdot>x)) \<Longrightarrow> P; 
                        \<And>a s. ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a \<and> x = ubConc a\<cdot>s \<Longrightarrow> P\<rbrakk> 
                        \<Longrightarrow> P"
  using sbcases by blast

lemma sbtake_ind: 
  "\<forall>x. (P (ubLeast (ubDom\<cdot>x)) \<and> 
       (\<forall>a s. P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a \<longrightarrow> P (ubConc a\<cdot>s))) 
       \<longrightarrow> P (sbTake n\<cdot>x)"
  apply rule+
proof -
  fix x :: "'a stream\<^sup>\<Omega>"
  assume a0: "P (ubLeast (ubDom\<cdot>x)) \<and> (\<forall>a s. P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a \<longrightarrow> P (ubConc a\<cdot>s))"
  
  hence a1: "P (ubLeast (ubDom\<cdot>x))"
    by simp
  have a2: "(\<forall>a s. P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a \<longrightarrow> P (ubConc a\<cdot>s))"
    using a0 by blast

  show "P (sbTake n\<cdot>x)"
  proof(induct n)
    case 0
    then show ?case 
      by (simp add: a1 sbtake_zero)
  next
    case (Suc n)
    then show ?case 
      apply(rule_tac x=x in sbcases2)
       apply (metis sbtake_sbdom sbtake_sbgetch stream.take_strict ubgetchI ubleast_ubgetch)
      apply(simp add: sbcases)
      using sbcases
      sorry
  qed
qed

lemma ind_ub: 
  "\<lbrakk> adm P; 
     P (ubLeast (ubDom\<cdot>x)); 
     \<And>u ub. P ub \<and> ubDom\<cdot>u = (ubDom\<cdot>x) \<and> ubDom\<cdot>ub = (ubDom\<cdot>x) \<and> ubMaxLen (Fin 1) u \<Longrightarrow> P (ubConc u\<cdot>ub) \<rbrakk>
     \<Longrightarrow> P (x :: 'a stream ubundle)"
  apply (unfold adm_def)
  apply (erule_tac x="\<lambda>i. sbTake i\<cdot>x" in allE, auto)
  by(simp add: sbtake_ind)


end