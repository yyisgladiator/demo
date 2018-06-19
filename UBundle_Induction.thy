theory UBundle_Induction
  imports UBundle UBundle_Pcpo UBundle_Conc "untimed/Streams" "untimed/SPF"
begin

  



(****************************************************)
section\<open>MaxLen\<close>
(****************************************************) 


default_sort uscl


definition ubMaxLen :: "lnat \<Rightarrow> 'M\<^sup>\<Omega> \<Rightarrow> bool" where
"ubMaxLen n ub  \<equiv> \<forall>c \<in> ubDom\<cdot>ub. usclLen\<cdot>(ub . c) \<le> n"


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


lemma ubmaxlen_least: "ubMaxLen 0 ((ubLeast cs):: 'a stream\<^sup>\<Omega>)"
  by(simp add: ubMaxLen_def usclLen_stream_def)

lemma sbcases: "\<And>x :: 'a stream\<^sup>\<Omega>. x = (ubLeast (ubDom\<cdot>x)) \<or> (\<exists>a s. ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a \<and> x = ubConc a\<cdot>s)"
  apply(case_tac "x = (ubLeast (ubDom\<cdot>x))")
   apply(simp_all)
proof - 
  fix x :: "'a stream\<^sup>\<Omega>"
  assume "x \<noteq> ubLeast (ubDom\<cdot>x)"
  show "\<exists>a::'a stream\<^sup>\<Omega>. ubDom\<cdot>a = ubDom\<cdot>x \<and> (\<exists>s::'a stream\<^sup>\<Omega>. ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (Suc (0::nat))) a \<and> x = ubConc a\<cdot>s)"
    apply(rule_tac x = "sbHd\<cdot>x" in exI)
    apply(simp)
    apply(rule_tac x = "sbRt\<cdot>x" in exI)
    apply(simp)
    apply rule
     apply(simp add: ubMaxLen_def usclLen_stream_def sbHd_def)
    apply(rule ub_eq)
    apply (simp add: sbtake_sbdom)
  proof - 
    fix c
    assume c_domx: "c \<in> ubDom\<cdot>x"
    show "x  .  c = ubConc (sbHd\<cdot>x)\<cdot>(sbRt\<cdot>x)  .  c"
      apply(subst ubConc_usclConc_eq)
      using c_domx apply simp
      using c_domx apply simp
      apply(simp add: usclConc_stream_def)
      by (simp add: c_domx sbHd_def sbRt_def)
  qed
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
  
  hence a01: "P (ubLeast (ubDom\<cdot>x))"
    by simp
  have a02: "(\<forall>a s. P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a \<longrightarrow> P (ubConc a\<cdot>s))"
    using a0 by blast

  show "P (sbTake n\<cdot>x)"
  proof(induct n)
    case 0
    then show ?case 
      by (simp add: a01 sbtake_zero)
  next
    case (Suc n)
    then have case_suc: "P (sbTake n\<cdot>x)"
      by blast
    
    show ?case
      apply(rule_tac x=x in sbcases2)
      using a01 apply (metis sbtake_sbdom sbtake_sbgetch stream.take_strict ubgetchI ubleast_ubgetch)
    proof - 
      fix a
      fix s
      assume a1: "ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (1::nat)) a \<and> x = ubConc a\<cdot>s"
      have a11: "ubDom\<cdot>a = ubDom\<cdot>x"
        using a1 by blast
      have a12: "ubDom\<cdot>s = ubDom\<cdot>x"
        using a1 by blast
      have a13: "ubMaxLen (Fin (1::nat)) a"
        using a1 by blast
      have a14: "x = ubConc a\<cdot>s"
        using a1 by blast

      show "P (sbTake (Suc n)\<cdot>x)"
        
        sorry
    qed
  qed
qed
(*
  apply(induct_tac n)
  apply(simp add: sbtake_zero)
  apply(rule_tac x=x in sbcases2)
   apply clarsimp
*)

lemma finind_ub: 
  "\<lbrakk> \<exists>n. ubMaxLen (Fin n) x; 
     P (ubLeast (ubDom\<cdot>x)); 
     \<And>u ub. P ub \<and> ubDom\<cdot>u = (ubDom\<cdot>x) \<and> ubDom\<cdot>ub = (ubDom\<cdot>x) \<and> ubMaxLen (Fin 1) u \<Longrightarrow> P (ubConc u\<cdot>ub) \<rbrakk>
     \<Longrightarrow> P (x :: 'a stream ubundle)"
proof - 
  obtain n where "ubMaxLen (Fin n) x"
    sorry
  then have "sbTake n\<cdot>x = x"
    sorry
  then show ?thesis
    sorry
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