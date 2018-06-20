theory UBundle_Induction
  imports UBundle UBundle_Pcpo UBundle_Conc "untimed/Streams" "untimed/SB"
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

lemma ubmaxlen_sbtake: "ubMaxLen (Fin n) (sbTake n\<cdot>x)"
  sorry

lemma ubleast_sbtake: assumes "x \<noteq> ubLeast (ubDom\<cdot>x)" shows "sbHd\<cdot>x \<noteq> ubLeast (ubDom\<cdot>x)"
  sorry

lemma sbcases: "\<And>x :: 'a stream\<^sup>\<Omega>. x = (ubLeast (ubDom\<cdot>x)) \<or> (\<exists>a s. ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a  \<and> a \<noteq> (ubLeast (ubDom\<cdot>x)) \<and> x = ubConc a\<cdot>s)"
  apply(case_tac "x = (ubLeast (ubDom\<cdot>x))")
   apply(simp_all)
proof - 
  fix x :: "'a stream\<^sup>\<Omega>"
  assume a1: "x \<noteq> ubLeast (ubDom\<cdot>x)"
  show "\<exists>a::'a stream\<^sup>\<Omega>. ubDom\<cdot>a = ubDom\<cdot>x \<and> (\<exists>s::'a stream\<^sup>\<Omega>. ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (Suc (0::nat))) a \<and> a \<noteq> (ubLeast (ubDom\<cdot>x))  \<and> x = ubConc a\<cdot>s)"
    apply(rule_tac x = "sbHd\<cdot>x" in exI)
    apply(simp)
    apply(rule_tac x = "sbRt\<cdot>x" in exI)
    apply(simp)
    apply rule
     apply(simp add: ubMaxLen_def usclLen_stream_def sbHd_def)
    apply rule
     apply(simp add: ubleast_sbtake a1)
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
                        \<And>a s. ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a \<and> a \<noteq> (ubLeast (ubDom\<cdot>x)) \<and> x = ubConc a\<cdot>s \<Longrightarrow> P\<rbrakk> 
                        \<Longrightarrow> P"
  using sbcases by blast


lemma sbtake_ind2: 
  "\<forall>x. (P (ubLeast (ubDom\<cdot>x)) \<and> 
       (\<forall>a s. P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a  \<and> u \<noteq> (ubLeast (ubDom\<cdot>x)) \<longrightarrow> P (ubConc a\<cdot>s))) 
        \<and> ubMaxLen (Fin n) x
       \<longrightarrow> P x"
proof(induct n)
  case 0
  then show ?case 
    
    sorry
next
  case (Suc n)
  then show ?case 
    
    sorry
qed

lemma sbtake_ind: 
  "\<forall>x. (P (ubLeast (ubDom\<cdot>x)) \<and> 
       (\<forall>a s. P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a \<and> a \<noteq> (ubLeast (ubDom\<cdot>x)) \<longrightarrow> P (ubConc a\<cdot>s))) 
       \<longrightarrow> P (sbTake n\<cdot>x)" 
  sorry

lemma finind_ub: 
  "\<lbrakk> \<exists>n. ubMaxLen (Fin n) x; 
     P (ubLeast (ubDom\<cdot>x)); 
     \<And>u ub. P ub \<and> ubDom\<cdot>u = (ubDom\<cdot>x) \<and> ubDom\<cdot>ub = (ubDom\<cdot>x) \<and> ubMaxLen (Fin 1) u \<and> u \<noteq> (ubLeast (ubDom\<cdot>x)) \<Longrightarrow> P (ubConc u\<cdot>ub) \<rbrakk>
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
     \<And>u ub. P ub \<and> ubDom\<cdot>u = (ubDom\<cdot>x) \<and> ubDom\<cdot>ub = (ubDom\<cdot>x) \<and> ubMaxLen (Fin 1) u \<and> u \<noteq> (ubLeast (ubDom\<cdot>x)) \<Longrightarrow> P (ubConc u\<cdot>ub) \<rbrakk>
     \<Longrightarrow> P (x :: 'a stream ubundle)"
  apply (unfold adm_def)
  apply (erule_tac x="\<lambda>i. sbTake i\<cdot>x" in allE, auto)
  by(simp add: sbtake_ind)


end