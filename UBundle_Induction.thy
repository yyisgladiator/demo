theory UBundle_Induction
  imports UBundle UBundle_Pcpo UBundle_Conc
begin

  
default_sort uscl


(****************************************************)
section\<open>Induction\<close>
(****************************************************) 

definition ubMaxLen:: "'M\<^sup>\<Omega> \<Rightarrow> lnat " where
"ubMaxLen b \<equiv> if ubDom\<cdot>b \<noteq> {} then (GREATEST ln. ln\<in>{(usclLen\<cdot>(b . c)) | c. c \<in> ubDom\<cdot>b}) else \<infinity>"  

lemma ubmaxlen_mono: "monofun (\<lambda>b. if ubDom\<cdot>b \<noteq> {} then (GREATEST ln. ln\<in>{(usclLen\<cdot>(b . c)) | c. c \<in> ubDom\<cdot>b}) else \<infinity>)"
  sorry

lemma ubmaxlen_mono2: "monofun ubMaxLen"
  using ubmaxlen_mono by (simp add: monofun_def ubMaxLen_def)

(*
lemma ind: 
  "\<lbrakk>adm P; P \<epsilon>; \<And>a s. P s  \<Longrightarrow> P (\<up>a \<bullet> s)\<rbrakk> \<Longrightarrow> P x"
apply (unfold adm_def)
apply (erule_tac x="\<lambda>i. stake i\<cdot>x" in allE, auto)
apply (simp add: stakeind)
by (simp add: reach_stream)
*)

lemma ind_ub: 
  "\<lbrakk>adm P; P (ubLeast cs); \<And>u ub. P ub  \<Longrightarrow> P (ubConc u\<cdot>ub)\<rbrakk> \<Longrightarrow> P x"
  sorry




end