section {* cpo fixpoint *}

theory CPOFix
imports Prelude
begin

default_sort type
  
(* genaral fixpoint over cpo, x is \<sqsubseteq> f x*)  
  

definition fixg_cont::"('a::cpo) \<rightarrow>('a \<rightarrow> 'a) \<rightarrow> 'a" where
"fixg_cont = (\<Lambda> x F. \<Squnion>i. iterate i\<cdot>F\<cdot>x)"

definition fixg::"('a::cpo) \<Rightarrow> ('a \<rightarrow> 'a) \<Rightarrow> 'a" where
"fixg = (\<lambda> x F. \<Squnion>i. iterate i\<cdot>F\<cdot>x)"

lemma iter_fixg_cont[simp]:
 shows "cont (\<lambda> x F . iterate i\<cdot>F\<cdot>x)"
  by simp
    
lemma iter_fixg_mono[simp]:
 shows "monofun (\<lambda> x F. iterate i\<cdot> F\<cdot> x)"
  by (simp add: cont2mono)

    
lemma iter_fixg_mono2: assumes "x \<sqsubseteq> y" and "F1 \<sqsubseteq> F2"
  shows "\<forall>i . (iterate i\<cdot>F1\<cdot>x) \<sqsubseteq> (iterate i\<cdot>F2\<cdot>y)"
  by (simp add: assms(1) assms(2) monofun_cfun)
    
lemma iter_fixg_chain: assumes "x \<sqsubseteq> F\<cdot>x"
  shows "chain (\<lambda>i. iterate i\<cdot>F\<cdot>x)"
    apply (rule chainI)
  by (metis assms cont_pref_eq1I iterate_Suc2)
    
lemma iter_fixg_dom: assumes "x \<sqsubseteq> F\<cdot>x"
  shows "(iterate i\<cdot>F\<cdot>x) \<sqsubseteq> (iterate i\<cdot>F\<cdot>(F\<cdot>x))"
  by (simp add: assms cont_pref_eq1I)
(* cont \<lambda>F *)
    
    
lemma lub_iter_fixg_mono_req: assumes "F1 \<sqsubseteq> F2" and "x \<sqsubseteq> F1\<cdot>x" and "x\<sqsubseteq>F2\<cdot>x"
  shows "(\<Squnion>i. iterate i\<cdot>F1\<cdot>x) \<sqsubseteq> (\<Squnion>i. iterate i\<cdot>F2\<cdot>x)"
proof -
  have "\<forall>i. (iterate i\<cdot>F1\<cdot>x) \<sqsubseteq> (iterate i\<cdot>F2\<cdot>x)"
    by (simp add: iter_fixg_mono2 assms(1) assms(2))
   then show ?thesis
    by (simp add: lub_mono assms iter_fixg_mono2 iter_fixg_chain)
qed


(*cont (\<lambda> F. fixg x F)*)
  
lemma chain_lub_iter_fixg: assumes "chain Y"  and "\<forall>i. x \<sqsubseteq> (Y i)\<cdot>x"
  shows "chain (\<lambda>i. \<Squnion>ia. iterate ia\<cdot>(Y i)\<cdot>x)"
proof -
  have f1: "\<forall>i. (Y i) \<sqsubseteq> (Y (Suc i))"
    using assms(1) po_class.chain_def by blast
  have f2: "\<forall>i. (Y i)\<cdot>x \<sqsubseteq> (Y (Suc i))\<cdot>x"
    using assms(1) po_class.chain_def monofun_cfun_fun by blast
  thus ?thesis
  proof -
    have "\<And>n a na. a \<notsqsubseteq> (Y n)\<cdot>a \<or> iterate na\<cdot>(Y n)\<cdot>a \<sqsubseteq> iterate (Suc na)\<cdot>(Y n)\<cdot>a"
      by (metis (full_types) iterate_Suc2 monofun_cfun_arg)
    then show ?thesis
      by (simp add: assms ch2ch_lub f1 po_class.chainI)
  qed
qed
  
lemma chain_lub_iter_fixg_req: assumes "chain Y" and "\<forall>i. x \<sqsubseteq> (Y i)\<cdot>x"
  shows "(\<Squnion>i ia. iterate i\<cdot>(Y ia)\<cdot>x) \<sqsubseteq> (\<Squnion>i ia.  iterate ia\<cdot>(Y i)\<cdot>x)"
proof -
  have f1: "\<And>i. cont (\<lambda>x F. iterate i\<cdot>F\<cdot>x)"
    by (simp add: assms(2))
  moreover
  have f2: "(\<Squnion>i. iterate i\<cdot>(\<Squnion>i. Y i)\<cdot>x) = (\<Squnion> ia i. iterate ia\<cdot>(Y i)\<cdot>x)"
    by (subst cont2lub_lub_eq,simp_all add: assms)
  ultimately
  show ?thesis
    by (simp add: diag_lub ch2ch_cont assms iter_fixg_chain)
qed  
  
lemma chain_lub_lub_iter_fixg: assumes "chain Y"
                               and "\<forall>i. x \<sqsubseteq> (Y i)\<cdot>x" 
  shows "(\<Squnion>i.(iterate i\<cdot>(\<Squnion>i. Y i)\<cdot>x)) \<sqsubseteq> (\<Squnion>i ia. (iterate ia\<cdot>(Y i)\<cdot>x))"
proof -
  have f2: "(\<Squnion>i. iterate i\<cdot>(\<Squnion>i. Y i)\<cdot>x) = (\<Squnion> ia i. iterate ia\<cdot>(Y i)\<cdot>x)"
    by (subst cont2lub_lub_eq, simp_all add: assms)
  have f4: "(\<Squnion>i ia. iterate i\<cdot>(Y ia)\<cdot>x) \<sqsubseteq> (\<Squnion>i ia.  iterate ia\<cdot>(Y i)\<cdot>x)"
    by (rule chain_lub_iter_fixg_req, simp_all add: assms)
  show ?thesis
    by(simp add: f2 f4)
qed
  

 lemma fixg_monoI [simp]: assumes "\<And> F. x \<sqsubseteq> F\<cdot>x"
  shows "monofun (\<lambda>F. \<Squnion>i.(iterate i\<cdot>F)\<cdot>x )"
proof -
  have "\<And>F1 F2. F1 \<sqsubseteq> F2 \<Longrightarrow> x \<sqsubseteq> F1\<cdot>x \<Longrightarrow> x \<sqsubseteq> F2\<cdot>x \<Longrightarrow> ((\<lambda> F. (\<Squnion>i.(iterate i\<cdot>F)\<cdot>x)) F1) 
                              \<sqsubseteq> ((\<lambda> F. (\<Squnion>i.(iterate i\<cdot>F)\<cdot>x)) F2)"
    by (simp add: lub_iter_fixg_mono_req)
  thus ?thesis
    by (frule monofunI, simp_all add: assms)
qed 

(* Insertion lemma for cont proofs fixg *)
lemma fixg_contI [simp]: assumes "\<And> F. x \<sqsubseteq> F\<cdot>x"
  shows "cont (\<lambda> F. (\<Squnion>i.(iterate i\<cdot>F)\<cdot> x) )"
  apply (rule contI2)
  apply (rule fixg_monoI, simp_all add: assms)
proof(auto)
  fix Y::"nat \<Rightarrow> 'a \<rightarrow>'a"
  assume a1:"chain Y"
  have "\<forall>i. x \<sqsubseteq> (Y i)\<cdot>x"
    by (simp add: assms)
  then show "(\<Squnion>i. iterate i\<cdot>(\<Squnion>i. Y i)\<cdot>x) \<sqsubseteq> (\<Squnion>i ia. iterate ia\<cdot>(Y i)\<cdot>x)"
  apply(simp add: contlub_cfun_fun contlub_cfun_arg a1)
  using chain_lub_lub_iter_fixg
  by (simp add: a1 chain_lub_iter_fixg_req)
qed 
  
lemma fixg_contI2 [simp]: fixes x :: "'a::cpo" 
                            assumes"\<And>F. x\<sqsubseteq> F\<cdot>x"
                            shows "cont (\<lambda> F. fixg x F)"
proof -
  have f1: "(\<lambda> F. fixg x F) = (\<lambda> F. \<Squnion>i. iterate i\<cdot>F\<cdot>x)"
    by (simp add: fixg_def)
  show ?thesis
    apply (subst f1)
    using fixg_contI assms by blast
qed  
 
  
  
(*cont (\<lambda> x. fixg x F)*)
  
lemma lub_iter_fixg_mono_req_2: assumes "x \<sqsubseteq> y" and "x \<sqsubseteq> F\<cdot>x" and "y \<sqsubseteq> F\<cdot>y"
  shows "(\<Squnion>i. iterate i\<cdot>F\<cdot>x) \<sqsubseteq> (\<Squnion>i. iterate i\<cdot>F\<cdot>y)"
proof -
  have "\<forall>i. (iterate i\<cdot>F\<cdot>x) \<sqsubseteq> (iterate i\<cdot>F\<cdot>y)"
    by (simp add: iter_fixg_mono2 assms(1) assms(2))
   then show ?thesis
    by (simp add: lub_mono assms iter_fixg_mono2 iter_fixg_chain)
qed

  
lemma chain_lub_iter_fixg_2: assumes "chain Y" and "chain Y2" and "\<forall>i. Y i \<sqsubseteq> (Y2 i)\<cdot>(Y i)"
  shows "chain (\<lambda>i. \<Squnion>ia. iterate ia\<cdot>(Y2 i)\<cdot>(Y i))"
proof -
  have f1: "\<forall>i. (Y i) \<sqsubseteq> (Y (Suc i))"
    using assms(1) po_class.chain_def by blast
  thus ?thesis
  proof -
    have "\<And>n a na. Y n \<notsqsubseteq> (Y2 n)\<cdot>a \<or> iterate na\<cdot>(Y2 n)\<cdot> (Y n) \<sqsubseteq> iterate (Suc na)\<cdot>(Y2 n)\<cdot>a"
      by (metis (full_types) iterate_Suc2 monofun_cfun_arg)
    then show ?thesis
      by (simp add: assms ch2ch_lub f1 po_class.chainI)
  qed
qed
 
  
lemma chain_lub_iter_fixg_req_2: assumes "chain Y" and "\<forall>i. Y i \<sqsubseteq> F\<cdot>(Y i)"
  shows "(\<Squnion>i ia. iterate i\<cdot>F\<cdot>(Y ia)) \<sqsubseteq> (\<Squnion>i ia.  iterate ia\<cdot>F\<cdot>(Y i))"
proof -
  have f1: "\<And>i. cont (\<lambda>x F. iterate i\<cdot>F\<cdot>x)"
    by (simp add: assms(2))
  moreover
  have f2: "(\<Squnion>i. iterate i\<cdot>F\<cdot>(\<Squnion>i. Y i)) = (\<Squnion> ia i. iterate ia\<cdot>F\<cdot>(Y i))"
    by (subst cont2lub_lub_eq,simp_all add: assms)
  ultimately
  show ?thesis
    by (simp add: diag_lub ch2ch_cont assms iter_fixg_chain)
qed  
  
lemma chain_lub_lub_iter_fixg_2: assumes "chain Y"
                               and "\<forall>i. Y i \<sqsubseteq> F\<cdot>(Y i)" 
  shows "((\<Squnion>i.(iterate i\<cdot>F)\<cdot> (\<Squnion>i. Y i))) \<sqsubseteq> ((\<Squnion>i ia. (iterate ia\<cdot>F)\<cdot>(Y i)))"
proof -
  have f2: "(\<Squnion>i. iterate i\<cdot>F\<cdot>(\<Squnion>i. Y i)) = (\<Squnion> ia i. iterate ia\<cdot>F\<cdot>(Y i))"
    by (subst cont2lub_lub_eq, simp_all add: assms)
  have f4: "(\<Squnion>i ia. iterate i\<cdot>F\<cdot>(Y ia)) \<sqsubseteq> (\<Squnion>i ia.  iterate ia\<cdot>F\<cdot>(Y i))"
    by (rule chain_lub_iter_fixg_req_2, simp_all add: assms)
  show ?thesis
    by(simp add: f2 f4)
qed
  


lemma fixg_monoI_2 [simp]: assumes "\<And> x. x \<sqsubseteq> F\<cdot>x"
  shows "monofun (\<lambda>x. \<Squnion>i.(iterate i\<cdot>F)\<cdot>x )"
proof -
  have "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> F\<cdot>x \<Longrightarrow> y \<sqsubseteq> F\<cdot>y\<Longrightarrow> ((\<lambda> x. (\<Squnion>i.(iterate i\<cdot>F)\<cdot>x)) x) 
                              \<sqsubseteq> ((\<lambda> x. (\<Squnion>i.(iterate i\<cdot>F)\<cdot>x)) y)"
    by (simp add: lub_iter_fixg_mono_req_2)
  thus ?thesis
    by (frule monofunI, simp_all add: assms)
qed 
 
lemma lub_iter_fixg_mono_req_3: assumes "x \<sqsubseteq> y" and "x \<sqsubseteq> F1\<cdot>x" and "y \<sqsubseteq> F2\<cdot>y" and "F1\<sqsubseteq>F2"
  shows "(\<Squnion>i. iterate i\<cdot>F1\<cdot>x) \<sqsubseteq> (\<Squnion>i. iterate i\<cdot>F2\<cdot>y)"
proof -
  have "\<forall>i. (iterate i\<cdot>F1\<cdot>x) \<sqsubseteq> (iterate i\<cdot>F2\<cdot>y)"
    by (simp add: iter_fixg_mono2 assms)
   then show ?thesis
    by (simp add: lub_mono assms iter_fixg_mono2 iter_fixg_chain)
qed  

(*
lemma fixg_monoI_3 [simp]: assumes "\<And> F. x \<sqsubseteq> F\<cdot>x" and"(\<And>x. x \<sqsubseteq> F\<cdot>x)" and "(\<And>y. y \<sqsubseteq> F\<cdot>y)"
  shows "monofun (\<lambda>x F. \<Squnion>i.(iterate i\<cdot>F)\<cdot>x)"
proof -
  have "\<And>x y F1 F2. F1 \<sqsubseteq> F2 \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> F1\<cdot>x \<Longrightarrow> y \<sqsubseteq> F2\<cdot>y \<Longrightarrow> ((\<lambda> x F. (\<Squnion>i.(iterate i\<cdot>F)\<cdot>x)) x F1) 
                              \<sqsubseteq> ((\<lambda> x F. (\<Squnion>i.(iterate i\<cdot>F)\<cdot>x)) y F2)"
    by (simp add: lub_iter_fixg_mono_req_3)
  thus ?thesis
    apply (frule monofunI)
    using fixg_monoI_2[of x] fixg_monoI[of F] assms apply auto
    sorry
qed *)

(* Insertion lemma for cont proofs fixg *)
lemma fixg_contI_2 [simp]: assumes "\<And> x. x \<sqsubseteq> F\<cdot>x"
  shows "cont (\<lambda> x. (\<Squnion>i.(iterate i\<cdot>F)\<cdot> x) )"
  apply (rule contI2)
  apply (rule fixg_monoI_2, simp_all add: assms)
proof(auto)
  fix Y::"nat \<Rightarrow> 'a"
  assume a1:"chain Y"
  have "\<forall>i. Y i \<sqsubseteq> F\<cdot>(Y i)"
    by (simp add: assms)
  then show "(\<Squnion>i. iterate i\<cdot>F\<cdot>(\<Squnion>i. Y i)) \<sqsubseteq> (\<Squnion>i ia. iterate ia\<cdot>F\<cdot>(Y i))"
  apply(simp add: contlub_cfun_fun contlub_cfun_arg a1)
  using chain_lub_lub_iter_fixg
  by (simp add: a1 chain_lub_iter_fixg_req_2)
qed

lemma fixg_contI2_2 [simp]: fixes F :: "'a::cpo \<rightarrow> 'a" 
                            assumes"\<And>x. x\<sqsubseteq> F\<cdot>x"
                            shows "cont (\<lambda> x. fixg x F)"
proof -
  have f1: "(\<lambda> x. fixg x F) = (\<lambda> x. \<Squnion>i. iterate i\<cdot>F\<cdot>x)"
    by (simp add: fixg_def)
  show ?thesis
    apply (subst f1)
    using fixg_contI_2 assms by blast
qed
  
(*cont (fixg) maybe not possible like that*) 

lemma fixg_mono: assumes"\<And>F. x \<sqsubseteq> F\<cdot>x" and "\<And>F. y \<sqsubseteq> F\<cdot>y" and "x \<sqsubseteq> y" shows "(\<lambda>F. \<Squnion>i. iterate i\<cdot> F\<cdot>x) \<sqsubseteq> (\<lambda>F. \<Squnion>i. iterate i\<cdot>F\<cdot>y)"
  apply(insert fixg_monoI_2)
  by (metis (no_types, lifting) assms fun_belowI iterate_Suc2 lub_mono monofun_cfun_arg po_class.chainI)
    (*
lemma fixg_insert:"\<And>x. x \<sqsubseteq> F\<cdot>x \<Longrightarrow> fixg\<cdot>x\<cdot>F = (\<Squnion>i. iterate i\<cdot>F\<cdot>x)"
  apply(simp add: fixg_def,subst beta_cfun) 
   apply(rule contI) 
    apply(simp add: contlub_cfun_arg contlub_cfun_fun)
  proof-
  fix Y::"nat \<Rightarrow> 'a::cpo"
  assume c1: "chain Y"
  show "range (\<lambda>i. \<Lambda> F. \<Squnion>ia. iterate ia\<cdot>F\<cdot>(Y i)) <<| (\<Lambda> F. \<Squnion>i ia. iterate i\<cdot>F\<cdot>(Y ia))"
    sorry
next
  fix F::"'a \<rightarrow> 'a"
  show "\<And>x. x \<sqsubseteq> F\<cdot>x \<Longrightarrow> (\<Lambda> F. \<Squnion>i. fixg x F i)\<cdot>F = (\<Squnion>i. fixg x F i)"
  apply(subst beta_cfun,auto)    
  proof(rule contI)
    fix Y::"nat \<Rightarrow> 'a::cpo \<rightarrow> 'a"
    assume c1: "chain Y"
    then have "\<And>x. chain (\<lambda>i ia. iterate ia\<cdot>(Y i)\<cdot>x)"
      apply (simp add: chain_def)
      by (simp add: fun_belowI monofun_cfun)
    then show "\<And>x. range (\<lambda>i. \<Squnion>ia. iterate ia\<cdot>(Y i)\<cdot>x) <<| (\<Squnion>i. iterate i\<cdot>(\<Squnion>i. Y i)\<cdot>x)"   
      apply(simp add: lub_fun contlub_cfun_fun contlub_cfun_arg c1)
        sorry         
  qed
qed
   *)

    
    
(*fixg gives the least fixpoint, if x \<sqsubseteq> F\<cdot>x*)

lemma fixg_fix:assumes" x \<sqsubseteq> F\<cdot>x " and "\<forall> y. y \<sqsubseteq> x \<longrightarrow> x = y"
  shows "fixg x F = F\<cdot>(fixg x F)"
  apply (simp add: fixg_def)
  apply (subst lub_range_shift [of _ 1, symmetric])
  apply(rule chainI)
  apply(subst iterate_Suc2)
  apply(rule Cfun.monofun_cfun_arg, simp add: assms)
  apply (subst contlub_cfun_arg)
  apply(rule chainI)
  apply(subst iterate_Suc2)
  apply(rule Cfun.monofun_cfun_arg, simp add: assms)
  by simp
    
lemma fixg_least_below:assumes" x \<sqsubseteq> F\<cdot>x " and "\<forall> y. y \<sqsubseteq> x \<longrightarrow> x = y" and "x \<sqsubseteq> y"
  shows "F\<cdot>y \<sqsubseteq> y \<Longrightarrow> (fixg x F) \<sqsubseteq> y"
  apply (simp add: fixg_def)
  apply (rule lub_below)
  apply(rule chainI)
  apply(subst iterate_Suc2)
  apply(rule Cfun.monofun_cfun_arg, simp add: assms)
  apply (induct_tac i)
  apply (simp add: assms)
  apply (simp add: assms(1))
  apply (erule rev_below_trans)
  by (erule monofun_cfun_arg)


lemma fixg_least_fix:assumes"F\<cdot>y = y" and "x \<sqsubseteq> y" and "x \<sqsubseteq> F\<cdot>x" and "\<forall> y. y \<sqsubseteq> x \<longrightarrow> x = y"
  shows "fixg x F \<sqsubseteq> y"
  by(subst fixg_least_below, simp_all add: assms)  
    
end
  