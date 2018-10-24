section {* cpo fixpoint *}

theory CPOFix
imports Prelude
begin

default_sort type
  
(* genaral fixpoint over cpo, x is \<sqsubseteq> f x*)  
  
definition fixg::"('a::cpo) \<Rightarrow> ('a \<rightarrow> 'a) \<rightarrow> 'a" where
"fixg = (\<lambda> x. \<Lambda> F. if x \<sqsubseteq> F\<cdot>x then \<Squnion>i. iterate i\<cdot>F\<cdot>x else x)"
    
lemma iter_fixg_mono2: assumes "x \<sqsubseteq> y" and "F1 \<sqsubseteq> F2"
  shows "\<forall>i . (iterate i\<cdot>F1\<cdot>x) \<sqsubseteq> (iterate i\<cdot>F2\<cdot>y)"
  by (simp add: assms(1) assms(2) monofun_cfun)
    
lemma iter_fixg_chain: assumes "x \<sqsubseteq> F\<cdot>x"
  shows "chain (\<lambda>i. iterate i\<cdot>F\<cdot>x)"
    apply (rule chainI)
  by (metis assms cont_pref_eq1I iterate_Suc2)
        
lemma lub_iter_fixg_mono_req: assumes "F1 \<sqsubseteq> F2" and "x \<sqsubseteq> F1\<cdot>x" and "x\<sqsubseteq>F2\<cdot>x"
  shows "(\<Squnion>i. iterate i\<cdot>F1\<cdot>x) \<sqsubseteq> (\<Squnion>i. iterate i\<cdot>F2\<cdot>x)"
proof -
  have "\<forall>i. (iterate i\<cdot>F1\<cdot>x) \<sqsubseteq> (iterate i\<cdot>F2\<cdot>x)"
    by (simp add: iter_fixg_mono2 assms(1) assms(2))
   then show ?thesis
    by (simp add: lub_mono assms iter_fixg_mono2 iter_fixg_chain)
qed

(*cont (\<lambda> F. fixg x F)*)
  
lemma fixg_pre:"x \<sqsubseteq> (if x \<sqsubseteq> F\<cdot>x then \<Squnion>i. iterate i\<cdot>F\<cdot>x else x)" 
proof(cases "x\<sqsubseteq>F\<cdot>x")
  case True
  then show ?thesis
  proof -
    have "\<And>n. iterate n\<cdot>F\<cdot>x \<sqsubseteq> (\<Squnion>n. iterate n\<cdot>F\<cdot>x)"
      using True is_ub_thelub iter_fixg_chain by blast
    then have "x \<sqsubseteq> (\<Squnion>n. iterate n\<cdot>F\<cdot>x)"
      by (metis iterate_0)
    then show ?thesis
      using True by presburger
  qed
next
  case False
  then show ?thesis 
    by simp
qed

lemma fixg_mono[simp]:"monofun (\<lambda>F. if x \<sqsubseteq> F\<cdot>x then \<Squnion>i. iterate i\<cdot>F\<cdot>x else x)"
proof(rule monofunI)
   fix xa::"'a \<rightarrow> 'a" and y::"'a \<rightarrow> 'a"
  assume a1:"xa \<sqsubseteq> y"
  show "(if x \<sqsubseteq> xa\<cdot>x then \<Squnion>i. iterate i\<cdot>xa\<cdot>x else x) \<sqsubseteq> (if x \<sqsubseteq> y\<cdot>x then \<Squnion>i. iterate i\<cdot>y\<cdot>x else x)"
  proof(cases "x \<sqsubseteq> xa \<cdot>x")
    case True
    then have "x \<sqsubseteq> y\<cdot>x"
      using a1 cfun_below_iff rev_below_trans by blast
    then show ?thesis 
      by (simp add: True a1 lub_iter_fixg_mono_req)
  next
    case False
    then show ?thesis
      by(simp add: fixg_pre)
  qed
qed 
  
  
lemma fixg_cont[simp]:assumes "\<And> y z. x\<sqsubseteq>z \<and> y\<sqsubseteq>z \<longrightarrow> x\<sqsubseteq>y" shows "cont (\<lambda>F. if x \<sqsubseteq> F\<cdot>x then \<Squnion>i. iterate i\<cdot>F\<cdot>x else x)"
proof(rule Cont.contI2, simp)
fix Y:: "nat \<Rightarrow> ('a \<rightarrow> 'a)"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i. if x \<sqsubseteq> Y i\<cdot>x then \<Squnion>ia. iterate ia\<cdot>(Y i)\<cdot>x else x)"
  show "(if x \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x then \<Squnion>i. iterate i\<cdot>(\<Squnion>i. Y i)\<cdot>x else x) \<sqsubseteq> (\<Squnion>i. if x \<sqsubseteq> Y i\<cdot>x then \<Squnion>ia. iterate ia\<cdot>(Y i)\<cdot>x else x)"
  proof(cases "x \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x")
    case True
    then show ?thesis
    proof(cases "\<exists>i. x \<sqsubseteq> (Y i)\<cdot>x")
      case True
      then have h1:"\<forall>i. x \<sqsubseteq> Y i \<cdot>x"
        by (meson a1 assms cfun_below_iff is_ub_thelub rev_below_trans)
      then have h2:"(\<Squnion>i. if x \<sqsubseteq> Y i\<cdot>x then \<Squnion>ia. iterate ia\<cdot>(Y i)\<cdot>x else x) = (\<Squnion>i.\<Squnion>ia. iterate ia\<cdot>(Y i)\<cdot>x)"
        by simp
      have h3:"(if x \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x then \<Squnion>i. iterate i\<cdot>(\<Squnion>i. Y i)\<cdot>x else x) = (\<Squnion>i. iterate i\<cdot>(\<Squnion>ia. Y ia)\<cdot>x)"
        by (meson True a1 below_trans cfun_below_iff is_ub_thelub)
      have h4:"(\<Squnion>i. iterate i\<cdot>(\<Squnion>ia. Y ia)\<cdot>x) = (\<Squnion>i.\<Squnion>ia. iterate i\<cdot>( Y ia)\<cdot>x)"
        by(simp add: a1 contlub_cfun_fun contlub_cfun_arg)
      show ?thesis
      proof-
        show "(if x \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x then \<Squnion>i. iterate i\<cdot>(\<Squnion>i. Y i)\<cdot>x else x) \<sqsubseteq> (\<Squnion>i. if x \<sqsubseteq> Y i\<cdot>x then \<Squnion>ia. iterate ia\<cdot>(Y i)\<cdot>x else x)"
          by(simp_all add: h2 h3  h4 diag_lub a1 h1 iter_fixg_chain)
      qed
    next
      case False
      have h1:"(\<Squnion>i. Y i)\<cdot>x = x"
      proof-
        have "x \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x"
          by(simp add: True)
        have "\<forall>i. Y i\<cdot>x \<sqsubseteq> x"
          using False True a1 assms cfun_below_iff is_ub_thelub by blast
        then show "(\<Squnion>i. Y i)\<cdot>x = x"
          by (metis True a1 below_antisym ch2ch_Rep_cfunL contlub_cfun_fun lub_below_iff)
      qed     
      have "\<forall>i. iterate i\<cdot>(\<Squnion>i. Y i)\<cdot>x = x"
      proof(auto)
        fix i::nat
        show "iterate i\<cdot>(\<Squnion>i. Y i)\<cdot>x = x"
        proof(induction i)
          case 0
          then show ?case
            by simp
        next
          case (Suc i)
          then show ?case
            by (simp add: h1) 
        qed
      qed
      then have "(\<Squnion>i. iterate i\<cdot>(\<Squnion>i. Y i)\<cdot>x) = x"
        by auto
      then show ?thesis
        using False by auto 
    qed
  next
    case False
    then show ?thesis
      using a2 below_lub fixg_pre by fastforce 
  qed
qed

lemma fixg_apply: assumes "\<And> y z. x\<sqsubseteq>z \<and> y\<sqsubseteq>z \<longrightarrow> x\<sqsubseteq>y"
  shows "fixg x\<cdot>F = (if x \<sqsubseteq> F\<cdot>x then \<Squnion>i. iterate i\<cdot>F\<cdot>x else x)"
  by (simp add: assms fixg_def)

(*fixg gives the least fixpoint, if x \<sqsubseteq> F\<cdot>x*)

lemma fixg_fix:assumes" x \<sqsubseteq> F\<cdot>x " and "\<And>y z. x \<sqsubseteq> z \<and> y \<sqsubseteq> z \<longrightarrow> x \<sqsubseteq> y"
  shows "fixg x\<cdot> F = F\<cdot>(fixg x\<cdot>F)"
  apply (simp add: fixg_def assms)
  apply (subst lub_range_shift [of _ 1, symmetric])
  apply(rule chainI)
  apply(subst iterate_Suc2)
  apply(rule Cfun.monofun_cfun_arg, simp add: assms)
  apply (subst contlub_cfun_arg)
  apply(rule chainI)
  apply(subst iterate_Suc2)
  apply(rule Cfun.monofun_cfun_arg, simp add: assms)
  by simp
    
lemma fixg_least_below:assumes" x \<sqsubseteq> F\<cdot>x " and "\<And>y z. x \<sqsubseteq> z \<and> y \<sqsubseteq> z \<longrightarrow> x \<sqsubseteq> y" and "x \<sqsubseteq> y"
  shows "F\<cdot>y \<sqsubseteq> y \<Longrightarrow> (fixg x\<cdot> F) \<sqsubseteq> y"
  apply (simp add: fixg_def assms)
  apply (rule lub_below)
  apply(rule chainI)
  apply(subst iterate_Suc2)
  apply(rule Cfun.monofun_cfun_arg, simp add: assms)
  apply (induct_tac i)
  apply (simp add: assms)
  apply (simp add: assms(1))
  apply (erule rev_below_trans)
  by (erule monofun_cfun_arg)


lemma fixg_least_fix:assumes"F\<cdot>y = y" and "x \<sqsubseteq> y" and "x \<sqsubseteq> F\<cdot>x" and "\<And>y z. x \<sqsubseteq> z \<and> y \<sqsubseteq> z \<longrightarrow> x \<sqsubseteq> y"
  shows "fixg x\<cdot> F \<sqsubseteq> y"
  by(subst fixg_least_below, simp_all add: assms)  
    
end
  