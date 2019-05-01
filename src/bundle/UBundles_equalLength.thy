theory UBundles_equalLength
imports inc.UnivClasses UBundle

begin

definition ub_eqLen :: "'s ubundle \<Rightarrow> bool" where
"ub_eqLen ub \<equiv> (\<forall> c1 \<in> (ubDom\<cdot>ub). \<forall> c2 \<in> (ubDom\<cdot>ub). usclLen\<cdot>(ub . c1) = usclLen\<cdot>(ub . c2))"

cpodef 's::uscl eqLenBundle = "{b :: 's ubundle. ub_eqLen b}"
  using ubWell_empty
  using ub_eqLen_def ubdom_ubrep_eq apply fastforce
proof -
  have "\<And>(Y :: nat \<Rightarrow> 's ubundle). chain Y \<Longrightarrow> (\<forall>i. ub_eqLen (Y i)) \<Longrightarrow> ub_eqLen (Lub Y)"
  proof -
    fix Y :: "nat \<Rightarrow> 's ubundle"
    assume f0: "chain Y" and f1: "\<forall>i. ub_eqLen (Y i)"
    have f2: "\<forall>i. ubDom\<cdot>(Y i) = ubDom\<cdot>(Lub Y)"
      using f0 by simp
    show f3: "(ub_eqLen (Lub Y))" using f2 f0 f1 contlub_cfun_arg lub_eq
      by (smt ub_eqLen_def ubgetch_insert ubrep_chain_the ubrep_lub_eval)
  qed
  then show "adm (\<lambda>x::'s\<^sup>\<Omega>. x \<in> {b::'s\<^sup>\<Omega>. ub_eqLen b})"
    by (simp add: adm_def)
qed
setup_lifting type_definition_eqLenBundle
end