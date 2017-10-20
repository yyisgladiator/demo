(*  Title:        SPF
    Author:       Jens Christoph Bürger
    e-mail:       jens.buerger@rwth-aachen.de

    Description:  Extends "Stream Processing Functions"
*)

theory SPF_JB
imports SPF

begin
  
default_sort message 

(*
declare [[show_types]]
declare [[show_consts]]
*)

section \<open>definitions\<close>

definition spfApplyOut :: "('a SB \<rightarrow> 'a SB) \<Rightarrow> 'a SPF \<rightarrow> 'a SPF" where
"spfApplyOut k \<equiv> (\<Lambda> g. Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x)))"



section \<open>spfApplyOut\<close>

lemma spfapplyout_cont [simp]: "cont (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x))"
proof (rule spf_contI)
  show "\<And>x y. sbDom\<cdot>x = spfDom\<cdot>g \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> k\<cdot>(g \<rightleftharpoons> x) \<sqsubseteq> k\<cdot>(g \<rightleftharpoons> y)"
    using monofun_cfun_arg spf_pref_eq by blast

  show "\<And>Y. chain Y \<Longrightarrow> sbDom\<cdot>(\<Squnion>i. Y i) = spfDom\<cdot>g \<Longrightarrow> k\<cdot>(g \<rightleftharpoons> (\<Squnion>i. Y i)) \<sqsubseteq> (\<Squnion>i. k\<cdot>(g \<rightleftharpoons> Y i))"
    proof -
    fix Y :: "nat \<Rightarrow> 'a SB"
    assume a1: "chain Y"
      have f2: "\<forall>f c. \<not> chain f \<or> (c\<cdot>(Lub f::'a SB)::'b) = (\<Squnion>n. c\<cdot>(f n))"
        using contlub_cfun_arg by blast
      have f3: "Rep_CSPF g (Lub Y) = (\<Squnion>n. Rep_CSPF g (Y n))"
        using a1 contlub_cfun_arg by blast
      have "\<forall>f. \<not> chain f \<or> lub\<rightharpoonup>range f = (\<Squnion>n. (f\<rightharpoonup>n::'a SB))"
        using op_the_lub by blast
      hence "(\<Squnion>n. k\<cdot>\<lambda>n. Rep_CSPF g (Y n)\<rightharpoonup>n) = k\<cdot>(g \<rightleftharpoons> Lub Y)"
        using f3 f2 a1 by (metis (no_types) ch2ch_Rep_cfunR op_the_chain)
      thus "k\<cdot>(g \<rightleftharpoons> (\<Squnion>n. Y n)) \<sqsubseteq> (\<Squnion>n. k\<cdot>(g \<rightleftharpoons> Y n))"
        by auto
    qed
qed  

 (* intro lemma for spe_well proofs with spf_applyout *)
lemma spfapplyout_wellI [simp]: assumes "\<And>b. sbDom\<cdot>b = spfDom\<cdot>g \<Longrightarrow> sbDom\<cdot>(k\<cdot>(g \<rightleftharpoons> b)) = cs"
  shows "spf_well (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>g) \<leadsto> k\<cdot>(g \<rightleftharpoons>x))"
  apply (rule spf_wellI)
  apply (simp_all add: domIff2)
  by (simp add: assms)

end