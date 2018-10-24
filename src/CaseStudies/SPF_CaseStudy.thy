theory SPF_CaseStudy
imports  "../SPF"  "../Streams" StreamCase_Study

begin

(*instantiation nat :: message
begin
  definition ctype_nat :: "channel \<Rightarrow> nat set" where
  "ctype c = range nat"

instance ..
end*)


lemma [simp]: "cs \<subseteq> ((ctype c) :: nat set)"
apply(simp add: ctype_nat_def)
by (metis subset_UNIV subset_image_iff transfer_int_nat_set_return_embed)

lemma sbAdd_chain[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {c1,c3} \<Longrightarrow> chain (\<lambda> i. [c2 \<mapsto> add\<cdot>(Y i . c1)\<cdot>(Y i . c3)]\<Omega>)"
  apply(rule chainI)
  apply(rule sb_below)
   apply (simp add: sbdom_rep_eq)
  apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)

lemma sbAdd_chain1[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {c1,c3} \<Longrightarrow> chain (\<lambda> i. [c2 \<mapsto> add\<cdot>(Y i . c1)\<cdot>(Y i . c3)]\<Omega>)"
by (simp add: sbChain_dom_eq2)

lemma sAdd_Lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {c1,c3} \<Longrightarrow> 
  (\<Squnion>i. add\<cdot>(Y i . c1)\<cdot>(Y i . c3)) = add\<cdot>((Lub Y) . c1)\<cdot>((Lub Y). c3) "
proof -
  assume a1: "chain Y"
  have f2: "\<forall>f fa. (\<not> chain f \<or> \<not> chain fa) \<or> (\<Squnion>n. (f n\<cdot>(fa n::nat stream)::nat stream)) = Lub f\<cdot>(Lub fa)"
    using lub_APP by blast
  have f3: "\<forall>f c. \<not> chain f \<or> chain (\<lambda>n. f n\<cdot>(c::channel)::nat stream)"
    using ch2ch_Rep_cfunL by blast
  have f4: "chain (\<lambda>n. sbGetCh\<cdot>(Y n))"
    using a1 ch2ch_Rep_cfunR by blast
  have f5: "\<forall>f c. \<not> chain f \<or> chain (\<lambda>n. c\<cdot>(f n::nat stream)::nat stream \<rightarrow> nat stream)"
    using ch2ch_Rep_cfunR by blast
  have f6: "\<forall>f c. \<not> chain f \<or> (c\<cdot>(Lub f::nat stream)::nat stream \<rightarrow> nat stream) = (\<Squnion>n. c\<cdot>(f n))"
    using contlub_cfun_arg by blast
  have f7: "\<forall>f c. \<not> chain f \<or> (c\<cdot>(Lub f::nat SB)::channel \<rightarrow> nat stream) = (\<Squnion>n. c\<cdot>(f n))"
    using contlub_cfun_arg by blast
  have "\<forall>f c. \<not> chain f \<or> (Lub f\<cdot>(c::channel)::nat stream) = (\<Squnion>n. f n\<cdot>c)"
    using contlub_cfun_fun by blast
  then have "(\<Squnion>n. add\<cdot>(Y n . c1)\<cdot>(Y n . c3)) = add\<cdot>(Lub Y . c1)\<cdot>(Lub Y . c3)"
    using f7 f6 f5 f4 f3 f2 a1 by presburger
  then show ?thesis
    by fastforce
qed


lemma spfAdd_mono[simp]: "monofun (\<lambda> sb. (sbDom\<cdot>sb = {c1, c3}) \<leadsto> ([c2\<mapsto>add\<cdot>(sb . c1)\<cdot>(sb . c3)]\<Omega>))" (is "monofun ?F")
  apply(rule spf_mono2monofun)
   apply(rule spf_monoI)
   apply(simp add: domIff2)
   apply(rule sb_below)
    apply (simp add: sbdom_insert)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   apply (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
  apply rule
  by(simp add: domIff2)

lemma spfAdd_chain [simp]: "chain Y \<Longrightarrow> chain (\<lambda> i. (sbDom\<cdot>(Y i) = {c1, c3}) \<leadsto> ([c2\<mapsto>add\<cdot>((Y i) . c1)\<cdot>((Y i) . c3)]\<Omega>))" 
  apply(rule chainI)
  apply (simp add: sbChain_dom_eq2)
  apply(rule impI, rule some_below, rule sb_below)
   apply (simp add: sbdom_insert)
  apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)

lemma lub_insert: "chain Y \<Longrightarrow>(\<Squnion>i. Y i) . c =  (\<Squnion>i. (Y i) .c)"
by (metis (mono_tags, lifting) lub_eq lub_eval sbgetch_insert)

lemma spfAdd_cont[simp]: "cont (\<lambda> sb. (sbDom\<cdot>sb = {c1, c3}) \<leadsto> ([c2\<mapsto>add\<cdot>(sb . c1)\<cdot>(sb . c3)]\<Omega>))" (is "cont ?F")
  apply(rule spf_cont2cont)
    apply(rule spf_contlubI)
    apply(simp add: domIff2 sbChain_dom_eq2)
    apply(rule sb_below)
     apply (simp add: sbdom_rep_eq )
     apply(simp only: Cfun.contlub_cfun_arg sbAdd_chain1)
     apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
    apply(simp add: sbdom_rep_eq sbgetch_rep_eq lub_insert)
   apply (simp add: monofun2spf_mono)
  apply(simp add: domIff2)
  by rule+

lift_definition addComp :: "nat SPF" is 
"\<Lambda> sb. (sbDom\<cdot>sb = {c1, c3}) \<leadsto> ([c2\<mapsto>add\<cdot>(sb . c1)\<cdot>(sb . c3)]\<Omega>)"
by(auto simp add: spf_well_def domIff2 sbdom_rep_eq)






(* Sum1 *)

lemma sum1_monofun [simp]: "monofun (\<lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2\<mapsto>add\<cdot>(sum3\<cdot>(sb . c1))\<cdot>oracle]\<Omega>))"
  apply(rule spf_mono2monofun)
   apply(rule spf_monoI)
   apply(simp add: domIff2)
   apply(rule sb_below)
    apply (simp add: sbdom_insert)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   apply (simp add: monofun_cfun_arg monofun_cfun_fun)
  apply(simp add: domIff2)
  by rule+

lemma sum1_cont_help[simp]: "\<And>Y. chain Y \<Longrightarrow> sbDom\<cdot>(\<Squnion>j. Y j) = {c1} \<Longrightarrow> chain (\<lambda>i. [c2 \<mapsto> add\<cdot>(sum3\<cdot>(Y i . c1))\<cdot>oracle]\<Omega>)"
  apply(rule chainI)
  apply(rule sb_below)
   apply (simp add: sbdom_insert)
  apply(simp add: sbdom_insert sbgetch_insert)
  by (smt monofun_cfun monofun_cfun_arg monofun_cfun_arg po_class.chain_def po_eq_conv theRep_chain)

lemma sum1_cont [simp]: "cont (\<lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2\<mapsto>add\<cdot>(sum3\<cdot>(sb . c1))\<cdot>oracle]\<Omega>))"
  apply(rule spf_cont2cont)
    apply(rule spf_contlubI)
    apply(simp add: domIff2 sbChain_dom_eq2)
    apply(rule sb_below)
     apply (simp add: sbdom_rep_eq )
     apply(subst contlub_cfun_arg, simp)
     apply (simp add: sbdom_rep_eq )
    apply(simp add: sbdom_rep_eq sbgetch_rep_eq lub_insert)
    apply (smt contlub_cfun_arg contlub_cfun_fun lub_eq monofun_cfun_arg monofun_cfun_fun po_class.chainE po_class.chainI po_eq_conv)
   apply (simp add: monofun2spf_mono)
  apply(auto simp add: domIff)
done

lemma sum1_well [simp]:"spf_well (\<Lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2\<mapsto>add\<cdot>(sum3\<cdot>(sb . c1))\<cdot>oracle]\<Omega>))"
by(auto simp add: spf_well_def domIff2 sbdom_rep_eq)



(* define sum1 components *)
definition sum1Comp :: "nat stream \<Rightarrow> nat SPF" where
"sum1Comp oracle \<equiv> Abs_SPF (\<Lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2\<mapsto>add\<cdot>(sum3\<cdot>(sb . c1))\<cdot>oracle]\<Omega>))"

lemma sum1Comp_rep_eq: "Rep_SPF (sum1Comp oracle) = (\<Lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2\<mapsto>add\<cdot>(sum3\<cdot>(sb . c1))\<cdot>oracle]\<Omega>))"
by(simp add: sum1Comp_def)

lemma sum1Comp_rep_eqC: "Rep_CSPF (sum1Comp oracle) = (\<lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2\<mapsto>add\<cdot>(sum3\<cdot>(sb . c1))\<cdot>oracle]\<Omega>))"
by(simp add: sum1Comp_def Rep_CSPF_def)

lemma sum1Comp_dom [simp]: "spfDom\<cdot>(sum1Comp oracle) = {c1}"
  apply(simp add: spfdom_insert Rep_CSPF_def sum1Comp_rep_eq)
  apply(simp add: domIff2)
  by (meson sbleast_sbdom someI)

lemma sum1Comp_ran [simp]: "spfRan\<cdot>(sum1Comp oracle) = {c2}"
  apply(simp add: spfran_least)
  apply(simp add: sum1Comp_rep_eqC)
  by(simp add: sbdom_insert)
  

lemma sum1Comp_apply: "(Rep_CSPF (sum1Comp oracle)) \<rightharpoonup> ([c1 \<mapsto> s]\<Omega>) . c2 = add\<cdot>(sum3\<cdot>s)\<cdot>oracle"
apply(simp add: Rep_CSPF_def sum1Comp_rep_eq sbdom_rep_eq)
by(simp add: sbgetch_insert)



lift_definition sum1 :: "nat SPS" is "{ sum1Comp oracle | oracle. #oracle = \<infinity>}" 
proof(rule sps_wellI)
  fix f
  assume "f \<in> {sum1Comp oracle |oracle. #oracle = \<infinity>}"
  obtain "oracle" where f_sum: "f = sum1Comp oracle" using \<open>f \<in> {sum1Comp oracle |oracle. #oracle = \<infinity>}\<close> by blast
  thus "spfDom\<cdot>f={c1}" by simp
  thus "spfRan\<cdot>f={c2}" by (simp add: f_sum)
qed

lemma [simp]:"spsDom sum1 = {c1}"
  apply(simp add: spsDom_def sum1.rep_eq)
  by (smt singletonD someI_ex sum1Comp_dom zed_len)

lemma [simp]: "spsRan sum1 = {c2}"
  apply(simp add: spsRan_def sum1.rep_eq)
  by (smt siterateBlock_len someI_ex sum1Comp_ran)

lemma sum1_len: assumes "f\<in>(Rep_SPS sum1)" 
  shows "#((Rep_CSPF f) \<rightharpoonup> ([c1 \<mapsto> s]\<Omega>) . c2) = #s" 
proof -
  obtain "oracle" where f_sum: "f = sum1Comp oracle \<and> #oracle=\<infinity>" using assms sum1.rep_eq by blast
  thus ?thesis by (simp add:  add_commutative sum1Comp_apply sum3_def) 
qed

lemma sum1_apply: assumes "f\<in>(Rep_SPS sum1)" and "Fin n < #s"
  shows "snth n ((Rep_CSPF f) \<rightharpoonup> ([c1 \<mapsto> s]\<Omega>) . c2) \<ge> snth n (sum3\<cdot>s)" (is "?L \<ge> ?R")
proof -
  obtain "oracle" where f_sum: "f = sum1Comp oracle \<and> #oracle=\<infinity>" using assms sum1.rep_eq by blast
  hence "?L = snth n (add\<cdot>(sum3\<cdot>s)\<cdot>oracle)" by (simp add: sum1Comp_apply)
  hence "?L = snth n (sum3\<cdot>s) + snth n oracle" by(simp add: f_sum add_snth assms)
  thus ?thesis by simp 
qed

lemma "\<exists>f\<in>(Rep_SPS sum1). (Rep_CSPF f) \<rightharpoonup> ([c1 \<mapsto> s]\<Omega>) . c2 = sum3\<cdot>s"
proof -
  have f1: "sum1Comp \<up>0\<infinity> \<in> (Rep_SPS sum1)" using sum1.rep_eq by auto 
  have "(Rep_CSPF (sum1Comp \<up>0\<infinity>)) \<rightharpoonup> ([c1 \<mapsto> s]\<Omega>) . c2 = sum3\<cdot>s" by(simp add: sum1Comp_apply)
  thus ?thesis using local.f1 by blast 
qed






(* Das war ein test um einfacher die stetigkeit von SPF's zu zeigen *)
(* hat (bisher) nicht wirklich gekalappt... *)
lemma contSPF: fixes g:: "'m SB \<Rightarrow> 'm SB"
  assumes "\<And>Y. chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = cs \<Longrightarrow> g (\<Squnion>i. Y i) = (\<Squnion>i. g (Y i))"
  shows "cont (\<lambda>sb. (sbDom\<cdot>sb = cs) \<leadsto> g sb)" (is "cont ?F")
  apply(rule spf_cont2cont)
    apply(rule spf_contlubI)
    apply (smt assms domIff lub_eq option.sel po_eq_conv sbChain_dom_eq2)
   apply(rule spf_monoI)
(*   apply (simp_all add: domIff2) *)
   sorry

lemma sbdom_Lub20: "chain Y \<Longrightarrow> sbDom\<cdot>(\<Squnion>i. Y i) = sbDom\<cdot>(Y 0)"
  using sbChain_dom_eq2 by blast


lemma zeroComp_cont[simp] : "cont (\<lambda> sb :: nat SB . (sbDom\<cdot>sb = {c2}) \<leadsto> [c1 \<mapsto> \<up>0 \<bullet> (sb . c2)]\<Omega>)"
(*  apply(rule contSPF)
  apply(rule sb_eq)
   apply(simp add: sbdom_rep_eq sbdom_Lub20)
   apply(subst sbdom_Lub20)
    apply(rule chainI, rule sb_below)
     apply(simp add: sbdom_rep_eq)
    apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
    apply (simp add: monofun_cfun_arg monofun_cfun_fun po_class.chainE)
   apply(simp add: sbdom_rep_eq)
  apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
  apply meson
  apply(simp add: lub_insert)
  apply(subst lub_insert)
   apply(rule chainI, rule sb_below)
    apply(simp add: sbdom_rep_eq)
   apply(simp add: sbgetch_rep_eq)
   apply (rule impI)
   apply (simp add: monofun_cfun_arg monofun_cfun_fun po_class.chainE)
  by(simp add: sbgetch_rep_eq contlub_cfun_arg)
*)
  sorry


lift_definition zeroComp :: "nat SPF" is 
"\<Lambda> sb . (sbDom\<cdot>sb = {c2}) \<leadsto> [c1 \<mapsto> \<up>0 \<bullet> (sb . c2)]\<Omega>"
(*
by(auto simp add: spf_well_def domIff2 sbdom_rep_eq)
*)
sorry

(*
(* to simplify the welltyped proofs define that alle Channels have the type "Nat" *)
lemma ctype_simp [simp]: "ctype c = range Nat"
using ctype.elims by blast *)

end
