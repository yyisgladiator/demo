theory Feedback_MW
imports SPF Streams SBTheorie ParComp_MW StreamCase_Study SPF_MW SerComp_JB

begin

(* Add component *)

lemma spfadd_mono[simp] : "monofun 
                           (\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) \<leadsto> ([ch3 \<mapsto> add\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))"
  apply (rule spf_mono2monofun)
   apply (rule spf_monoI)
   apply (simp add: domIff2)
   apply (rule sb_below)
    apply (simp add: sbdom_insert)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   apply (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
   by (rule, simp add: domIff2)

lemma add_chain[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {ch1,ch2} 
                        \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto>add\<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2)]\<Omega>)"
  apply (rule chainI)
  apply (rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (simp add: monofun_cfun po_class.chainE)

lemma add_chain_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1,ch2} 
                                \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto>add\<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2)]\<Omega>)"
  by (simp add: sbChain_dom_eq2)

lemma sAdd_Lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1,ch2} \<Longrightarrow> 
  (\<Squnion>i. add\<cdot>(Y i . ch1)\<cdot>(Y i . ch2)) = add\<cdot>((Lub Y) . ch1)\<cdot>((Lub Y). ch2)"
  by (simp add: lub_distribs(1) lub_eval)

lemma spfadd_chain [simp]: "chain Y \<Longrightarrow>
      chain (\<lambda> i. (sbDom\<cdot>(Y i) = {ch1, ch2}) \<leadsto> ([ch3\<mapsto>add\<cdot>((Y i) . ch1)\<cdot>((Y i) . ch2)]\<Omega>))"
  apply (rule chainI)
  apply (simp add: sbChain_dom_eq2)
  apply (rule impI, rule some_below, rule sb_below)
   apply (simp add: sbdom_rep_eq)
  apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)

lemma spfadd_cont[simp]: "cont (\<lambda> sb. (sbDom\<cdot>sb = {ch1, ch2}) 
                                \<leadsto> ([ch3\<mapsto>add\<cdot>(sb . ch1)\<cdot>(sb . ch2)]\<Omega>))" (is "cont ?F")
  apply (rule spf_cont2cont)
    apply (rule spf_contlubI)
    apply (simp add: domIff2 sbChain_dom_eq2)
    apply (rule sb_below)
     apply (simp add: sbdom_rep_eq )
     apply (simp only: Cfun.contlub_cfun_arg add_chain_lub)
     apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
   apply (simp add: monofun2spf_mono)
  by(simp add: domIff2, rule+)

(* Delay component *)

definition delay:: "nat stream  \<rightarrow> nat stream" where
"delay \<equiv> \<Lambda> s . \<up>0 \<bullet> s"

lemma spfdelay_mono[simp] : "monofun (\<lambda> sb. (sbDom\<cdot>sb = {ch3}) \<leadsto> ([ch2\<mapsto>delay\<cdot>(sb . ch3)]\<Omega>))"
  apply (rule spf_mono2monofun)
   apply (rule spf_monoI)
   apply (simp add: domIff2)
   apply (rule sb_below)
    apply (simp add: sbdom_insert)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   apply (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
   by (rule, simp add: domIff2)

lemma delay_chain[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {ch3} 
                        \<Longrightarrow> chain (\<lambda> i. [ch2\<mapsto>delay\<cdot>((Y i) . ch3)]\<Omega>)"
  apply (rule chainI)
  apply (rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (simp add: monofun_cfun po_class.chainE)

lemma delay_chain_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch3} 
                                \<Longrightarrow> chain (\<lambda> i. [ch2\<mapsto>delay\<cdot>((Y i) . ch3)]\<Omega>)"
  by (simp add: sbChain_dom_eq2)

lemma delay_Lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch3} \<Longrightarrow> 
  (\<Squnion>i. delay\<cdot>(Y i . ch3)) = delay\<cdot>((Lub Y). ch3)"
  by (simp add: lub_distribs(1) lub_eval)

lemma spfdelay_chain [simp]: "chain Y \<Longrightarrow>
      chain (\<lambda> i. (sbDom\<cdot>(Y i) = {ch3}) \<leadsto> ([ch2\<mapsto>delay\<cdot>((Y i) . ch3)]\<Omega>))"
  apply (rule chainI)
  apply (simp add: sbChain_dom_eq2)
  apply (rule impI, rule some_below, rule sb_below)
   apply (simp add: sbdom_rep_eq)
  apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)

lemma spfdelay_cont[simp]: "cont (\<lambda> sb. (sbDom\<cdot>sb = {ch3}) 
                                \<leadsto> ([ch2\<mapsto>delay\<cdot>(sb . ch3)]\<Omega>))" (is "cont ?F")
  apply (rule spf_cont2cont)
    apply (rule spf_contlubI)
    apply (simp add: domIff2 sbChain_dom_eq2)
    apply (rule sb_below)
     apply (simp add: sbdom_rep_eq )
     apply (simp only: Cfun.contlub_cfun_arg delay_chain_lub)
     apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
   apply (simp add: monofun2spf_mono)
  by(simp add: domIff2, rule+)


(* SPF Definition *)

lift_definition addC :: "nat SPF" is
"\<Lambda> sb. (sbDom\<cdot>sb = {c1, c2}) \<leadsto> ([c3\<mapsto>add\<cdot>(sb . c1)\<cdot>(sb . c2)]\<Omega>)"
  by (auto simp add: spf_well_def domIff2 sbdom_rep_eq)

lift_definition delayC :: "nat SPF" is
"\<Lambda> sb. (sbDom\<cdot>sb = {c3}) \<leadsto> ([c2\<mapsto>delay\<cdot>(sb . c3)]\<Omega>)"
  by (auto simp add: spf_well_def domIff2 sbdom_rep_eq)

(* component properties *)

lemma add_rep_eqC: "Rep_CSPF addC = (\<lambda> sb. (sbDom\<cdot>sb = {c1, c2}) \<leadsto> ([c3\<mapsto>add\<cdot>(sb . c1)\<cdot>(sb . c2)]\<Omega>))"
  by (simp add: addC.rep_eq Rep_CSPF_def)

lemma delay_rep_eqC: "Rep_CSPF delayC = (\<lambda> sb. (sbDom\<cdot>sb = {c3}) \<leadsto> ([c2\<mapsto>delay\<cdot>(sb . c3)]\<Omega>))"
  by (simp add: delayC.rep_eq Rep_CSPF_def)

lemma [simp]: "spfDom\<cdot>addC = {c1,c2}"
  apply(simp add: spfdom_insert addC.rep_eq Rep_CSPF_def domIff2)
  by (meson sbleast_sbdom someI_ex)

lemma [simp]: "spfRan\<cdot>addC = {c3}"
  apply (simp add: spfran_least add_rep_eqC)
  by (simp add: sbdom_insert)

lemma [simp]: "spfDom\<cdot>delayC = {c3}"
  apply(simp add: spfdom_insert delayC.rep_eq Rep_CSPF_def domIff2)
  by (meson sbleast_sbdom someI_ex)

lemma [simp]: "spfRan\<cdot>delayC = {c2}"
  apply (simp add: spfran_least delay_rep_eqC)
  by (simp add: sbdom_insert)

(* composition prerequirements *)

lemma [simp]: "spfComp_well addC delayC"
  by (simp add: spfComp_well_def)

lemma [simp]: "C addC delayC = {c1,c2,c3}"
  by (auto simp add: C_def)

lemma [simp]: "L addC delayC = {c2, c3}"
  by (auto simp add: L_def)

lemma [simp]: "Oc addC delayC = {c2, c3}"
  by (auto simp add: Oc_def)

lemma [simp]: "I addC delayC = {c1}"
by(auto simp add: I_def)

lemma [simp]: "spfDom\<cdot>(spfcomp addC delayC) = {c1}"
by(simp add: spfComp_dom_I)

lemma [simp]: "spfRan\<cdot>(spfcomp addC delayC) = {c2, c3}"
by(simp add: spfComp_ran_Oc)

(* prerequirements for final lemma *)

(* final lemma *)

definition sum1 :: "nat SPF" where
"sum1 \<equiv> hide (addC \<otimes>  delayC) {c2}"

lemma sum1EqCh: assumes "sbDom\<cdot>sb = I addC delayC" shows "(sum1 \<rightleftharpoons> sb) . c3 = ((addC \<otimes>  delayC) \<rightleftharpoons> sb) . c3"
apply(simp add: sum1_def)
apply(subst hideSbRestrictCh)
by(simp_all add: assms)

lemma sumEq: assumes "sbDom\<cdot>sb = I addC delayC" shows "(sum1 \<rightleftharpoons> sb) . c3 = sum4\<cdot>(sb . c1)"
apply(subst sum1EqCh, simp add: assms)
sorry

end