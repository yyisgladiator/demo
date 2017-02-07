theory Feedback_MW
imports SPF Streams SBTheorie ParComp_MW StreamCase_Study SPF_MW SerComp_JB 

begin

(* Delay component *)

definition append0:: "nat stream  \<rightarrow> nat stream" where
"append0 \<equiv> \<Lambda> s . \<up>0 \<bullet> s"

lemma spfappend0_mono[simp] : "monofun (\<lambda> sb. (sbDom\<cdot>sb = {ch3}) \<leadsto> ([ch2\<mapsto>append0\<cdot>(sb . ch3)]\<Omega>))"
  apply (rule spf_mono2monofun)
   apply (rule spf_monoI)
   apply (simp add: domIff2)
   apply (rule sb_below)
    apply (simp add: sbdom_insert)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   apply (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
   by (rule, simp add: domIff2)

lemma append0_chain[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {ch3} 
                        \<Longrightarrow> chain (\<lambda> i. [ch2\<mapsto>append0\<cdot>((Y i) . ch3)]\<Omega>)"
  apply (rule chainI)
  apply (rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (simp add: monofun_cfun po_class.chainE)

lemma append0_chain_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch3} 
                                \<Longrightarrow> chain (\<lambda> i. [ch2\<mapsto>append0\<cdot>((Y i) . ch3)]\<Omega>)"
  by (simp add: sbChain_dom_eq2)

lemma append0_Lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch3} \<Longrightarrow> 
  (\<Squnion>i. append0\<cdot>(Y i . ch3)) = append0\<cdot>((Lub Y). ch3)"
  by (simp add: lub_distribs(1) lub_eval)

lemma spfappend0_chain [simp]: "chain Y \<Longrightarrow>
      chain (\<lambda> i. (sbDom\<cdot>(Y i) = {ch3}) \<leadsto> ([ch2\<mapsto>append0\<cdot>((Y i) . ch3)]\<Omega>))"
  apply (rule chainI)
  apply (simp add: sbChain_dom_eq2)
  apply (rule impI, rule some_below, rule sb_below)
   apply (simp add: sbdom_rep_eq)
  apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)

lemma spfappend0_cont[simp]: "cont (\<lambda> sb. (sbDom\<cdot>sb = {ch3}) 
                                \<leadsto> ([ch2\<mapsto>append0\<cdot>(sb . ch3)]\<Omega>))" (is "cont ?F")
  apply (rule spf_cont2cont)
    apply (rule spf_contlubI)
    apply (simp add: domIff2 sbChain_dom_eq2)
    apply (rule sb_below)
     apply (simp add: sbdom_rep_eq )
     apply (simp only: Cfun.contlub_cfun_arg append0_chain_lub)
     apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
   apply (simp add: monofun2spf_mono)
  by(simp add: domIff2, rule+)


(* SPF Definition *)

definition addC :: "nat SPF" where
"addC \<equiv> addSPF (c1, c2, c3)" 

lift_definition append0C :: "nat SPF" is
"\<Lambda> sb. (sbDom\<cdot>sb = {c3}) \<leadsto> ([c2\<mapsto>append0\<cdot>(sb . c3)]\<Omega>)"
  by (auto simp add: spf_well_def domIff2 sbdom_rep_eq)

(* addC definition without addSPF

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

lift_definition addC :: "nat SPF" is
"\<Lambda> sb. (sbDom\<cdot>sb = {c1, c2}) \<leadsto> ([c3\<mapsto>add\<cdot>(sb . c1)\<cdot>(sb . c2)]\<Omega>)"
  by (auto simp add: spf_well_def domIff2 sbdom_rep_eq)

lemma addCEqAddSPF: "addC \<equiv> addCHelper"
apply(simp add: addC_def addSPF_def addCHelper_def)
by (simp add: Abs_CSPF_def)

*)

(* component properties *)

lemma add_rep_eqC: "Rep_CSPF addC = (\<lambda> sb. (sbDom\<cdot>sb = {c1, c2}) \<leadsto> ([c3\<mapsto>add\<cdot>(sb . c1)\<cdot>(sb . c2)]\<Omega>))"
by(auto simp add: addC_def addSPF_rep_eqC)

lemma append0_rep_eqC: "Rep_CSPF append0C = (\<lambda> sb. (sbDom\<cdot>sb = {c3}) \<leadsto> ([c2\<mapsto>append0\<cdot>(sb . c3)]\<Omega>))"
  by (simp add: append0C.rep_eq Rep_CSPF_def)

lemma [simp]: "spfDom\<cdot>addC = {c1,c2}"
by (metis add_rep_eqC sbgetch_insert sbleast_sbdom spfdom2sbdom)

lemma [simp]: "spfRan\<cdot>addC = {c3}"
  apply (simp add: spfran_least add_rep_eqC)
  by (simp add: sbdom_insert)

lemma [simp]: "spfDom\<cdot>append0C = {c3}"
  apply(simp add: spfdom_insert append0C.rep_eq Rep_CSPF_def domIff2)
  by (meson sbleast_sbdom someI_ex)

lemma [simp]: "spfRan\<cdot>append0C = {c2}"
  apply (simp add: spfran_least append0_rep_eqC)
  by (simp add: sbdom_insert)

(* composition prerequirements *)

lemma [simp]: "spfComp_well addC append0C"
  by (simp add: spfComp_well_def)

lemma [simp]: "C addC append0C = {c1,c2,c3}"
  by (auto simp add: C_def)

lemma [simp]: "L addC append0C = {c2, c3}"
  by (auto simp add: L_def)

lemma [simp]: "Oc addC append0C = {c2, c3}"
  by (auto simp add: Oc_def)

lemma [simp]: "I addC append0C = {c1}"
by(auto simp add: I_def)

lemma [simp]: "spfDom\<cdot>(spfcomp addC append0C) = {c1}"
by(simp add: spfComp_dom_I)

lemma [simp]: "spfRan\<cdot>(spfcomp addC append0C) = {c2, c3}"
by(simp add: spfComp_ran_Oc)

(* sum1 definition *)

definition sum1 :: "nat SPF" where
"sum1 \<equiv> hide (addC \<otimes>  append0C) {c2}"

lemma sum1EqCh: assumes "sbDom\<cdot>sb = I addC append0C" shows "(sum1 \<rightleftharpoons> sb) . c3 = ((addC \<otimes>  append0C) \<rightleftharpoons> sb) . c3"
apply(simp add: sum1_def)
apply(subst hideSbRestrictCh)
by(simp_all add: assms)

(* prerequirements test lemma *)

definition teststream :: "nat stream" where
"teststream \<equiv> ((\<up>1) \<bullet> (\<up>2) \<bullet> (\<up>3))"

lemma [simp]: "4 = Suc (Suc (Suc (Suc 0)))"
by simp

lemma [simp]: "5 = Suc (Suc (Suc (Suc (Suc 0))))"
by simp

lemma [simp]: "6 = Suc (Suc (Suc (Suc (Suc (Suc 0)))))"
by simp

(* test lemma *)
(*
lemma addSbLeastDom: "sbDom\<cdot>(sbLeast {c1, c2, c3}) \<inter> {c1, c2} = {c1, c2}"
by simp

lemma addSbLeast: "([c3 \<mapsto> add\<cdot>(((sbLeast {c1, c2, c3})\<bar>{c1, c2}) . c1)\<cdot>(((sbLeast {c1, c2, c3})\<bar>{c1, c2}) . c2)]\<Omega>) = ([c3 \<mapsto> \<epsilon>]\<Omega>)"
by simp*)
(*
lemma [simp]: "cont (\<Lambda> z. ([c1 \<mapsto> ((\<up>1) \<bullet> (\<up>2) \<bullet> (\<up>3))]\<Omega>) \<uplus> (addC\<rightleftharpoons>z\<bar>{c1, c2}) \<uplus> (append0C\<rightleftharpoons>z\<bar>{c3}))"
sorry*)

lemma [simp]: "cont (Rep_cfun (\<Lambda> z. ([c1 \<mapsto> teststream]\<Omega>) \<uplus> (addC\<rightleftharpoons>(z\<bar>{c1, c2})) \<uplus> (append0C\<rightleftharpoons>(z\<bar>{c3}))))"
sorry

lemma Iterate0_H2_test: "((iterate (Suc 0)\<cdot>(ParComp_MW.spfCompHelp2 addC append0C ([c1 \<mapsto> ((\<up>1) \<bullet> (\<up>2) \<bullet> (\<up>3))]\<Omega>)))
                         \<cdot>(sbLeast {c1, c2, c3})) = ([c1 \<mapsto> ((\<up>1) \<bullet> (\<up>2) \<bullet> (\<up>3))]\<Omega>) \<uplus> ([c2 \<mapsto> (\<up>0)]\<Omega>) \<uplus> ([c3 \<mapsto> \<epsilon>]\<Omega>)"
apply(simp add: spfCompHelp2_def)
apply(simp add: add_rep_eqC append0_rep_eqC)
sorry

lemma Iterate1_H2_test: "((iterate (Suc (Suc 0))\<cdot>(ParComp_MW.spfCompHelp2 addC append0C ([c1 \<mapsto> ((\<up>1) \<bullet> (\<up>2) \<bullet> (\<up>3))]\<Omega>)))
                         \<cdot>(sbLeast {c1, c2, c3})) = ([c1 \<mapsto> ((\<up>1) \<bullet> (\<up>2) \<bullet> (\<up>3))]\<Omega>) \<uplus> ([c2 \<mapsto> \<epsilon>]\<Omega>) \<uplus> ([c3 \<mapsto> \<epsilon>]\<Omega>)"
apply(subst iterate_Suc)
apply(subst Iterate0_H2_test)
apply(simp add: spfCompHelp2_def)
apply(simp add: add_rep_eqC append0_rep_eqC)
sorry

(*
lemma lub_H2_test: "(\<Squnion>i. (iterate i\<cdot>(ParComp_MW.spfCompHelp2 addC append0C ([c1 \<mapsto> ((\<up>1) \<bullet> (\<up>2) \<bullet> (\<up>3))]\<Omega>)))\<cdot>(sbLeast {c1, c2, c3}))
                  = (([c1 \<mapsto> ((\<up>1) \<bullet> (\<up>2) \<bullet> (\<up>3))]\<Omega>) \<uplus> ([c2 \<mapsto> ((\<up>0) \<bullet> (\<up>1) \<bullet> (\<up>3) \<bullet> (\<up>6))]\<Omega>) \<uplus> ([c3 \<mapsto> ((\<up>1) \<bullet> (\<up>3) \<bullet> (\<up>6))]\<Omega>)) "
sorry
*)

lemma test: "sum1\<rightleftharpoons>([c1\<mapsto><[1,2,3]>]\<Omega>).c3 = <[1,3,6]>"
apply(simp add: sum1EqCh)
apply(subst ParComp_MW.spfcomp_tospfH2)
apply(subst spfcomp_repAbs, simp_all)
sorry
(* by(simp add: lub_H2_test) *)

(* prerequirements for final lemma *)



(* final lemma *)

lemma sumEq: assumes "sbDom\<cdot>sb = I addC append0C" shows "(sum1 \<rightleftharpoons> sb) . c3 = sum4\<cdot>(sb . c1)"
apply(subst sum1EqCh, simp add: assms)
sorry

end