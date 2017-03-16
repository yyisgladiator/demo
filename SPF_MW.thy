theory SPF_MW
imports SPF SerComp_JB ParComp_MW (*InnerProd_Case_StudyTSPFTheorie*)
begin

(* operator for parallel composition *)

definition parcomp :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF" ("_\<parallel>_") where
"parcomp f1 f2 \<equiv> Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))"

(* operator for serial composition *)

definition sercomp :: "'m SPF => 'm SPF => 'm SPF"  ("_\<circ>_") where
"sercomp f1 f2 \<equiv> Abs_CSPF (\<lambda> x. (sbDom\<cdot>x =  spfDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> x) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))"

(* spfDom spfcomp *)

lemma spfDomAbs: assumes "cont (\<lambda> x. (sbDom\<cdot>x = cs ) \<leadsto> f(x))" and "spf_well (Abs_cfun (\<lambda> x. (sbDom\<cdot>x = cs ) \<leadsto> f(x)))"
    shows "spfDom\<cdot>(Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = cs ) \<leadsto> f(x))) = cs" 
apply(simp add: spfDom_def)
apply(simp_all add: assms)
by (smt domIff option.discI sbleast_sbdom someI_ex)

lemma spfComp_dom_I: assumes "spfComp_well f1 f2" shows "spfDom\<cdot>(spfcomp f1 f2) = I f1 f2"
apply(simp add: spfcomp_tospfH2, subst spfDomAbs)
by(simp_all add: assms)

(* spfRan spfcomp *)

lemma sbDomIterate: "sbDom\<cdot>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 (sbLeast (I f1 f2)))\<cdot>sb)  = sbDom\<cdot>((spfCompHelp2 f1 f2 (sbLeast (I f1 f2)))\<cdot>sb)"
apply(simp add: sbDom_def spfCompHelp2_def)
(* in SPF *)
sorry

lemma spfDomHelp: assumes "spfDom\<cdot>f1 \<subseteq> sbDom\<cdot>sb" shows "sbDom\<cdot>f1\<rightleftharpoons>sb\<bar>spfDom\<cdot>f1 = spfRan\<cdot>f1"
by (simp add: assms)

lemma sbDomH2: assumes "spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 \<subseteq> sbDom\<cdot>sb2" shows "sbDom\<cdot>((spfCompHelp2 f1 f2 sb1)\<cdot>sb2) = sbDom\<cdot>sb1 \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2"
apply(simp add: spfCompHelp2_def)
apply(subst spfDomHelp)
using assms apply auto[1]
apply(subst spfDomHelp)
using assms apply auto[1]
by simp

lemma spfComp_ran_Oc: assumes "spfComp_well f1 f2" shows "spfRan\<cdot>(spfcomp f1 f2) = Oc f1 f2"
apply(simp add: spfcomp_tospfH2)
apply(simp add:  spfran_least)
apply(subst spfDomAbs, simp_all add: assms)
apply(subst sbDomIterate)
apply(subst sbDomH2, simp)
using C_def apply blast
using Oc_def by auto

(* hide *)

definition hide :: "'m SPF \<Rightarrow>  channel set \<Rightarrow> 'm SPF" ("_\<h>_") where
"hide f cs \<equiv> Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(spfRan\<cdot>f - cs)))"

lemma hidecont_helper: assumes "cont (Rep_CSPF(f))" shows "cont (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(spfRan\<cdot>f - cs)))"
apply(subst if_then_cont, simp_all)
by (simp add: cont_compose)

lemma hidespfwell_helper: assumes "spf_well (Abs_cfun (Rep_CSPF(f)))" 
  shows "spf_well (Abs_cfun (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(spfRan\<cdot>f - cs))))"
  apply(auto simp add: spf_well_def domIff2 sbdom_rep_eq)
sorry

lemma spfDomHide: "spfDom\<cdot>(f \<h> cs) = spfDom\<cdot>f"
  apply(simp add: hide_def)
    by(simp add: spfDomAbs hidecont_helper hidespfwell_helper)

lemma hideSbRestrict: assumes "sbDom\<cdot>sb = spfDom\<cdot>f" 
   shows "(hide f cs)\<rightleftharpoons>sb = (f\<rightleftharpoons>sb)\<bar>(spfRan\<cdot>f - cs)"
  apply(simp add: hide_def)
  apply(simp add: hidecont_helper hidespfwell_helper)
    by (simp add: assms)

lemma hideSbRestrictCh: assumes "sbDom\<cdot>sb = spfDom\<cdot>f" and "c \<notin> cs"
   shows "(hide f cs)\<rightleftharpoons>sb . c = (f\<rightleftharpoons>sb) . c"
  apply(simp add: hide_def)
  apply(simp add: hidecont_helper hidespfwell_helper assms)
  by (smt DiffI Diff_subset Int_absorb1 assms(1) assms(2) domIff option.exhaust_sel sbleast_sbdom sbrestrict2sbgetch sbrestrict_sbdom sbunion_getchL sbunion_idL spfLeastIDom spf_sbdom2dom spfran2sbdom)
    
lemma hideSpfRan: "spfRan\<cdot>(hide f cs) = spfRan\<cdot>f - cs"
  apply(subst spfran_least)
  apply(simp add: spfDomHide)
  apply(subst hideSbRestrict)
  apply(simp)
  apply(subst sbrestrict_sbdom)
  by (simp add: Diff_subset Int_absorb1 spfran_least)

lemma hideSubset: "spfRan\<cdot>(hide f cs) \<subseteq> spfRan\<cdot>f"
  using hideSpfRan by auto

(* lemmas about parallel composition *)

lemma LtopL: "L f1 f2 = {} \<Longrightarrow> pL f1 f2 = {}"
apply(simp add: L_def pL_def)
by (simp add: Int_Un_distrib inf_sup_distrib2)

lemma unionRestrictCh: assumes "sbDom\<cdot>sb1 \<inter> cs = {}"
                           and "sbDom\<cdot>sb2 \<union> sbDom\<cdot>sb3 = cs"
                           and "c \<in> cs"
   shows "(sb1 \<uplus> sb2 \<uplus> sb3 \<bar> cs) . c = (sb2 \<uplus> sb3) . c"
by (metis (no_types, lifting) Un_upper2 assms(1) assms(2) inf_sup_distrib1 inf_sup_ord(3) sbrestrict_id sbunion_commutative sbunion_restrict2 sbunion_restrict3 sup_eq_bot_iff)

lemma unionRestrict: assumes "sbDom\<cdot>sb1 \<inter> cs = {}"
                         and "sbDom\<cdot>sb2 \<union> sbDom\<cdot>sb3 = cs"
   shows "sb1 \<uplus> sb2 \<uplus> sb3 \<bar> cs = sb2 \<uplus> sb3"
apply(rule sb_eq)
apply(simp_all add: assms)
apply (simp add: Int_absorb1 assms(2) sup_assoc)
by (metis Un_iff assms(2) sbunion_getchL sbunion_getchR)

lemma parCompHelp2Eq: assumes "L f1 f2 = {}"
                          and "spfComp_well f1 f2"
                          and "sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2"    
   shows "(\<Squnion>i. iterate i\<cdot>(ParComp_MW.spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2 = (f1\<rightleftharpoons>(x\<bar>spfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x\<bar>spfDom\<cdot>f2))" 
apply(subst spfComp_parallel_itconst2, simp_all add: assms)
apply(simp add: Oc_def)
apply(subst unionRestrict)
apply(simp_all add: assms)
by (metis Diff_triv L_def assms(1) inf_commute)

lemma parCompHelp2Eq2: assumes "L f1 f2 = {}"
                           and "spfComp_well f1 f2" 
   shows " (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2) \<leadsto> ((\<Squnion>i. iterate i\<cdot>(ParComp_MW.spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)
         = (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2) \<leadsto> ((f1\<rightleftharpoons>(x\<bar>spfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x\<bar>spfDom\<cdot>f2)))"
using assms(1) assms(2) parCompHelp2Eq by fastforce

lemma parallelOperatorEq: assumes "L f1 f2 = {}"
                              and "spfComp_well f1 f2"  
   shows "(f1 \<otimes> f2) = (f1 \<parallel> f2)"
apply(simp add: parcomp_def spfcomp_tospfH2)
apply(subst spfComp_I_domf1f2_eq, simp_all add: assms)
apply(subst parCompHelp2Eq2)
by(simp_all add: assms)

lemma parCompDom: assumes "L f1 f2 = {}"
                  and "spfComp_well f1 f2" shows "spfDom\<cdot>(f1 \<parallel> f2) = spfDom\<cdot>(spfcomp f1 f2)"
  by (simp add: assms(1) assms(2) parallelOperatorEq)

lemma parCompRan: assumes "L f1 f2 = {}"
                  and "spfComp_well f1 f2" shows "spfRan\<cdot>(f1 \<parallel> f2) = spfRan\<cdot>(spfcomp f1 f2)"
  by (simp add: assms(1) assms(2) parallelOperatorEq)

(* lemmas about serial composition *)

lemma pLEmptyNoSelfloops: assumes "pL f1 f2 = {}"
  shows "no_selfloops f1 f2"
  apply(simp add: no_selfloops_def)
  using assms pL_def by auto
    
lemma spfComp_I_domf1_eq: assumes "pL f1 f2 = {}"
                              and "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                              and "spfComp_well f1 f2"
   shows "I f1 f2 = spfDom\<cdot>f1"
  using SerComp_JB.spfComp_I_domf1_eq assms(1) assms(2) assms(3) pLEmptyNoSelfloops spfComp_dom_I spfdom_insert by blast

     
lemma serCompHelp2Eq: assumes "pL f1 f2 = {}"
                          and "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                          and "spfComp_well f1 f2"
                          and "sbDom\<cdot>x = spfDom\<cdot>f1" 
   shows "(\<Squnion>i. iterate i\<cdot>(SPF.spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2 = ((f1 \<rightleftharpoons> x)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))" 
  apply(subst spfComp_serial_itconst2)
       apply(simp_all add: assms)
    apply(subst spfComp_I_domf1_eq, simp_all add: assms)
    apply(simp add: pLEmptyNoSelfloops assms)
  apply(simp add: Oc_def)
   apply(subst unionRestrict, simp_all add: assms)
   using pL_def assms(1) assms(2) apply blast
   by (metis (no_types, lifting) assms(2) assms(4) domIff option.collapse sbleast_sbdom spfLeastIDom spf_sbdom2dom spfran2sbdom)

lemma serCompHelp2Eq2: assumes "pL f1 f2 = {}"
                           and "spfComp_well f1 f2"
                           and "spfRan\<cdot>f1 = spfDom\<cdot>f2"
   shows " (sbDom\<cdot>x = spfDom\<cdot>f1) \<leadsto> ((\<Squnion>i. iterate i\<cdot>(SPF.spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)
         = (sbDom\<cdot>x = spfDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> x) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
  by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) lub_eq serCompHelp2Eq)

lemma serialOperatorEq: assumes "pL f1 f2 = {}"
                            and "spfComp_well f1 f2"
                            and "spfRan\<cdot>f1 = spfDom\<cdot>f2"
   shows "(f1 \<otimes> f2) = (f1 \<circ> f2)"
apply(simp add: sercomp_def SerComp_JB.spfcomp_tospfH2)
apply(subst spfComp_I_domf1_eq, simp_all add: assms)
apply(subst serCompHelp2Eq2)
by(simp_all add: assms)

(* general lemmas for cont and spf_well *)

lemma conthelper: assumes "cont (Rep_CSPF f)" and "spfDom\<cdot>f = cs" shows "cont (\<lambda> z. (f\<rightleftharpoons>(z\<bar>cs)))"
by (metis Rep_CSPF_def cont_Rep_cfun2 cont_compose op_the_cont)

lemma conthelper2: assumes "cs = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2"
                       and "cont (Rep_CSPF f1)" 
                       and "cont (Rep_CSPF f2)"
  shows "cont (\<lambda> x. (sbDom\<cdot>x = cs)\<leadsto>((f1\<rightleftharpoons>(x\<bar>spfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x\<bar>spfDom\<cdot>f2))))"
apply(subst if_then_cont, simp_all)
apply(subst cont2cont_APP)
apply (metis Rep_CSPF_def cont_Rep_cfun2 cont_compose conthelper)
using conthelper apply auto[1]
by auto

lemma spfwellhelper: assumes "cs = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2" 
                         and "cont (Rep_CSPF f1)" 
                         and "cont (Rep_CSPF f2)"
  shows "spf_well (\<Lambda> x. (sbDom\<cdot>x = cs)\<leadsto>((f1\<rightleftharpoons>(x\<bar>spfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x\<bar>spfDom\<cdot>f2))))"
apply(simp add: spf_well_def domIff2 sbdom_rep_eq)
apply(subst Abs_cfun_inverse2)
apply(subst conthelper2, simp_all add: assms)
apply(subst Abs_cfun_inverse2)
apply(subst conthelper2, simp_all add: assms)
apply(subst Abs_cfun_inverse2)
   apply(subst conthelper2, simp_all add: assms)
sorry
(* apply (rule spf_mono2monofun)
   apply (rule spf_monoI)
   apply (simp add: domIff2)
   apply (rule sb_below)*)
(* append Element *)

definition appendElem:: "nat \<Rightarrow> nat stream \<Rightarrow> nat stream" where
"appendElem a s = \<up>a \<bullet> s"

lemma [simp]: "cont (appendElem a)"
  sorry

definition appendElem2:: "'a \<Rightarrow> 'a stream \<rightarrow> 'a stream" where
"appendElem2 a \<equiv> \<Lambda> s. \<up>a \<bullet> s" 
 
definition appendSPF :: "(channel \<times> channel) \<Rightarrow> nat \<Rightarrow> nat SPF" where
"appendSPF cs a \<equiv> Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs)}) \<leadsto> ([(snd cs)\<mapsto>(appendElem a (sb.(fst cs)))]\<Omega>))"

lemma appendSPF_mono: "monofun (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs)}) \<leadsto> ([(snd cs)\<mapsto>(appendElem a (sb.(fst cs)))]\<Omega>))"
  apply(simp only: appendElem_def)
  apply (rule spf_mono2monofun)
   apply (rule spf_monoI)
   apply (simp add: domIff2)
   apply (rule sb_below)
    apply (simp add: sbdom_insert)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   apply (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
   by (rule, simp add: domIff2)

lemma append_chain: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {(fst cs), (snd cs)} 
                        \<Longrightarrow> chain (\<lambda> i. [(snd cs)\<mapsto>(appendElem a ((Y i).(fst cs)))]\<Omega>)"
  apply(simp only: appendElem_def)
  apply (rule chainI)
  apply (rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (simp add: monofun_cfun po_class.chainE)

lemma appendSPF_chain_lub: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {(fst cs), (snd cs)} 
                        \<Longrightarrow> chain (\<lambda> i. [(snd cs)\<mapsto>(appendElem a ((Y i).(fst cs)))]\<Omega>)"
  sorry     
 

lemma appendSPF_Lub: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {(fst cs), (snd cs)} 
                        \<Longrightarrow> (\<Squnion>i.(appendElem a ((Y i).(fst cs)))) = appendElem a ((Lub Y).(fst cs))"
  apply(simp only: appendElem_def)    
  by (simp add: lub_distribs(1) lub_eval)

(*    
lemma appendSPF_chain: "chain Y \<Longrightarrow>
                        chain (\<lambda> i. (sbDom\<cdot>(Y i) = {(fst cs),(snd cs)}) \<leadsto> ([(snd cs)\<mapsto>(appendElem a ((Y i).(fst cs)))]\<Omega>))"
sorry
*)

lemma appendSPF_cont: "cont (\<lambda> sb. (sbDom\<cdot>sb = {(fst cs)}) \<leadsto> ([(snd cs)\<mapsto>(appendElem a (sb.(fst cs)))]\<Omega>))"
  apply (rule spf_cont2cont)
    apply (rule spf_contlubI)
    apply (simp add: domIff2 sbChain_dom_eq2)
    apply (rule sb_below)
     apply (simp add: sbdom_rep_eq )
     apply (simp only: Cfun.contlub_cfun_arg appendSPF_chain_lub)
sorry

(* spfLift *)  
  
definition spfLift_1x1 :: "('m stream \<rightarrow> 'm stream) \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> 'm SPF" where
  "spfLift_1x1 f ch1 ch2  \<equiv> Abs_CSPF (\<lambda>b. ( (b\<in>{ch1}^\<Omega>) \<leadsto> ([ch2 \<mapsto> f\<cdot>(b . ch1)]\<Omega>)))"  
  
definition spfLift_1x2 :: "('m stream \<rightarrow> 'm stream) \<Rightarrow> ('m stream \<rightarrow> 'm stream) \<Rightarrow> channel \<Rightarrow> (channel \<times> channel) \<Rightarrow> 'm SPF" where
  "spfLift_1x2 f1 f2 ch1 cs \<equiv> 
   Abs_CSPF (\<lambda>b. ( (b\<in>{ch1}^\<Omega>) \<leadsto> ([(fst cs) \<mapsto> f1\<cdot>(b . ch1), (snd cs) \<mapsto> f2\<cdot>(b . ch1)]\<Omega>)))"  
 
definition spfLift_1x3 :: "('m stream \<rightarrow> 'm stream) \<Rightarrow> ('m stream \<rightarrow> 'm stream) \<Rightarrow> ('m stream \<rightarrow> 'm stream) \<Rightarrow> channel \<Rightarrow> (channel \<times> channel \<times> channel) \<Rightarrow> 'm SPF" where
  "spfLift_1x3 f1 f2 f3 ch1 cs \<equiv> 
   Abs_CSPF (\<lambda>b. ( (b\<in>{ch1}^\<Omega>) \<leadsto> ([(fst cs) \<mapsto> f1\<cdot>(b . ch1), (fst (snd cs)) \<mapsto> f2\<cdot>(b . ch1), (snd (snd cs)) \<mapsto> f3\<cdot>(b . ch1)]\<Omega> )))"  
   
definition spfLift_2x1 :: "('m stream \<rightarrow> 'm stream \<rightarrow> 'm stream) \<Rightarrow> (channel \<times> channel) \<Rightarrow> channel \<Rightarrow> 'm SPF" where
  "spfLift_2x1 f cs ch1  \<equiv> Abs_CSPF (\<lambda>b. ( (b\<in>{fst cs, snd cs}^\<Omega>) \<leadsto> ([ch1 \<mapsto> f\<cdot>(b . (fst cs))\<cdot>(b . (snd cs))]\<Omega>)))"  
  
  
end