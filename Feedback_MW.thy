theory Feedback_MW
imports SPF Streams SBTheorie ParComp_MW StreamCase_Study SPF_MW SerComp_JB SPF_Templates

begin

(* append component *)
section Append

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
section SPFs

definition addC :: "nat SPF" where
"addC \<equiv> addSPF (c1, c2, c3)" 
  
lift_definition append0C :: "nat SPF" is
"\<Lambda> sb. (sbDom\<cdot>sb = {c3}) \<leadsto> ([c2\<mapsto>append0\<cdot>(sb . c3)]\<Omega>)"
  apply(simp add: spf_well_def)
  apply(simp add:  domIff2)
  by (auto simp add: sbdom_rep_eq)

(* component properties *)
subsection Properties

lemma add_rep_eqC: "Rep_CSPF addC = (\<lambda> sb. (sbDom\<cdot>sb = {c1, c2}) \<leadsto> ([c3\<mapsto>add\<cdot>(sb . c1)\<cdot>(sb . c2)]\<Omega>))"
by(auto simp add: addC_def addSPF_rep_eqC)

lemma append0_rep_eqC: "Rep_CSPF append0C = (\<lambda> sb. (sbDom\<cdot>sb = {c3}) \<leadsto> ([c2\<mapsto>append0\<cdot>(sb . c3)]\<Omega>))"
  by (simp add: append0C.rep_eq Rep_CSPF_def)

lemma [simp]: "spfDom\<cdot>addC = {c1,c2}"
  by (metis add_rep_eqC sbleast_sbdom spfdom2sbdom)

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
subsection Composition_prerequirements

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
section sum1

definition sum1SPF :: "nat SPF" where
"sum1SPF \<equiv> hide (addC \<otimes>  append0C) {c2}"

lemma sum1EqCh: assumes "sbDom\<cdot>sb = I addC append0C" shows "(sum1SPF \<rightleftharpoons> sb) . c3 = ((addC \<otimes> append0C) \<rightleftharpoons> sb) . c3"
apply(simp add: sum1SPF_def)
apply(subst hideSbRestrictCh)
by(simp_all add: assms)

(* prerequirements test lemma *)
section Test
subsection Prerequirements

lemma [simp]: "4 = Suc (Suc (Suc (Suc 0)))"
  by simp

lemma [simp]: "5 = Suc (Suc (Suc (Suc (Suc 0))))"
  by simp

lemma [simp]: "6 = Suc (Suc (Suc (Suc (Suc (Suc 0)))))"
  by simp

lemma numeral_7_eq_7[simp]: "7 = Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))"
  by simp

(* test lemma *)
subsection Lemma

lemma sbunion_commutative2: assumes "sbDom\<cdot>b1 \<inter> sbDom\<cdot>b2 = {}"
                                and "sbDom\<cdot>b1 \<inter> sbDom\<cdot>b3 = {}"
                                and "sbDom\<cdot>b2 \<inter> sbDom\<cdot>b3 = {}"
  shows "b1\<uplus>b2\<uplus>b3 = b1\<uplus>b3\<uplus>b2"
by (metis assms(3) sbunion_associative sbunion_commutative)

lemma unionRestrict2: assumes "sbDom\<cdot>sb3 \<inter> cs = {}"
                         and "sbDom\<cdot>sb1 \<union> sbDom\<cdot>sb2 = cs"
   shows "sb1 \<uplus> sb2 \<uplus> sb3 \<bar> cs = sb1 \<uplus> sb2"
apply(rule sb_eq)
by(simp_all add: assms)

lemma contAddC: "cont (\<lambda> z. (addC\<rightleftharpoons>(z\<bar>{c1, c2})))"
by(subst conthelper, simp_all)

lemma contAppend0: "cont (\<lambda> z. (append0C\<rightleftharpoons>(z\<bar>{c3})))"
by(subst conthelper, simp_all)

lemma contAddCAppend0CUnion: "cont (\<lambda> z. sb2 \<uplus> (addC\<rightleftharpoons>(z\<bar>{c1, c2})) \<uplus> (append0C\<rightleftharpoons>(z\<bar>{c3})))"
apply(subst cont2cont_APP)
by(simp_all add: contAddC contAppend0)

lemma Iterate1_H2_test: "((iterate (Suc 0)\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))
                         \<cdot>(sbLeast {c1, c2, c3})) = ([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0]>]\<Omega>) \<uplus> ([c3 \<mapsto> \<epsilon>]\<Omega>)"
apply(simp add: SPF.spfCompHelp2_def contAddCAppend0CUnion)
apply(simp add: add_rep_eqC append0_rep_eqC append0_def)
apply(subst sbunion_commutative2)
by(auto simp add: sbdom_rep_eq)

lemma Iterate2_H2_test: "((iterate (Suc (Suc 0))\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))
                         \<cdot>(sbLeast {c1, c2, c3})) = ([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1]>]\<Omega>)"
apply(subst iterate_Suc)
apply(subst Iterate1_H2_test)
apply(simp add: SPF.spfCompHelp2_def contAddCAppend0CUnion)
apply(subst unionRestrict2, auto simp add: sbdom_rep_eq)
apply(simp add: add_rep_eqC append0_rep_eqC append0_def)
apply(auto simp add: sbdom_rep_eq)
apply(simp add: add_def)
apply(subst sbunion_commutative2)
by(auto simp add: sbdom_rep_eq)

lemma Iterate3_H2_test: "((iterate (Suc (Suc (Suc 0)))\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))
                         \<cdot>(sbLeast {c1, c2, c3})) = ([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0,1]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1]>]\<Omega>)"
apply(subst iterate_Suc)
apply(subst Iterate2_H2_test)
apply(simp add: SPF.spfCompHelp2_def contAddCAppend0CUnion)
apply(subst unionRestrict2, auto simp add: sbdom_rep_eq)
apply(simp add: add_rep_eqC append0_rep_eqC append0_def)
apply(auto simp add: sbdom_rep_eq)
apply(simp add: add_def)
apply(subst sbunion_commutative2)
by(auto simp add: sbdom_rep_eq)

lemma Iterate4_H2_test: "((iterate (Suc (Suc (Suc (Suc 0))))\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))
                         \<cdot>(sbLeast {c1, c2, c3})) = ([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0,1]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1,3]>]\<Omega>)"
apply(subst iterate_Suc)
apply(subst Iterate3_H2_test)
apply(simp add: SPF.spfCompHelp2_def contAddCAppend0CUnion)
apply(subst unionRestrict2, auto simp add: sbdom_rep_eq)
apply(simp add: add_rep_eqC append0_rep_eqC append0_def)
apply(auto simp add: sbdom_rep_eq)
apply(simp add: add_def)
apply(subst sbunion_commutative2)
by(auto simp add: sbdom_rep_eq)

lemma Iterate5_H2_test: "((iterate (Suc (Suc (Suc (Suc (Suc 0)))))\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))
                         \<cdot>(sbLeast {c1, c2, c3})) = ([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0,1,3]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1,3]>]\<Omega>)"
apply(subst iterate_Suc)
apply(subst Iterate4_H2_test)
apply(simp add: SPF.spfCompHelp2_def contAddCAppend0CUnion)
apply(subst unionRestrict2, auto simp add: sbdom_rep_eq)
apply(simp add: add_rep_eqC append0_rep_eqC append0_def)
apply(auto simp add: sbdom_rep_eq)
apply(simp add: add_def)
apply(subst sbunion_commutative2)
by(auto simp add: sbdom_rep_eq)

lemma Iterate6_H2_test: "((iterate (Suc (Suc (Suc (Suc (Suc (Suc 0))))))\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))
                         \<cdot>(sbLeast {c1, c2, c3})) = ([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0,1,3]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1,3,6]>]\<Omega>)"
apply(subst iterate_Suc)
apply(subst Iterate5_H2_test)
apply(simp add: SPF.spfCompHelp2_def contAddCAppend0CUnion)
apply(subst unionRestrict2, auto simp add: sbdom_rep_eq)
apply(simp add: add_rep_eqC append0_rep_eqC append0_def)
apply(auto simp add: sbdom_rep_eq)
apply(simp add: add_def)
apply(subst sbunion_commutative2)
by(auto simp add: sbdom_rep_eq)

lemma Iterate7_H2_test: "((iterate (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))
                         \<cdot>(sbLeast {c1, c2, c3})) = ([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0,1,3,6]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1,3,6]>]\<Omega>)"
apply(subst iterate_Suc)
apply(subst Iterate6_H2_test)
apply(simp add: SPF.spfCompHelp2_def contAddCAppend0CUnion)
apply(subst unionRestrict2, auto simp add: sbdom_rep_eq)
apply(simp add: add_rep_eqC append0_rep_eqC append0_def)
apply(auto simp add: sbdom_rep_eq)
apply(simp add: add_def)
apply(subst sbunion_commutative2)
by(auto simp add: sbdom_rep_eq)

lemma Iterate_H2_test_max: "(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>))\<cdot>(([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0,1,3,6]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1,3,6]>]\<Omega>))
                      = ([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0,1,3,6]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1,3,6]>]\<Omega>)"
apply(simp add: SPF.spfCompHelp2_def contAddCAppend0CUnion)
apply(subst unionRestrict2, auto simp add: sbdom_rep_eq)
apply(simp add: add_rep_eqC append0_rep_eqC append0_def)
apply(auto simp add: sbdom_rep_eq)
apply(simp add: add_def)
apply(subst sbunion_commutative2)
by(auto simp add: sbdom_rep_eq)

lemma Iterate_H2_max:
  "((iterate (Suc (Suc (Suc (Suc (Suc (Suc (Suc i)))))))\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))\<cdot>(sbLeast {c1, c2, c3})) 
           = ((iterate 7\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))\<cdot>(sbLeast {c1, c2, c3}))"
  apply(subst numeral_7_eq_7,subst Iterate7_H2_test)
  apply(induction i)
  using Iterate7_H2_test apply blast
  by (metis (no_types, lifting) Iterate_H2_test_max iterate_Suc)

    
lemma addAppend_H2_chain:  "chain (\<lambda>i. iterate i\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>))\<cdot>(sbLeast {c1, c2, c3}))"
apply(rule sbIterate_chain)
by (auto)

lemma Iterate_max_H2_test: "max_in_chain 7 (\<lambda>i. iterate i\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>))
                         \<cdot>(sbLeast {c1, c2, c3}))"
apply(rule max_in_chainI, subst numeral_7_eq_7)
  apply(subst Iterate7_H2_test)
  sorry
(*
    apply(subst Iterate_H2_max, simp)
  apply(subst numeral_7_eq_7, subst Iterate7_H2_test)
    by auto
*)

lemma lub_H2_test1: "(\<Squnion>i. (iterate i\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))\<cdot>(sbLeast {c1, c2, c3}))
                  = ((iterate (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))\<cdot>(sbLeast {c1, c2, c3})) "
using Iterate_max_H2_test addAppend_H2_chain maxinch_is_thelub by fastforce

lemma lub_H2_test2: "(\<Squnion>i. (iterate i\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))\<cdot>(sbLeast {c1, c2, c3}))
                  = (([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0,1,3,6]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1,3,6]>]\<Omega>)) "
using Iterate7_H2_test lub_H2_test1 by auto

lemma lub_H2_test_getCh: "(\<Squnion>i. iterate i\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>))\<cdot>(sbLeast {c1, c2, c3})) . c3
                  = <[1,3,6]>"
apply(subst lub_H2_test2)
apply(subst sbunion_getchR)
by(auto simp add: sbdom_rep_eq)

(* needs cont and spf_well of spfcomp *)
lemma spfcomp_RepAbs: assumes "spfComp_well f1 f2" shows
 "Rep_CSPF (Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(SPF.spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2))
            = (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(SPF.spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)"
sorry

lemma sfa: "\<up>(Suc 0) \<bullet> \<up>2 \<bullet> \<up>(Suc (Suc (Suc 0))) = <[1,2,3]>"
by auto

lemma test: "sum1SPF \<rightleftharpoons>([c1\<mapsto><[1,2,3]>]\<Omega>).c3 = <[1,3,6]>"
apply(simp add: sum1EqCh)
apply(subst SPF.spfcomp_tospfH2)
apply(subst spfcomp_RepAbs, simp_all)
apply(subst sfa, subst lub_H2_test_getCh)
by auto

(* Broy Operator *)
section Broy
  
subsection Stueber_Version
  
primrec spfFeedbackHelper :: "nat \<Rightarrow> 'a SPF \<Rightarrow> 'a SB \<Rightarrow> 'a SB" where
  "spfFeedbackHelper 0 f sb = sbLeast (spfDom\<cdot>f \<union> spfRan\<cdot>f)" |
  "spfFeedbackHelper (Suc i) f sb = 
    (let last = spfFeedbackHelper i f sb in
    (sb \<uplus> (f \<rightleftharpoons> (last \<bar> spfDom\<cdot>f))))"
  
definition spfFeedbackOperatorStueber :: "'a SPF \<Rightarrow> 'a SPF"  where (* ("\<mu>_" 50) *)
  "spfFeedbackOperatorStueber f \<equiv> Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = spfDom\<cdot>f - spfRan\<cdot>f) \<leadsto> 
    ((\<Squnion>i. spfFeedbackHelper i f sb  ) \<bar> (spfRan\<cdot>f)))"

subsection Broy_Version

definition spfFeedbackOperator :: "'a SPF \<Rightarrow> 'a SPF" ("\<mu>_" 50) where
  "spfFeedbackOperator f \<equiv> Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = spfDom\<cdot>f - spfRan\<cdot>f) \<leadsto>
    (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. (f\<rightleftharpoons>((sb \<uplus> z)\<bar>(spfDom\<cdot>f))))\<cdot>(sbLeast (spfRan\<cdot>f))))" 

  (* \<Lambda> x. fix\<cdot>(\<Lambda> (z,y). f(x,y)) *)
  
  (* v1: (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. sb \<uplus> (f\<rightleftharpoons>z))\<cdot>(sbLeast (spfDom\<cdot>f))) *)
  (* v2: (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. (f\<rightleftharpoons>z))\<cdot>(sb \<uplus> sbLeast (spfDom\<cdot>f \<inter> spfRan\<cdot>f)))  Problem: sbDom((f\<rightleftharpoons>z)) = {c3}*)
  (* v3: (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. (f\<rightleftharpoons>(sb \<uplus> z)))\<cdot>(sbLeast (spfDom\<cdot>f \<inter> spfRan\<cdot>f))) *)
  (* v4: (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. (f\<rightleftharpoons>((sb \<uplus> z)\<bar>(spfDom\<cdot>f))))\<cdot>(sbLeast (spfRan\<cdot>f)))) *)
  
(* sum4 SPF *) 
subsection sum4
(*
definition idC :: "nat SPF" where
"idC \<equiv> idSPF (c5, c1)"

lemma [simp]: "spfDom\<cdot>idC = {c5}"
by (simp add: idC_def)  

lemma [simp]: "spfRan\<cdot>idC = {c1}"
by (simp add: idC_def)

definition sum4SPF :: "nat SPF" where
"sum4SPF \<equiv> \<mu>((idC \<parallel> append0C) \<circ> addC)"

subsubsection Properties

lemma [simp]: "I idC append0C = {c3, c5}"
by (simp add: I_def)

lemma [simp]: "Oc idC append0C = {c1, c2}"
by (auto simp add: Oc_def)

lemma [simp]: "L idC append0C = {}"
by (auto simp add: L_def)

lemma [simp]: "spfComp_well idC append0C"
by (simp add: spfComp_well_def)

lemma domIdAppend: "spfDom\<cdot>(idC \<parallel> append0C) = {c3, c5}"
apply(subst parCompDom, simp_all)
apply(subst spfComp_dom_I)
by simp_all

lemma ranIdAppend: "spfRan\<cdot>(idC \<parallel> append0C) = {c1, c2}"
apply(subst parCompRan, simp_all)
apply(subst spfComp_ran_Oc)
by simp_all

lemma domIdAppendAdd: "spfDom\<cdot>((idC \<parallel> append0C) \<circ> addC) = {c3, c5}"
sorry

lemma ranIdAppendAdd: "spfRan\<cdot>((idC \<parallel> append0C) \<circ> addC) = {c3}"
sorry

lemma contFeedback: "cont (\<lambda>x. (sbDom\<cdot>x = {c5})\<leadsto>(\<Squnion>i. spfFeedbackHelper i ((idC\<parallel>append0C)\<circ>addC) x)\<bar>(spfRan\<cdot>((idC\<parallel>append0C)\<circ>addC)))"
sorry

lemma spfwellFeedback: "spf_well (\<Lambda> x. (sbDom\<cdot>x = {c5})\<leadsto>(\<Squnion>i. spfFeedbackHelper i ((idC\<parallel>append0C)\<circ>addC) x)\<bar>(spfRan\<cdot>((idC\<parallel>append0C)\<circ>addC)))"
sorry

lemma domFeedback: "spfDom\<cdot>(sum4SPF) = {c5}"
apply(simp add: sum4SPF_def spfFeedbackOperator_def)
apply(subst spfDomAbs)
apply(simp_all add: domIdAppendAdd ranIdAppendAdd)
by(simp_all add: contFeedback spfwellFeedback)

lemma ranFeedback: "spfRan\<cdot>(sum4SPF) = {c3}"
apply(simp add: sum4SPF_def spfFeedbackOperator_def)
sorry

lemma sum4Eq: assumes "sbDom\<cdot>sb = {c5}" shows "(sum4SPF \<rightleftharpoons> sb) . c3 = sum4\<cdot>(sb . c5)"
apply(simp add: sum4SPF_def sum4_def)
apply(simp add: spfFeedbackOperator_def domIdAppendAdd ranIdAppendAdd)
apply(simp add: contFeedback spfwellFeedback)
sorry
*)
section Final_Lemma
(* prerequirements for final lemma *)
subsection Prerequirements


(* final lemma *)

lemma spfCompFixEq: assumes "sbDom\<cdot>sb = I addC append0C"
  shows "(\<Squnion>i. iterate i\<cdot>(SPF.spfCompHelp2 addC append0C sb)\<cdot>(sbLeast {c1, c2, c3})) . c3 = (\<mu> z. add\<cdot>(sb . c1)\<cdot>(\<up>0 \<bullet> z))" 
  sorry
    
lemma sumEq: assumes "sbDom\<cdot>sb = I addC append0C" shows "(sum1SPF \<rightleftharpoons> sb) . c3 = sum4\<cdot>(sb . c1)"
  apply(subst sum1EqCh, simp add: assms)
  apply(simp only: SPF.spfcomp_tospfH2 sum4_def)
  apply(subst  spfcomp_RepAbs)
   apply(simp_all add: assms)
  apply(subst spfCompFixEq)
    by(auto simp add: assms)

end