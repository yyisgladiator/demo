theory SPF_Feedback_MW
imports "../CaseStudies/StreamCase_Study" "../SPF_Comp" "../SPF_Templates"  SPF_FeedComp_JB "../SPF_Feedback_JB"

begin


section \<open>SPF definitions\<close>
(* definition of addC and append0C *)

  
definition addC :: "nat SPF" where
"addC \<equiv> SPF2x1 add (c1, c2, c3)" 
  
definition append0C :: "nat SPF" where
"append0C \<equiv> SPF1x1 (appendElem2 0) (c3,c2)"

(* component properties *)
subsection \<open>SPF properties\<close>

lemma add_rep_eqC: "Rep_CSPF addC = (\<lambda> sb. (sbDom\<cdot>sb = {c1, c2}) \<leadsto> ([c3\<mapsto>add\<cdot>(sb . c1)\<cdot>(sb . c2)]\<Omega>))"
by(auto simp add: addC_def SPF2x1_rep_eq)

lemma append0_rep_eqC: "Rep_CSPF append0C = (\<lambda> sb. (sbDom\<cdot>sb = {c3}) \<leadsto> ([c2\<mapsto>((appendElem2 0)\<cdot>(sb . c3))]\<Omega>))"
  apply(simp add: append0C_def)
  by(auto simp add: SPF1x1_rep_eq)

lemma [simp]: "spfDom\<cdot>addC = {c1,c2}"
  by (metis add_rep_eqC sbleast_sbdom spfdom2sbdom)

lemma [simp]: "spfRan\<cdot>addC = {c3}"
  apply (simp add: spfran_least add_rep_eqC)
  by (simp add: sbdom_insert)

lemma [simp]: "spfDom\<cdot>append0C = {c3}"
  by(auto simp add: append0C_def SPF1x1_dom)

lemma [simp]: "spfRan\<cdot>append0C = {c2}"
  by(auto simp add: append0C_def SPF1x1_ran)

    
subsection \<open>composition prerequirements\<close>

  
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

    
section \<open>sum1SPF definition\<close>
  
  
definition sum1SPF :: "nat SPF" where
"sum1SPF \<equiv> hide (addC \<otimes>  append0C) {c2}"

lemma sum1EqCh: assumes "sbDom\<cdot>sb = I addC append0C" shows "(sum1SPF \<rightleftharpoons> sb) . c3 = ((addC \<otimes> append0C) \<rightleftharpoons> sb) . c3"
apply(simp add: sum1SPF_def)
apply(subst hideSbRestrictCh)
by(simp_all add: assms)

  
section Test
subsection \<open>prerequirements test lemma\<close>

  
lemma [simp]: "4 = Suc (Suc (Suc (Suc 0)))"
  by simp

lemma [simp]: "5 = Suc (Suc (Suc (Suc (Suc 0))))"
  by simp

lemma [simp]: "6 = Suc (Suc (Suc (Suc (Suc (Suc 0)))))"
  by simp

lemma numeral_7_eq_7[simp]: "7 = Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))"
  by simp


subsection \<open>test lemma\<close>

  
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

lemma conthelper: assumes "cont (Rep_CSPF f)" and "spfDom\<cdot>f = cs" shows "cont (\<lambda> z. (f\<rightleftharpoons>(z\<bar>cs)))"
by (metis Rep_CSPF_def cont_Rep_cfun2 cont_compose op_the_cont)  
  
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
apply(simp add: add_rep_eqC append0_rep_eqC appendElem2_def)
apply(subst sbunion_commutative2)
by(auto simp add: sbdom_rep_eq)

lemma Iterate2_H2_test: "((iterate (Suc (Suc 0))\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))
                         \<cdot>(sbLeast {c1, c2, c3})) = ([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1]>]\<Omega>)"
apply(subst iterate_Suc)
apply(subst Iterate1_H2_test)
apply(simp add: SPF.spfCompHelp2_def contAddCAppend0CUnion)
apply(subst unionRestrict2, auto simp add: sbdom_rep_eq)
apply(simp add: add_rep_eqC append0_rep_eqC appendElem2_def)
apply(simp add: sbdom_rep_eq)
apply(simp add: add_def)
apply(subst sbunion_commutative2)
by(auto simp add: sbdom_rep_eq)

lemma Iterate3_H2_test: "((iterate (Suc (Suc (Suc 0)))\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))
                         \<cdot>(sbLeast {c1, c2, c3})) = ([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0,1]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1]>]\<Omega>)"
apply(subst iterate_Suc)
apply(subst Iterate2_H2_test)
apply(simp add: SPF.spfCompHelp2_def contAddCAppend0CUnion)
apply(subst unionRestrict2, auto simp add: sbdom_rep_eq)
apply(simp add: add_rep_eqC append0_rep_eqC appendElem2_def)
apply(simp add: sbdom_rep_eq)
apply(simp add: add_def)
apply(subst sbunion_commutative2)
by(auto simp add: sbdom_rep_eq)

lemma Iterate4_H2_test: "((iterate (Suc (Suc (Suc (Suc 0))))\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))
                         \<cdot>(sbLeast {c1, c2, c3})) = ([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0,1]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1,3]>]\<Omega>)"
apply(subst iterate_Suc)
apply(subst Iterate3_H2_test)
apply(simp add: SPF.spfCompHelp2_def contAddCAppend0CUnion)
apply(subst unionRestrict2, auto simp add: sbdom_rep_eq)
apply(simp add: add_rep_eqC append0_rep_eqC appendElem2_def)
apply(simp add: sbdom_rep_eq)
apply(simp add: add_def)
apply(subst sbunion_commutative2)
by(auto simp add: sbdom_rep_eq)

lemma Iterate5_H2_test: "((iterate (Suc (Suc (Suc (Suc (Suc 0)))))\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))
                         \<cdot>(sbLeast {c1, c2, c3})) = ([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0,1,3]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1,3]>]\<Omega>)"
apply(subst iterate_Suc)
apply(subst Iterate4_H2_test)
apply(simp add: SPF.spfCompHelp2_def contAddCAppend0CUnion)
apply(subst unionRestrict2, auto simp add: sbdom_rep_eq)
apply(simp add: add_rep_eqC append0_rep_eqC appendElem2_def)
apply(simp add: sbdom_rep_eq)
apply(simp add: add_def)
apply(subst sbunion_commutative2)
by(auto simp add: sbdom_rep_eq)

lemma Iterate6_H2_test: "((iterate (Suc (Suc (Suc (Suc (Suc (Suc 0))))))\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))
                         \<cdot>(sbLeast {c1, c2, c3})) = ([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0,1,3]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1,3,6]>]\<Omega>)"
apply(subst iterate_Suc)
apply(subst Iterate5_H2_test)
apply(simp add: SPF.spfCompHelp2_def contAddCAppend0CUnion)
apply(subst unionRestrict2, auto simp add: sbdom_rep_eq)
apply(simp add: add_rep_eqC append0_rep_eqC appendElem2_def)
apply(simp add: sbdom_rep_eq)
apply(simp add: add_def)
apply(subst sbunion_commutative2)
by(auto simp add: sbdom_rep_eq)

lemma Iterate7_H2_test: "((iterate (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))
                         \<cdot>(sbLeast {c1, c2, c3})) = ([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0,1,3,6]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1,3,6]>]\<Omega>)"
apply(subst iterate_Suc)
apply(subst Iterate6_H2_test)
apply(simp add: SPF.spfCompHelp2_def contAddCAppend0CUnion)
apply(subst unionRestrict2, auto simp add: sbdom_rep_eq)
apply(simp add: add_rep_eqC append0_rep_eqC appendElem2_def)
apply(simp add: sbdom_rep_eq)
apply(simp add: add_def)
apply(subst sbunion_commutative2)
by(auto simp add: sbdom_rep_eq)

lemma Iterate_H2_test_max: "(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>))\<cdot>(([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0,1,3,6]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1,3,6]>]\<Omega>))
                      = ([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0,1,3,6]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1,3,6]>]\<Omega>)"
apply(simp add: SPF.spfCompHelp2_def contAddCAppend0CUnion)
apply(subst unionRestrict2, auto simp add: sbdom_rep_eq)
apply(simp add: add_rep_eqC append0_rep_eqC appendElem2_def)
apply(simp add: sbdom_rep_eq)
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

lemma Iterate_H2_max2:
  "((iterate (Suc (Suc (Suc (Suc (Suc (Suc (Suc i)))))))\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>)))\<cdot>(sbLeast {c1, c2, c3})) 
           = ([c1 \<mapsto> <[1,2,3]>]\<Omega>) \<uplus> ([c2 \<mapsto> <[0,1,3,6]>]\<Omega>) \<uplus> ([c3 \<mapsto> <[1,3,6]>]\<Omega>)"
  apply(subst Iterate_H2_max)
  apply(subst numeral_7_eq_7)
  apply(subst Iterate7_H2_test)
    by auto
    
lemma addAppend_H2_chain:  "chain (\<lambda>i. iterate i\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>))\<cdot>(sbLeast {c1, c2, c3}))"
proof - 
  have f1: "C addC append0C = {c1, c2, c3}"
    apply(simp add: C_def)
    by auto
  then have f2: "(\<lambda>i. iterate i\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>))\<cdot>(sbLeast {c1, c2, c3}))
                = (\<lambda>i. iterate i\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>))\<cdot>(sbLeast (C addC append0C)))"
    by(simp)
  show ?thesis
    apply(subst f2)
    apply(rule spfComp_serialnf_chain, simp_all)
    by(simp add: sbdom_rep_eq)
qed
    
lemma Iterate_max_H2_test: "max_in_chain 7 (\<lambda>i. iterate i\<cdot>(SPF.spfCompHelp2 addC append0C ([c1 \<mapsto> <[1,2,3]>]\<Omega>))
                         \<cdot>(sbLeast {c1, c2, c3}))"
  apply(rule max_in_chainI)
  apply(subst numeral_7_eq_7)
  apply(subst Iterate_H2_max2)
  by (smt Iterate_H2_max2 Suc_le_D Suc_le_mono numeral_7_eq_7)

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

lemma spfcomp_RepAbs: assumes "spfComp_well f1 f2" shows
 "Rep_CSPF (Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(SPF.spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2))
            = (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(SPF.spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)"
  by simp

lemma sfa: "\<up>(Suc 0) \<bullet> \<up>2 \<bullet> \<up>(Suc (Suc (Suc 0))) = <[1,2,3]>"
by auto

lemma test: "sum1SPF \<rightleftharpoons>([c1\<mapsto><[1,2,3]>]\<Omega>).c3 = <[1,3,6]>"
apply(subst  sum1EqCh, simp add: sbdom_rep_eq)
apply(subst SPF.spfcomp_tospfH2)
apply(subst spfcomp_RepAbs, simp_all)
  apply(subst sfa, subst lub_H2_test_getCh)
by(simp add: sbdom_rep_eq)


section \<open>feedback operator\<close>
(* Broy Operator *)  
subsection \<open>primrec definition\<close>

  
primrec spfFeedbackHelper :: "nat \<Rightarrow> 'a SPF \<Rightarrow> 'a SB \<Rightarrow> 'a SB" where
  "spfFeedbackHelper 0 f sb = (spfDom\<cdot>f \<union> spfRan\<cdot>f)^\<bottom>" |
  "spfFeedbackHelper (Suc i) f sb = 
    (let last = spfFeedbackHelper i f sb in
    (sb \<uplus> (f \<rightleftharpoons> (last \<bar> spfDom\<cdot>f))))"
  
definition spfFeedbackOperatorRec :: "'a SPF \<Rightarrow> 'a SPF"  where (* ("\<mu>_" 50) *)
  "spfFeedbackOperatorRec f \<equiv> Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = spfDom\<cdot>f - spfRan\<cdot>f) \<leadsto> 
    ((\<Squnion>i. spfFeedbackHelper i f sb  ) \<bar> (spfRan\<cdot>f)))"

  
subsection \<open>iterate definition\<close>

  
definition spfFeedbackOperator :: "'a SPF \<Rightarrow> 'a SPF" ("\<mu>_" 50) where
"spfFeedbackOperator f \<equiv>
let I  = spfDom\<cdot>f - spfRan\<cdot>f;
    I1 = spfDom\<cdot>f;
    C  = spfRan\<cdot>f
in Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = I) \<leadsto>
    (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. (f\<rightleftharpoons>((sb \<uplus> z)\<bar> I1)))\<cdot>(C^\<bottom>)))" 


definition spfFeedbackOperator2 :: "'a SPF \<Rightarrow> 'a SPF" where
"spfFeedbackOperator2 f \<equiv>
let I  = spfDom\<cdot>f - spfRan\<cdot>f;
    I1 = spfDom\<cdot>f;
    C  = (spfDom\<cdot>f \<union> spfRan\<cdot>f)
in Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = I) \<leadsto>
    (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. sb \<uplus> (f\<rightleftharpoons>(z \<bar> I1)))\<cdot>(C^\<bottom>)) \<bar> (spfRan\<cdot>f))" 


subsection \<open>operator equality\<close>

subsubsection prerequirements
  
  
lemma [simp]: "cont (\<lambda> z. sb \<uplus> (f\<rightleftharpoons>(z\<bar>spfDom\<cdot>f)))"
  by (simp add: conthelper)
  
lemma feedbackHelpFunctionEq: "iterate i\<cdot>(\<Lambda> z. (sb \<uplus> f\<rightleftharpoons>(z\<bar>spfDom\<cdot>f)))\<cdot>((spfDom\<cdot>f \<union> spfRan\<cdot>f)^\<bottom>) = spfFeedbackHelper i f sb"
  apply(induct_tac i)
   apply simp
  apply(unfold iterate_Suc)
  by simp
    
    
subsubsection \<open>spfFeedbackOperatorRec eq spfFeedbackOperator2\<close>  

  
lemma spfFeedbackOperatorEqRec: "spfFeedbackOperator2 f = spfFeedbackOperatorRec f"
  apply(simp add: spfFeedbackOperator2_def spfFeedbackOperatorRec_def)
  apply(subst feedbackHelpFunctionEq)
    by auto

    
      
section \<open>sum4SPF definition\<close>

  

definition idC :: "nat SPF" where
"idC \<equiv> idSPF (c5, c1)"

lemma [simp]: "spfDom\<cdot>idC = {c5}"
by (simp add: idC_def)  

lemma [simp]: "spfRan\<cdot>idC = {c1}"
by (simp add: idC_def)

(* \<mu>((idC \<parallel> append0C) \<circ> addC) *)  
definition sum4SPF :: "nat SPF" where
"sum4SPF \<equiv> spfFeedbackOperator (sercomp (idC \<parallel> append0C) addC)"

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
  
  
section \<open>sum1SPF eq sum4SPF\<close>
  
subsection \<open>lemma\<close> 
(* final lemma *)  
  
lemma sum1SPFeqSum4SPF: assumes "sbDom\<cdot>sb = I addC append0C"
  shows "(sum1SPF \<rightleftharpoons> sb) . c3 = (sum4SPF \<rightleftharpoons> sb) . c3" 
  oops
      
  
section \<open>sum1SPF eq sum4\<close>

  
  (* old proof structure
subsection prerequirements
(* prerequirements for final lemma *)

lemma sbZ_eq:"([c2 \<mapsto> \<up>0\<bullet>z]\<Omega>) \<uplus> ([c3 \<mapsto> z]\<Omega>) = ([c2 \<mapsto> \<up>0\<bullet>z, c3 \<mapsto> z]\<Omega>)"
sorry
  
lemma spfCompFeedback_iter_prefix: assumes "sbDom\<cdot>sb = I addC append0C" 
                                       and "z = add\<cdot>(sb . c1)\<cdot>(\<up>0\<bullet>z)"
                                     shows "(iter_spfCompH3 addC append0C i sb) \<sqsubseteq>  ([c2 \<mapsto> \<up>0\<bullet>z, c3 \<mapsto> z]\<Omega>)"
 proof(induct i)
   case 0
   then show ?case
     apply(subst less_SBI)
       apply(simp_all add: sbLeast_def)
       apply(simp add: dom_def)
       by auto
 next
   case (Suc i)
   then show ?case 
     apply(subst less_SBI)
       apply(simp)
       sorry
 qed

lemma sum4_finiteInput: assumes "z = add\<cdot>x\<cdot>(\<up>0\<bullet>z)"
                            and "#x < \<infinity>"
                          shows "#z < \<infinity>"
proof (rule ccontr)
  have f1: "#z = \<infinity> \<Longrightarrow> #(add\<cdot>x\<cdot>(\<up>0\<bullet>z)) = \<infinity>"
    using assms(1) by auto
  then have f2: "#z = \<infinity> \<Longrightarrow> #x = \<infinity>"
    by simp
  assume "~ ?thesis"
  then show False
    using f2 assms(2) by (simp add: less_le)
qed
   
lemma spfCompFeedback_iter_nthEq: assumes "sbDom\<cdot>sb = I addC append0C" 
                                      and "z = add\<cdot>(sb . c1)\<cdot>(\<up>0\<bullet>z)"
                                      and "#(sb . c1) < \<infinity>"
  shows "stake i\<cdot>((iter_spfCompH3 addC append0C (2 * i) sb) . c3) = stake i\<cdot>z"
  sorry
    
lemma spfCompFeedback_iter_nthEq2: assumes "sbDom\<cdot>sb = I addC append0C" 
                                      and "z = add\<cdot>(sb . c1)\<cdot>(\<up>0\<bullet>z)"
                                      and "#(sb . c1) < \<infinity>"
  shows "stake i\<cdot>((iter_spfCompH3 addC append0C (2 * i) sb) . c3) = stake i\<cdot>(\<up>0\<bullet>z)"
  sorry
   
lemma spfCompFeedback_lub_iter_finiteInput: assumes "sbDom\<cdot>sb = I addC append0C" 
                                                and "z = add\<cdot>(sb . c1)\<cdot>(\<up>0\<bullet>z)"
                                                and "#(sb . c1) < \<infinity>"
                                              shows "(\<Squnion>i. (iter_spfCompH3 addC append0C i sb)) = ([c2 \<mapsto> \<up>0\<bullet>z, c3 \<mapsto> z]\<Omega>)"
proof - 
  have f11: "sbDom\<cdot>(\<Squnion>i. (iter_spfCompH3 addC append0C i sb)) = {c2,c3}"
    apply(subst lub_iter_spfCompH3_dom)
    by(simp_all add: assms)
  have f12: "sbDom\<cdot>([c2 \<mapsto> \<up>0\<bullet>z, c3 \<mapsto> z]\<Omega>) = {c2,c3}"
    sorry
  then have f13: "sbDom\<cdot>(\<Squnion>i. (iter_spfCompH3 addC append0C i sb)) = sbDom\<cdot>([c2 \<mapsto> \<up>0\<bullet>z, c3 \<mapsto> z]\<Omega>)"
    using f11 f12 by auto
  have f21: "(\<Squnion>i. (iter_spfCompH3 addC append0C i sb)) . c2 = \<up>0\<bullet>z"
    sorry
  then have f22: "(\<Squnion>i. (iter_spfCompH3 addC append0C i sb)) . c2 = ([c2 \<mapsto> \<up>0\<bullet>z, c3 \<mapsto> z]\<Omega>) . c2"
    sorry
  have f31: "(\<Squnion>i. (iter_spfCompH3 addC append0C i sb)) . c3 = z"
    sorry
  then have f32: "(\<Squnion>i. (iter_spfCompH3 addC append0C i sb)) . c3 = ([c2 \<mapsto> \<up>0\<bullet>z, c3 \<mapsto> z]\<Omega>) . c3"
    sorry
  show ?thesis
    apply(subst sb_eq, simp_all)
    using f13 apply auto[1]
    sorry
qed

lemma spfCompFeedback_lub_iter_infiniteInput: assumes "sbDom\<cdot>sb = I addC append0C" 
                                                  and "z = add\<cdot>(sb . c1)\<cdot>(\<up>0\<bullet>z)"
                                                  and "#(sb . c1) = \<infinity>"
  shows "(\<Squnion>i. (iter_spfCompH3 addC append0C i sb)) = ([c2 \<mapsto> \<up>0\<bullet>z]\<Omega>) \<uplus> ([c3 \<mapsto> z]\<Omega>)"  
  sorry    
    
lemma spfCompFeedbackFixEq: assumes "sbDom\<cdot>sb = I addC append0C" and "z = add\<cdot>(sb . c1)\<cdot>(\<up>0\<bullet>z)"
  shows "(\<Squnion>i. (iter_spfCompH3 addC append0C i sb)) = ([c2 \<mapsto> \<up>0\<bullet>z]\<Omega>) \<uplus> ([c3 \<mapsto> z]\<Omega>)"
proof(cases "#(sb . c1) < \<infinity>")
  case True
  then show ?thesis
    apply(subst sbZ_eq)
    using assms(1) assms(2) spfCompFeedback_lub_iter_finiteInput by blast
next
  case False
  have "\<not> #(sb . c1) < \<infinity> \<Longrightarrow> #(sb . c1) = \<infinity>"
    by (simp add: less_le)
  then show ?thesis 
    using False assms(1) assms(2) spfCompFeedback_lub_iter_infiniteInput by blast
qed
  
lemma spfCompFeedbackFixEqHelper: assumes "sbDom\<cdot>sb = I addC append0C" and "z = add\<cdot>(sb . c1)\<cdot>(\<up>0\<bullet>z)"
  shows "(\<Squnion>i. iterate i\<cdot>(spfCompH3 addC append0C sb)\<cdot>({c2, c3}^\<bottom>)) = ([c2 \<mapsto> \<up>0\<bullet>z]\<Omega>) \<uplus> ([c3 \<mapsto> z]\<Omega>)"
proof - 
  have "(\<Squnion>i. iterate i\<cdot>(spfCompH3 addC append0C sb)\<cdot>({c2, c3}^\<bottom>)) = (\<Squnion>i. (iter_spfCompH3 addC append0C i sb))"
    by simp
  then show ?thesis
    using assms(1) assms(2) spfCompFeedbackFixEq by presburger
qed


lemma spfCompFeedbackFixEqCh: assumes "sbDom\<cdot>sb = I addC append0C" and "z = add\<cdot>(sb . c1)\<cdot>(\<up>0\<bullet>z)"
  shows "(\<Squnion>i. iterate i\<cdot>(spfCompH3 addC append0C sb)\<cdot>({c2, c3}^\<bottom>)) . c3 = z"
proof -
  have f1: "(\<Squnion>i. iterate i\<cdot>(spfCompH3 addC append0C sb)\<cdot>({c2, c3}^\<bottom>)) = ([c2 \<mapsto> \<up>0\<bullet>z]\<Omega>) \<uplus> ([c3 \<mapsto> z]\<Omega>)"
    by (metis spfCompFeedbackFixEqHelper assms)
  have f2: "([c2 \<mapsto> \<up>0 \<bullet> z]\<Omega>) \<uplus> ([c3 \<mapsto> z]\<Omega>) . c3 = z"
    by (subst sbunion_getchR, simp_all add: sbdom_rep_eq)
  thus ?thesis
    by (simp add: f1)
qed
       
*)   
      
subsubsection general      
      
  
lemma spfcomp2_RepAbs: assumes "spfComp_well f1 f2" shows
 "Rep_CSPF (Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompH3 f1 f2 x)\<cdot>((spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)^\<bottom>))))
            = (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompH3 f1 f2 x)\<cdot>((spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)^\<bottom>)))"
  by simp   
  
lemma sbDomSB_eq: assumes "sbDom\<cdot>sb = {c1}" shows "sb = ([c1 \<mapsto> sb . c1]\<Omega>)"
  apply(subst sb_eq, simp_all)
   apply (metis Rep_SB_inverse assms dom_eq_singleton_conv fun_upd_same insertI1 sbdom_insert sbgetchE)
    by (metis Rep_SB_inverse assms dom_eq_singleton_conv fun_upd_same sbdom_insert sbgetchE singletonD)
    
    
subsection \<open>lemma\<close> 
(* final lemma *)

    
lemma sumEq: assumes "sbDom\<cdot>sb = I addC append0C" shows "(sum1SPF \<rightleftharpoons> sb) . c3 = sum4\<cdot>(sb . c1)"
  apply(subst sum1EqCh, simp add: assms)
  apply(subst spfcomp_and_spfcomp2_eq)
  apply(subst spfcompH3_abbrv_tospfH32)
  apply(subst spfcomp2_RepAbs, simp_all add: assms)
  apply(simp add: sum4_sb_spf_eq)
  apply(subst SPF_FeedComp_JB.addC_def, subst SPF_Feedback_MW.addC_def)
  apply(subst SPF_FeedComp_JB.append0C_def, subst SPF_Feedback_MW.append0C_def)
  apply(subst (2) sbDomSB_eq)
  by(simp_all add: assms SPF_FeedComp_JB.addC_def SPF_FeedComp_JB.append0C_def)
  
(*  apply(subst sum1EqCh, simp add: assms)
  apply(subst spfcomp_and_spfcomp2_eq)
  apply(subst spfcompH3_abbrv_tospfH32)
  apply(subst spfcomp2_RepAbs, simp_all add: assms)
  apply(subst spfCompFeedbackFixEqCh)
    using assms sum4_unfold  by auto
*)
         
end