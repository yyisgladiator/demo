(*  Title: InnerCase_Study
    Author: Marc Wiartalla, Jens Christoph Bürger
    e-mail: marc.wiartalla@rwth-aachen.de, jens.buerger@rwth-aachen.de

    Description: Evaluation of the serial and parallel composition using the general composition
                 operator
*)

theory InnerProd_Case_Study
  imports "../SPF"  "../SPF_Templates"  "../SPF_Composition_JB" "../Streams" "../SPF_Comp"  
            "../CaseStudies/StreamCase_Study" "../SPF_MW" "../ParComp_MW_JB"

begin

(* message instantiation already done in SerComp *)

(* DEFINITION ADD/MULT *)
(* Before we can build up the inner component we have to define the add and mult components first *)
(* ----------------------------------------------------------------------- *)
section \<open>Definitions\<close>
(* ----------------------------------------------------------------------- *)
  
(* As the necessary properties are already proved in SPF_Templates the components can be defined
   with a simple definition *)
definition mult1 :: "nat SPF" where
"mult1 \<equiv> SPF2x1 mult (c1,c2,c5)"

definition mult2 :: "nat SPF" where
"mult2 \<equiv> SPF2x1 mult (c3,c4,c6)"

definition addC :: "nat SPF" where
"addC \<equiv> SPF2x1 add (c5,c6,c7)"


definition innerProd :: "nat SPF" where
"innerProd \<equiv> ((mult1 \<otimes> mult2) \<otimes> addC) \<h> {c5, c6}"

definition innerProd2 :: "nat SPF" where
"innerProd2 \<equiv> ((mult1 \<parallel> mult2) \<circ> addC) \<h> {c5, c6}"


(* ----------------------------------------------------------------------- *)
section \<open>Component lemmata\<close>
(* ----------------------------------------------------------------------- *)   

(* To make the usage of the components even simpler the following lemmata are introduced 
   Note: The basis for this lemmata is still SPF_Templates *)
  
subsection \<open>representation equalities\<close>
(* ----------------------------------------------------------------------- *) 
  
lemma mult1_rep_eqC: "Rep_CSPF mult1 = 
                                (\<lambda> sb. (sbDom\<cdot>sb = {c1, c2}) \<leadsto> ([c5 \<mapsto> mult\<cdot>(sb . c1)\<cdot>(sb . c2)]\<Omega>))"
  by (auto simp add: SPF2x1_rep_eq mult1_def)

lemma mult2_rep_eqC: "Rep_CSPF mult2 = 
                                (\<lambda> sb. (sbDom\<cdot>sb = {c3, c4}) \<leadsto> ([c6 \<mapsto> mult\<cdot>(sb . c3)\<cdot>(sb . c4)]\<Omega>))"
  by (auto simp add: SPF2x1_rep_eq mult2_def)

lemma addC_rep_eqC: "Rep_CSPF addC = 
                                 (\<lambda> sb. (sbDom\<cdot>sb = {c5, c6}) \<leadsto> ([c7 \<mapsto> add\<cdot>(sb . c5)\<cdot>(sb . c6)]\<Omega>))"
  by (auto simp add: SPF2x1_rep_eq addC_def)
 

lemma domMult1: assumes "sbDom\<cdot>sb = {c1, c2}" shows "sbDom\<cdot>(mult1\<rightleftharpoons>sb) = {c5}"
apply(simp add: mult1_rep_eqC)
apply(simp add: assms)
by(simp add: sbDom_def)

lemma domMult2: assumes "sbDom\<cdot>sb = {c3, c4}" shows "sbDom\<cdot>(mult2\<rightleftharpoons>sb) = {c6}"
apply(simp add: mult2_rep_eqC)
apply(simp add: assms)
by(simp add: sbDom_def)    
    
lemma domMult1Restrict: assumes "{c1, c2} \<subseteq> sbDom\<cdot>sb" shows "sbDom\<cdot>(mult1\<rightleftharpoons>(sb\<bar>{c1, c2})) = {c5}"
  using assms domMult1 by auto

lemma domMult2Restrict: assumes "{c3, c4} \<subseteq> sbDom\<cdot>sb" shows "sbDom\<cdot>(mult2\<rightleftharpoons>(sb\<bar>{c3, c4})) = {c6}"
  using assms domMult2 by auto
    
lemma mult1Eq: assumes "sbDom\<cdot>sb = {c1, c2}" shows "mult1 \<rightleftharpoons> sb . c5 = mult\<cdot>(sb . c1)\<cdot>(sb . c2)"
apply(simp add: mult1_rep_eqC)
by(auto simp add: assms)

lemma mult2Eq: assumes "sbDom\<cdot>sb = {c3, c4}" shows "mult2 \<rightleftharpoons> sb . c6 = mult\<cdot>(sb . c3)\<cdot>(sb . c4)"
apply(simp add: mult2_rep_eqC)
by(auto simp add: assms)

lemma addCEq: assumes "sbDom\<cdot>sb = {c5, c6}" shows "addC \<rightleftharpoons> sb . c7 = add\<cdot>(sb . c5)\<cdot>(sb . c6)"
apply(simp add: addC_rep_eqC)
by(auto simp add: assms)


subsection \<open>Channel sets\<close>
(* ----------------------------------------------------------------------- *) 

(* To show that the components "fit" together the domain and range as well as the composition 
   specific channel sets are evaluated *)  
  
(* mult1 *)
lemma [simp]: "spfDom\<cdot>mult1 = {c1,c2}"
  by(simp add: mult1_def)

lemma [simp]: "spfRan\<cdot>mult1 = {c5}"
  by(simp add: mult1_def)

(* mult2 *)
lemma [simp]: "spfDom\<cdot>mult2 = {c3,c4}"
  by(simp add: mult2_def)

lemma [simp]: "spfRan\<cdot>mult2 = {c6}"
  by(simp add: mult2_def)

(* addC *)
lemma [simp]: "spfDom\<cdot>addC = {c5,c6}"
  by(simp add: addC_def)

lemma [simp]: "spfRan\<cdot>addC = {c7}"
  by(simp add: addC_def)

    
subsubsection \<open>parallel comp mults\<close>
    
lemma [simp]: "spfComp_well mult1 mult2"
  by (simp add: spfComp_well_def)

lemma [simp]: "no_selfloops mult1 mult2"
  by(simp add: no_selfloops_def)

lemma [simp]: "C mult1 mult2 = {c1,c2,c3,c4,c5,c6}"
  by (auto simp add: C_def)

lemma [simp]: "L mult1 mult2 = {}"
  by (auto simp add: L_def)

lemma [simp]: "Oc mult1 mult2 = {c5,c6}"
  by (auto simp add: Oc_def)

lemma [simp]: "I mult1 mult2 = {c1,c2,c3,c4}"
  by auto
    
    
subsubsection \<open>complete comp\<close> 
    
lemma [simp]: "spfDom\<cdot>(spfcomp mult1 mult2) = {c1, c2, c3, c4}"
by(simp add: spfComp_dom_I)

lemma [simp]: "spfRan\<cdot>(spfcomp mult1 mult2) = {c5, c6}"
by(simp add: spfComp_ran_Oc)

lemma [simp]: "spfComp_well (spfcomp mult1 mult2) addC"
by(simp add: spfComp_well_def)

lemma [simp]: "no_selfloops (spfcomp mult1 mult2) addC"
by(simp add: no_selfloops_def)

lemma [simp]: "C (spfcomp mult1 mult2) addC = {c1,c2,c3,c4,c5,c6,c7}"
by(auto simp add: C_def)

lemma [simp]: "L (spfcomp mult1 mult2) addC = {c5,c6}"
by(auto simp add: L_def)

lemma [simp]: "pL (spfcomp mult1 mult2) addC = {}"
by(auto simp add: pL_def)

lemma [simp]: "Oc (spfcomp mult1 mult2) addC = {c5, c6, c7}"
by(auto simp add: Oc_def)

lemma [simp]: "I (spfcomp mult1 mult2) addC  = {c1,c2,c3,c4}"
by(auto simp add: I_def)

lemma [simp]: "spfDom\<cdot>( spfcomp (spfcomp mult1 mult2) addC) = {c1, c2, c3, c4}"
apply(subst spfComp_dom_I)
by(simp_all add: I_def parCompDom parCompRan)
   
  
(* ----------------------------------------------------------------------- *)
section \<open>mult parallelcomposition properties\<close>
(* ----------------------------------------------------------------------- *)
  
  (* before the properties of the complete composition can be evaluated, we show some basic 
     properties of the parallel composition of mult1 and mult2 *)

lemma mult_comp1: assumes "sbDom\<cdot>sb = I mult1 mult2"
  shows "((Rep_CSPF (spfcomp mult1 mult2)) \<rightharpoonup> sb) . c5 
            = ((Rep_CSPF(mult1)) \<rightharpoonup> (sb\<bar>spfDom\<cdot>mult1)) . c5"
  by (subst spfCompParallelGetch1, simp_all add: assms)

lemma mult_comp2: assumes "sbDom\<cdot>sb = I mult1 mult2"
  shows "((Rep_CSPF (spfcomp mult1 mult2)) \<rightharpoonup> sb) . c6 
            = ((Rep_CSPF(mult2)) \<rightharpoonup> (sb\<bar>spfDom\<cdot>mult2)) . c6"
  by (subst spfCompParallelGetch2, simp_all add: assms)

lemma contMult1: "cont (\<lambda>x. (mult1\<rightleftharpoons>(x\<bar>{c1, c2})))"
by(subst conthelper, simp_all)

lemma contMult1Union: "cont (\<lambda>x. sbUnion\<cdot>(mult1\<rightleftharpoons>(x\<bar>{c1, c2})))"
by(simp add: contMult1)

lemma contMult2: "cont (\<lambda>x. (mult2\<rightleftharpoons>(x\<bar>{c3, c4})))"
  by(subst conthelper, simp_all)
    
    
lemma mults_comp1: assumes "sbDom\<cdot>sb = I mult1 mult2"
                   and "c \<in> spfRan\<cdot>mult1" 
shows "((Rep_CSPF (spfcomp mult1 mult2)) \<rightharpoonup> sb). c  = ((Rep_CSPF(mult1)) \<rightharpoonup> (sb\<bar>spfDom\<cdot>mult1)) .c"
  apply(subst spfCompParallelGetch1, simp_all add: assms)
proof -
  have "c \<in> spfRan\<cdot>mult1"
    using assms(2) by auto
  thus "c = c5"
    by (auto simp add: assms)
qed
  
lemma mults_comp2: assumes "sbDom\<cdot>sb = I mult1 mult2"
                   and "c \<in> spfRan\<cdot>mult2" 
shows "((Rep_CSPF (spfcomp mult1 mult2)) \<rightharpoonup> sb). c  = ((Rep_CSPF(mult2)) \<rightharpoonup> (sb\<bar>spfDom\<cdot>mult2)) .c"
  apply(subst spfCompParallelGetch2, simp_all add: assms)
proof -
  have "c \<in> spfRan\<cdot>mult2"
    using assms(2) by auto
  thus "c = c6"
    by (auto simp add: assms)
qed

    
lemma mults_comp: assumes "sbDom\<cdot>sb = I mult1 mult2"
  shows "((spfcomp mult1 mult2) \<rightleftharpoons> sb)  
            = ((mult1) \<rightleftharpoons> (sb\<bar>spfDom\<cdot>mult1)) \<uplus> ((mult2) \<rightleftharpoons> (sb\<bar>spfDom\<cdot>mult2))"
proof -
  have f1: "sbDom\<cdot>((mult1) \<rightleftharpoons> (sb\<bar>spfDom\<cdot>mult1)) = {c5}"
    by(subst spfran2sbdom2, simp_all add: assms)
  have f2: "sbDom\<cdot>((mult2) \<rightleftharpoons> (sb\<bar>spfDom\<cdot>mult2)) = {c6}"
    by(subst spfran2sbdom2, simp_all add: assms)
  have f3: "sbDom\<cdot>(((mult1) \<rightleftharpoons> (sb\<bar>spfDom\<cdot>mult1)) \<uplus> ((mult2) \<rightleftharpoons> (sb\<bar>spfDom\<cdot>mult2))) = {c5,c6}"
    apply(subst  sbunionDom, simp only: f1 f2)
    by auto
      
  (* lemmata for subgoal I of sb_eq rule *)   
  have f14: "sbDom\<cdot>((spfcomp mult1 mult2) \<rightleftharpoons> sb) = {c5,c6}"
    apply(subst spfran2sbdom2)
    by(simp_all add: assms I_def, auto)
        
  (* lemmata for subgoal II of sb_eq rule *)     
  have f21: "((spfcomp mult1 mult2) \<rightleftharpoons> sb). c5  = 
                          (((mult1) \<rightleftharpoons> (sb\<bar>spfDom\<cdot>mult1)) \<uplus> ((mult2) \<rightleftharpoons> (sb\<bar>spfDom\<cdot>mult2))) .c5"
    apply(subst sbunion_getchL)
     apply(auto simp only: f2)
      by(simp add: mults_comp1 assms)
  have f22: "((Rep_CSPF (spfcomp mult1 mult2)) \<rightharpoonup> sb). c6  = 
            (((mult1) \<rightleftharpoons> (sb\<bar>spfDom\<cdot>mult1)) \<uplus> ((mult2) \<rightleftharpoons> (sb\<bar>spfDom\<cdot>mult2))) .c6"
    apply(subst sbunion_getchR)
     apply(auto simp only: f2)
    by(simp add: mults_comp2 assms)
  have f23: "\<And>c. c \<in> sbDom\<cdot>((spfcomp mult1 mult2) \<rightleftharpoons> sb) 
              \<Longrightarrow> ((spfcomp mult1 mult2) \<rightleftharpoons> sb) . c 
                    = (((mult1) \<rightleftharpoons> (sb\<bar>spfDom\<cdot>mult1)) \<uplus> ((mult2) \<rightleftharpoons> (sb\<bar>spfDom\<cdot>mult2))) . c"
    apply(simp only: f14)
    using f21 f22 by blast
  show ?thesis
    apply(rule sb_eq)
     apply(simp only: f3 f14)
    by(simp add: f23)
qed
 

  
(* ----------------------------------------------------------------------- *)
section \<open>main lemmata\<close>
(* ----------------------------------------------------------------------- *)   
  (* After the properties of the parallel composition have been successfully evaluated, 
     the main lemma can be proved *)

lemma innerprod_serComp: assumes "sbDom\<cdot>sb = I (spfcomp mult1 mult2) addC"
  shows "((spfcomp (spfcomp mult1 mult2) addC)  \<rightleftharpoons> sb) . c7 = 
         (addC \<rightleftharpoons> ((spfcomp mult1 mult2) \<rightleftharpoons> (sb\<bar>(spfDom\<cdot>(spfcomp mult1 mult2))))) . c7"
  by (subst spfCompSeriellGetch, simp_all add: assms spfComp_ran_Oc)
  
lemma innerProdEqCh: assumes "sbDom\<cdot>sb = I (spfcomp mult1 mult2) addC" 
    shows "(innerProd  \<rightleftharpoons> sb) . c7 = (spfcomp (spfcomp mult1 mult2) addC) \<rightleftharpoons> sb . c7"
  by (metis (no_types, lifting) channel.distinct(111) channel.distinct(131) hideSbRestrictCh 
        innerProd_def insertE option.collapse sbgetch_insert singletonD spfDomHide spfdom2sbdom)

      
subsection \<open>inner Prod I\<close>
(* ----------------------------------------------------------------------- *)   

lemma innerprod_main: assumes "sbDom\<cdot>sb = I (spfcomp mult1 mult2) addC"
  shows "(innerProd  \<rightleftharpoons> sb) . c7 = add\<cdot>(mult\<cdot>(sb . c1)\<cdot>(sb . c2))\<cdot>(mult\<cdot>(sb . c3)\<cdot>(sb . c4))"
  apply(subst innerProdEqCh)
    apply(simp add: assms)
  apply(subst innerprod_serComp, simp_all add: assms)
  apply(subst mults_comp, simp_all add: assms)
  apply(subst addCEq, simp)
    apply(subst domMult1Restrict, simp add: assms)
    apply(subst domMult2Restrict, auto simp add: assms)
  apply(subst sbunion_getchL, subst domMult2, simp_all add: assms)
  apply(subst sbunion_getchR, subst domMult2, simp_all add: assms)
  apply(subst mult1Eq, simp add: assms)
  apply(subst mult2Eq, simp add: assms)
  by simp

    
subsection \<open>inner Prod II\<close>
(* ----------------------------------------------------------------------- *)  
  
lemma spfcomp_well_parallelOp: "spfComp_well (mult1\<parallel>mult2) addC"
apply(simp add: spfComp_well_def parallelOperatorEq)
by(simp add: parCompRan)

lemma no_selfloops_parallelOp: "no_selfloops (mult1\<parallel>mult2) addC"
apply(simp add: no_selfloops_def)
by(simp add: parCompDom parCompRan)

lemma innerProdEq2: "innerProd \<equiv> innerProd2"
apply(simp add: innerProd_def innerProd2_def parallelOperatorEq)
apply(subst serialOperatorEq)
apply(simp add: pL_def parCompDom parCompRan)
apply(simp add: spfcomp_well_parallelOp, simp_all)
  by(simp add: parCompRan)
    
 
(* ----------------------------------------------------------------------- *)
section \<open>unused lemmata\<close>
(* ----------------------------------------------------------------------- *)       
lemma multcomp_cont: "cont (\<lambda>x. (sbDom\<cdot>x = {c3, c4, c1, c2})\<leadsto>
                                          ((mult1\<rightleftharpoons>(x\<bar>spfDom\<cdot>mult1)) \<uplus> (mult2\<rightleftharpoons>(x\<bar>spfDom\<cdot>mult2))))"
apply(subst if_then_cont, simp_all)
apply(subst cont2cont_APP)
by(simp_all add: contMult1Union contMult2)


end