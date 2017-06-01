theory SPF_NewFeedback_MW
imports "CaseStudies/StreamCase_Study" SPF_MW SPF_Comp SPF_Templates SPF_FeedComp SPF_Feedback_JB 

begin

section \<open> general lemmas about sercomp and parcomp \<close>  

  
(* Should already be proven *)  
lemma parcomp_cont[simp]: "cont (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))"
sorry  
  
lemma parcomp_spf_well[simp]: "spf_well (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))"  
sorry

lemma sercomp_cont[simp]: "cont (\<lambda> x. (sbDom\<cdot>x =  spfDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> x) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))"
sorry  
  
lemma sercomp_spf_well[simp]: "spf_well (\<Lambda> x. (sbDom\<cdot>x =  spfDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> x) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))"  
sorry  

lemma parcomp_repAbs: "Rep_CSPF (Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))) 
                      = (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))"
  by simp
    
lemma sercomp_repAbs: "Rep_CSPF (Abs_CSPF (\<lambda> x. (sbDom\<cdot>x =  spfDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> x) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))) 
                      = (\<lambda> x. (sbDom\<cdot>x =  spfDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> x) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))"
  by simp
  
section \<open> Feedback Definitions \<close>  

  
definition MapIdFunct :: "(channel \<rightharpoonup> channel) \<Rightarrow> channel \<Rightarrow> channel" where
"MapIdFunct m \<equiv> (\<lambda> c. case m c of None \<Rightarrow> c | Some y \<Rightarrow> y )" 
  
definition sbRenameChMap :: "'m SB \<Rightarrow> (channel \<rightharpoonup> channel) \<Rightarrow> 'm SB" where
"sbRenameChMap sb m \<equiv> Abs_SB (\<lambda>c. Rep_SB(sb)((MapIdFunct m)(c)))"  
  
definition spfRename :: "'a SPF \<Rightarrow> (channel \<rightharpoonup> channel) \<Rightarrow> 'a SPF" where
"spfRename f m \<equiv> Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - dom(m)) \<union> ran(m)) \<leadsto> (f \<rightleftharpoons> (sbRenameChMap sb m)))" 
  
definition spfFeedbackOperator_new :: "'a SPF \<Rightarrow> (channel \<rightharpoonup> channel) \<Rightarrow> 'a SPF" where
"spfFeedbackOperator_new f m \<equiv> spfFeedbackOperator (spfRename f m)"   


section \<open> SPF Definitions \<close>
  
definition idC :: "nat SPF" where
"idC \<equiv> SPF1x1 sb_id (c1, c3)"

definition append0C :: "nat SPF" where
"append0C \<equiv> SPF1x1 (appendElem2 0) (c2,c4)"

definition addC :: "nat SPF" where
"addC \<equiv> SPF2x1 add (c3, c4, c5)" 

abbreviation innerSum4SPF :: "nat SPF" where
  "innerSum4SPF \<equiv> ((idC \<parallel> append0C) \<circ> addC)"

definition sum4SPF :: "nat SPF" where
"sum4SPF \<equiv> spfFeedbackOperator_new ((idC \<parallel> append0C) \<circ> addC) [c5 |-> c2]"


subsection \<open> requirements \<close>

lemma [simp]: "spfDom\<cdot>idC = {c1}"
  by(auto simp add: idC_def SPF1x1_dom)
    
lemma [simp]: "spfRan\<cdot>idC = {c3}"
  by(auto simp add: idC_def SPF1x1_ran)

lemma [simp]: "spfDom\<cdot>append0C = {c2}"
  by(auto simp add: append0C_def SPF2x1_dom)
    
lemma [simp]: "spfRan\<cdot>append0C = {c4}"
  by(auto simp add: append0C_def SPF2x1_ran)

lemma [simp]: "spfDom\<cdot>addC = {c3, c4}"
  by(auto simp add: addC_def SPF1x1_dom)
    
lemma [simp]: "spfRan\<cdot>addC = {c5}"
  by(auto simp add: addC_def SPF1x1_ran)    
    
lemma [simp]: "I idC append0C = {c1, c2}"
by (auto simp add: I_def)

lemma [simp]: "Oc idC append0C = {c3, c4}"
by (auto simp add: Oc_def)

lemma [simp]: "L idC append0C = {}"
by (auto simp add: L_def)

lemma [simp]: "spfComp_well idC append0C"
by (simp add: spfComp_well_def)  
  
lemma domIdAppend[simp]: "spfDom\<cdot>(idC \<parallel> append0C) = {c1, c2}"
apply(subst parCompDom, simp_all)
apply(subst spfComp_dom_I)
by simp_all

lemma ranIdAppend[simp]: "spfRan\<cdot>(idC \<parallel> append0C) = {c3, c4}"
apply(subst parCompRan, simp_all)
apply(subst spfComp_ran_Oc)
by simp_all  

lemma [simp]: "I (idC \<parallel> append0C) addC = {c1, c2}"
  by(simp add: I_def)
    
lemma [simp]: "Oc (idC \<parallel> append0C) addC = {c3, c4, c5}"
  by(auto simp add: Oc_def)

lemma [simp]: "L (idC \<parallel> append0C) addC = {c3, c4}"
  by(auto simp add: L_def) 
    
lemma [simp]: "pL (idC \<parallel> append0C) addC = {}"
  by(auto simp add: pL_def) 
  
lemma domIdAppendAdd: "spfDom\<cdot>(innerSum4SPF) = {c1, c2}"
  sorry

lemma ranIdAppendAdd: "spfRan\<cdot>(innerSum4SPF) = {c3, c4, c5}"
  sorry 
  
lemma innerSum4SPF_c5_eq: assumes "sbDom\<cdot>sb = I (idC \<parallel> append0C) addC" shows "(innerSum4SPF \<rightleftharpoons> sb) . c5 = add\<cdot>(sb . c1)\<cdot>(\<up>0\<bullet>(sb . c2))"
proof - 
  have f1: "{c1, c2} = {c2, c1}"
    by auto
  have f2: "sbDom\<cdot>([c3 \<mapsto> sb_id\<cdot>(sb . c1)]\<Omega>) \<union> sbDom\<cdot>([c4 \<mapsto> appendElem2 0\<cdot>(sb . c2)]\<Omega>) = {c3, c4}"
    apply(simp add: sbdom_rep_eq)
    by auto
  have f3: "(([c3 \<mapsto> sb_id\<cdot>(sb . c1)]\<Omega>) \<uplus> ([c4 \<mapsto> appendElem2 0\<cdot>(sb . c2)]\<Omega>)) . c3 = sb_id\<cdot>(sb . c1)"
    apply(subst sbunion_getchL)
     apply(simp add: sbdom_rep_eq)
      by simp
  have f4: "(([c3 \<mapsto> sb_id\<cdot>(sb . c1)]\<Omega>) \<uplus> ([c4 \<mapsto> appendElem2 0\<cdot>(sb . c2)]\<Omega>)) . c4 = appendElem2 0\<cdot>(sb . c2)"
    apply(subst sbunion_getchR)
     apply(simp add: sbdom_rep_eq)
      by simp
      (* doesn't work with variables *)
    have f5: "([c3 \<mapsto> sb_id\<cdot>(sb . c1)]\<Omega>) \<uplus> ([c4 \<mapsto> appendElem2 0\<cdot>(sb . c2)]\<Omega>) 
            \<uplus> ([c5 \<mapsto> add\<cdot>(sb_id\<cdot>(sb . c1))\<cdot>(appendElem2 0\<cdot>(sb . c2))]\<Omega>) . c5
            = add\<cdot>(sb_id\<cdot>(sb . c1))\<cdot>(appendElem2 0\<cdot>(sb . c2))"
    apply(subst sbunion_getchR)
     apply(simp add: sbdom_rep_eq)
       by(simp)
  show ?thesis  
    apply(simp only: sercomp_def)
    apply(simp only: sercomp_repAbs, simp add: assms)
    apply(simp only: parcomp_def)
    apply(simp only: parcomp_repAbs, simp add: assms f1)
    apply(simp add: idC_def append0C_def addC_def)
    apply(simp add: SPF1x1_rep_eq SPF2x1_rep_eq assms)
    apply(simp add: f2 f3 f4)
    apply(simp only: f5)
    by(simp add: sb_id_def appendElem2_def)
qed

section \<open> spfRename lemmas \<close>  
  
      
section \<open> result \<close>
  
lemma finalLemma: assumes "sbDom\<cdot>sb = spfDom\<cdot>sum4SPF" shows "(sum4SPF \<rightleftharpoons> sb) . c5 =  sum4\<cdot>(sb . c1)"
sorry     
      
end