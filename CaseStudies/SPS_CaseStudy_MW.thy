theory SPS_CaseStudy_MW
imports  "SPF_FeedComp_JB" "../SPF_Comp" "../SPF_Templates" "../SPS"
  
begin

section \<open>Definitions\<close>

  
subsection \<open>Composition\<close>
  
  
definition spsCompPar :: "'m SPS \<Rightarrow>'m  SPS \<Rightarrow> 'm SPS" (infixl "\<parallel>" 50) where
  "spsCompPar S1 S2 \<equiv> Abs_SPS {f1 \<parallel> f2 | f1 f2. f1\<in>(Rep_SPS S1) \<and> f2\<in>(Rep_SPS S2)}"  
 
definition spsCompSer :: "'m SPS \<Rightarrow>'m  SPS \<Rightarrow> 'm SPS" (infixl "\<circle>" 50) where
  "spsCompSer S1 S2 \<equiv> Abs_SPS {f1 \<circ> f2 | f1 f2. f1\<in>(Rep_SPS S1) \<and> f2\<in>(Rep_SPS S2)}" 

definition spsCompFeedback :: "'m SPS  \<Rightarrow> 'm SPS" where
  "spsCompFeedback S \<equiv> Abs_SPS { spfFeedbackOperator f1 | f1. f1\<in>(Rep_SPS S)}" 

lemma spsCompPar_well[simp]: assumes "\<forall> f\<in>(Rep_SPS S1). \<forall> g\<in>(Rep_SPS S2). spfDom\<cdot>f = spfDom\<cdot>g" 
                                 and "\<forall> f\<in>(Rep_SPS S1). \<forall> g\<in>(Rep_SPS S2). spfRan\<cdot>f = spfRan\<cdot>g" 
  shows "sps_well {f1 \<parallel> f2 | f1 f2. f1\<in>(Rep_SPS S1) \<and> f2\<in>(Rep_SPS S2)}"
  sorry
    
lemma spsCompSer_well[simp]: assumes "\<forall> f\<in>(Rep_SPS S1). \<forall> g\<in>(Rep_SPS S2). spfDom\<cdot>f = spfDom\<cdot>g" 
                                 and "\<forall> f\<in>(Rep_SPS S1). \<forall> g\<in>(Rep_SPS S2). spfRan\<cdot>f = spfRan\<cdot>g" 
  shows "sps_well {f1 \<circ> f2 | f1 f2. f1\<in>(Rep_SPS S1) \<and> f2\<in>(Rep_SPS S2)}"
  sorry
    
lemma spsCompFeedback_well[simp]: "sps_well { spfFeedbackOperator f1 | f1. f1\<in>(Rep_SPS S1)}"
  sorry
  
subsection \<open>Ariane\<close>

(* idC *)  
  
definition idC :: "nat SPF" where
"idC \<equiv> SPF1x1 sb_id (c1, c3)"

lift_definition SumSPSComp1 :: "nat SPS" is
  "{idC}"
  by(simp add: sps_well_def)   

lemma idC_eq: "Rep_SPS (Abs_SPS {idC}) = {idC}"
  using SumSPSComp1.abs_eq SumSPSComp1.rep_eq by auto   
    
(* append0C *)     
    
definition append0C :: "nat SPF" where
"append0C \<equiv> SPF1x1 (appendElem2 0) (c2,c4)"  
  
lift_definition SumSPSComp2 :: "nat SPS" is
  "{append0C}"
  by(simp add: sps_well_def)
    
lemma append0C_eq: "Rep_SPS (Abs_SPS {append0C}) = {append0C}"
  using SumSPSComp2.abs_eq SumSPSComp2.rep_eq by auto 
    
(* addC *)  
  
definition addC :: "nat SPF" where
"addC \<equiv> SPF2x1 add (c3, c4, c2)" 

lift_definition SumSPSComp3 :: "nat SPS" is
  "{addC}"
  by(simp add: sps_well_def)
    
lemma addC_eq: "Rep_SPS (Abs_SPS {addC}) = {addC}"
  using SumSPSComp3.abs_eq SumSPSComp3.rep_eq by auto
  
    
(* constant stream *) 

lemma constStream_cont[simp]: "cont (\<lambda> sb. (sbDom\<cdot>sb = {}) \<leadsto> ([c5\<mapsto>(s :: nat stream)]\<Omega>))"
  by simp

lemma constStream_spfWell[simp]: "spf_well (\<Lambda> sb. (sbDom\<cdot>sb = {}) \<leadsto> ([c5\<mapsto>(s :: nat stream)]\<Omega>))"
  apply(simp add: spf_well_def)
  apply(simp only: domIff2)
  apply(simp add: sbdom_rep_eq)
  by(auto) 

lemma constStream_dom[simp]: "spfDom\<cdot>(Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {}) \<leadsto> ([c5\<mapsto>(s :: nat stream)]\<Omega>))) = {}"
proof -
  have "\<exists>sa. sbDom\<cdot>(sa::'a SB) = {} \<and> (sbDom\<cdot>sa = {})\<leadsto>[c5 \<mapsto> s]\<Omega> \<noteq> None"
    by (metis (no_types) option.simps(3) sbleast_sbdom)
  then have "\<exists>sa. sbDom\<cdot>sa = {} \<and> Rep_CSPF (Abs_CSPF (\<lambda>sa. (sbDom\<cdot>sa = {})\<leadsto>[c5 \<mapsto> s]\<Omega>)) sa \<noteq> None"
    by simp
  then show ?thesis
    using spfdom2sbdom by blast
qed
    
lemma constStream_ran[simp]: "spfRan\<cdot>(Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {}) \<leadsto> ([c5\<mapsto>(s :: nat stream)]\<Omega>))) = {c5}"
proof - 
  have "sbDom\<cdot>([c5\<mapsto>(s :: nat stream)]\<Omega>) = {c5}"
    by(simp add: sbDom_def)
  moreover have "(Rep_CSPF (Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {}) \<leadsto> ([c5\<mapsto>(s :: nat stream)]\<Omega>)))) (Abs_SB(Map.empty) :: nat SB) = Some ([c5\<mapsto>(s :: nat stream)]\<Omega>)"
    by(simp) 
  ultimately show ?thesis
    using spfran2sbdom by blast
qed
    
lift_definition SumSPSComp4 :: "nat SPS" is
  "{ Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {}) \<leadsto> ([c5\<mapsto>s]\<Omega>)) | s :: nat stream. #s = \<infinity>}"
  using sps_well_def by fastforce 

abbreviation contStream where "contStream s \<equiv> (Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {}) \<leadsto> ([c5\<mapsto>(s :: nat stream)]\<Omega>)))"    
  
lemma contStream_eq: "Rep_SPS (Abs_SPS {contStream s | s :: nat stream. #s = \<infinity>}) = {contStream s | s :: nat stream. #s = \<infinity>}"
  using SumSPSComp4.abs_eq SumSPSComp4.rep_eq by auto  
  
(* addC2 *) 
    
definition addC2 :: "nat SPF" where
"addC2 \<equiv> SPF2x1 add (c2, c5, c6)" 

lift_definition SumSPSComp5 :: "nat SPS" is
  "{addC2}"
  by(simp add: sps_well_def)

lemma addC2_eq: "Rep_SPS (Abs_SPS {addC2}) = {addC2}"
  using SumSPSComp5.abs_eq SumSPSComp5.rep_eq by auto     
    
(* ariane *)  
    
definition SumSPS :: "nat SPS" where 
  "SumSPS \<equiv> ((spsCompFeedback ((SumSPSComp1 \<parallel> SumSPSComp2) \<circle> SumSPSComp3)) \<parallel> SumSPSComp4) \<circle> SumSPSComp5"

lift_definition SumSPS2 :: "nat SPS" is
  "{ Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c6\<mapsto>add\<cdot>(sum4\<cdot>(sb . c1))\<cdot>s]\<Omega>)) | s :: nat stream. #s = \<infinity>}"
  sorry


section \<open>Evaluation\<close>  
    
lemma finalLemma: assumes "f \<in> Rep_SPS SumSPS" and "sbDom\<cdot>sb = spsDom SumSPS"
  shows "snth n ((f\<rightleftharpoons>sb) . c6) \<ge> snth n (sum4\<cdot>(sb . c1))"
proof - 
  have f1: "sps_well {((\<mu>((idC\<parallel>SPS_CaseStudy_MW.append0C)\<circ>SPS_CaseStudy_MW.addC))\<parallel>f2) |f2. \<exists>s. f2 = contStream s \<and> #s = \<infinity>}"
    sorry
  have f2: "Rep_SPS SumSPS = { ((spfFeedbackOperator ((idC \<parallel> append0C) \<circ> addC)) \<parallel> (contStream s)) \<circ> addC2 | s :: nat stream. #s = \<infinity>}"
    apply(simp add: SumSPS_def)
    apply(simp add: spsCompPar_def spsCompSer_def spsCompFeedback_def)
    apply(simp add: SumSPSComp1_def SumSPSComp2_def SumSPSComp3_def SumSPSComp4_def SumSPSComp5_def) 
    apply(subst contStream_eq)
    apply(subst (2) sps_repAbs)
    apply(simp)
    apply(simp add: f1)
    sorry
  obtain s where f3: "(f = ((spfFeedbackOperator ((idC \<parallel> append0C) \<circ> addC)) \<parallel> (contStream s)) \<circ> addC2) \<and> #s = \<infinity>"
    using assms(1) f2 by auto
  then have f31: "f = ((spfFeedbackOperator ((idC \<parallel> append0C) \<circ> addC)) \<parallel> (contStream s)) \<circ> addC2"
    by blast
  have f4: "((spfFeedbackOperator ((idC \<parallel> append0C) \<circ> addC)) \<rightleftharpoons> sb) . c2 = sum4\<cdot>(sb . c1)"
    sorry
  have f5: "((((spfFeedbackOperator ((idC \<parallel> append0C) \<circ> addC)) \<parallel> (contStream s)) \<circ> addC2) \<rightleftharpoons> sb ). c6 = add\<cdot>(sum4\<cdot>(sb . c1))\<cdot>s"
    sorry
  have f6: "\<forall>s2. snth n (s2) \<le> snth n (add\<cdot>s2\<cdot>s)"
    sorry
  show ?thesis
    apply(subst f31, subst f5)
    by (simp add: f6)
qed  
  
  


    

end