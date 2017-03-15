theory SPS_CaseStudy_MW
imports Feedback_MW SPF_MW SPF_Templates
  
begin

definition sumAriane :: "nat SPF" where
"sumAriane \<equiv> sum1SPF"

definition addAriane :: "nat \<Rightarrow> nat SPF" where
"addAriane a \<equiv> Abs_CSPF (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {c3}) \<leadsto> ([c4 \<mapsto> (sb . c3) + ((\<up>a)\<infinity>)]\<Omega>))"

lemma spfCompArianeDom: "spfDom\<cdot>(sumAriane \<otimes> (addAriane a)) = {c1}"
  sorry

lemma spfCompArianeRan: "spfRan\<cdot>(sumAriane \<otimes> (addAriane a)) = {c4}"
  sorry

lift_definition ariane :: "nat SPS" is "{ (sumAriane \<otimes> (addAriane a)) | a. a \<in> \<nat> }"
  apply(simp add: sps_well_def)
  by (metis spfCompArianeDom spfCompArianeRan)
    
lemma spsDomAriane: "spsDom ariane = {c1}"
  apply(simp add: spsDom_def ariane.rep_eq)
    by (smt Nats_0 someI_ex spfCompArianeDom sumAriane_def)
  
lemma spsRanAriane: "spsRan ariane = {c4}"
  apply(simp add: spsRan_def ariane.rep_eq)
  by (smt Nats_0 someI_ex spfCompArianeRan sumAriane_def)
      
lemma test: "(sumAriane \<otimes> (addAriane 0)) \<in> Rep_SPS ariane"
  using Nats_0 ariane.rep_eq by blast
 
lemma final: assumes "f \<in> Rep_SPS ariane" and "sbDom\<cdot>sb = spsDom ariane"
  shows "snth n ((f\<rightleftharpoons>sb).c4) \<ge> snth n (sum4\<cdot>(sb . c1))"
sorry
    
(* alternative definition with spsComp *)    

lift_definition arianeHelper1 :: "nat SPS" is "{ sumAriane }"  
  using sps_well_def by fastforce
  
lift_definition arianeHelper2 :: "nat SPS" is "{ (addAriane a) | a. a \<in> \<nat> }"
  sorry
  
lift_definition ariane2 :: "nat SPS" is "arianeHelper1 \<Otimes> arianeHelper2"
  sorry

lemma [simp]: "Rep_SPS (Abs_SPS {sumAriane}) = {sumAriane}"
  using arianeHelper1.rep_eq arianeHelper1_def by auto
    
lemma [simp]: "Rep_SPS (Abs_SPS {addAriane a |a. a \<in> \<nat>}) = {addAriane a |a. a \<in> \<nat>}"
  using arianeHelper2.rep_eq arianeHelper2_def by auto
    
lemma arianeEq: "ariane \<equiv> ariane2"    
  apply(simp add: ariane_def ariane2_def spsComp_def)
  apply(simp add: arianeHelper1_def arianeHelper2_def)
  by (smt Collect_cong)
  
end