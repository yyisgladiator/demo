theory SPS_CaseStudy_MW
imports Feedback_MW SPF_MW SPF_Templates
  
begin

lemma [simp]: "spfDom\<cdot>(addSPF (c1,c2,c3)) = {c1, c2}"
  using addC_def by auto

lemma [simp]: "spfRan\<cdot>(addSPF (c1,c2,c3)) = {c3}"
  using addC_def by auto
  
lift_definition arianeComp1 :: "nat SPS" is
  "{addSPF (c1,c2,c3)}"
  by(simp add: sps_well_def)

lemma [simp]: "spfDom\<cdot>(appendSPF (c3,c2) 0) = {c3}"
  sorry

lemma [simp]: "spfRan\<cdot>(appendSPF (c3,c2) 0) = {c2}"
  sorry
    
lift_definition arianeComp2 :: "nat SPS" is
  "{appendSPF (c3,c2) 0}"
  by(simp add: sps_well_def)

lift_definition arianeComp3 :: "nat SPS" is
  "{addSPF (c3,c4,c5)}"
  by(simp add: sps_well_def)
    
lemma [simp]: "\<forall>f. (\<exists>s. f = Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {c5}) \<leadsto> ([c4\<mapsto>s :: nat stream]\<Omega>)) \<and> #s = \<infinity>) \<longrightarrow> spfDom\<cdot>(f) = {c5}"
  sorry

lemma [simp]: "\<forall>f. (\<exists>s. f = Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {c5}) \<leadsto> ([c4\<mapsto>s :: nat stream]\<Omega>)) \<and> #s = \<infinity>) \<longrightarrow> spfRan\<cdot>(f) = {c4}"
  sorry
    
lift_definition arianeComp4 :: "nat SPS" is
  "{ Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {c5}) \<leadsto> ([c4\<mapsto>s]\<Omega>)) | s :: nat stream. #s = \<infinity>}"
  by(simp add: sps_well_def)
   
lift_definition ariane :: "nat SPS" is "arianeComp1 \<Otimes> arianeComp2 \<Otimes> arianeComp3 \<Otimes> arianeComp4"
  sorry  

lemma final: assumes "f \<in> Rep_SPS ariane" and "sbDom\<cdot>sb = spsDom ariane"
  shows "snth n ((f\<rightleftharpoons>sb).c4) \<ge> sum_snth n (sb . c1)"
  sorry
  
  
  
lemma [simp]: "\<forall>f. (\<exists>s. f = Abs_CSPF (\<lambda>sb. (sbDom\<cdot>sb = {c1})\<leadsto>[c5 \<mapsto> add\<cdot>(sum3\<cdot>(sb . c1))\<cdot>s]\<Omega>) \<and> #s = \<infinity>) \<longrightarrow> spfDom\<cdot>f = {c1}"
  sorry
    
lemma [simp]: "\<forall>f. (\<exists>s. f = Abs_CSPF (\<lambda>sb. (sbDom\<cdot>sb = {c1})\<leadsto>[c5 \<mapsto> add\<cdot>(sum3\<cdot>(sb . c1))\<cdot>s]\<Omega>) \<and> #s = \<infinity>) \<longrightarrow> spfRan\<cdot>f = {c5}"
  sorry
  
lift_definition ariane2 :: "nat SPS" is
  "{ Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c5\<mapsto>add\<cdot>(sum3\<cdot>(sb . c1))\<cdot>s]\<Omega>)) | s :: nat stream. #s = \<infinity>}"
  by(simp add: sps_well_def)

lemma arianeEq: "ariane \<equiv> ariane2"
  sorry
  
(*
definition sumAriane :: "nat SPF" where
"sumAriane \<equiv> sum1SPF"

definition addAriane :: "nat stream  \<Rightarrow> nat SPF" where
"addAriane a \<equiv> Abs_CSPF (\<lambda> (sb::nat SB). (sbDom\<cdot>sb = {c3}) \<leadsto> ([c4 \<mapsto> (sb . c3) + a]\<Omega>))" (*((\<up>a)\<infinity>)]\<Omega>))"*)

lemma spfCompArianeDom: "spfDom\<cdot>(sumAriane \<otimes> (addAriane a)) = {c1}"
  sorry

lemma spfCompArianeRan: "spfRan\<cdot>(sumAriane \<otimes> (addAriane a)) = {c4}"
  sorry

lift_definition ariane :: "nat SPS" is "{ (sumAriane \<otimes> (addAriane a)) | a :: nat stream. True } " (*a \<in> \<nat> }"*)
  apply(simp add: sps_well_def)
  by (metis spfCompArianeDom spfCompArianeRan)
    
lemma spsDomAriane: "spsDom ariane = {c1}"
  apply(simp add: spsDom_def ariane.rep_eq)
    by (smt Nats_0 someI_ex spfCompArianeDom sumAriane_def)
  
lemma spsRanAriane: "spsRan ariane = {c4}"
  apply(simp add: spsRan_def ariane.rep_eq)
  by (smt Nats_0 someI_ex spfCompArianeRan sumAriane_def)
      
lemma test: "(sumAriane \<otimes> (addAriane ((\<up>0)\<infinity>))) \<in> Rep_SPS ariane"
  using Nats_0 ariane.rep_eq by blast
 
lemma final: assumes "f \<in> Rep_SPS ariane" and "sbDom\<cdot>sb = spsDom ariane"
  shows "snth n ((f\<rightleftharpoons>sb).c4) \<ge> snth n (sum4\<cdot>(sb . c1))"
sorry
    
(* alternative definition with spsComp *)    

lift_definition arianeHelper1 :: "nat SPS" is "{ sumAriane }"  
  using sps_well_def by fastforce
  
lift_definition arianeHelper2 :: "nat SPS" is "{ (addAriane a) | a :: nat stream. True }"  (*a \<in> \<nat> }"*)
  sorry
  
lift_definition ariane2 :: "nat SPS" is "arianeHelper1 \<Otimes> arianeHelper2"
  sorry

lemma [simp]: "Rep_SPS (Abs_SPS {sumAriane}) = {sumAriane}"
  using arianeHelper1.rep_eq arianeHelper1_def by auto
    
lemma [simp]: "Rep_SPS (Abs_SPS { (addAriane a) | a :: nat stream. True }) = { (addAriane a) | a :: nat stream. True }"
  using arianeHelper2.rep_eq arianeHelper2_def by auto
    
lemma arianeEq: "ariane \<equiv> ariane2"    
  apply(simp add: ariane_def ariane2_def spsComp_def)
  apply(simp add: arianeHelper1_def arianeHelper2_def)
  by (smt Collect_cong Rep_SPS_inverse arianeHelper2.rep_eq mem_Collect_eq sumAriane_def)
  *)
end