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
 
  
subsection \<open>Ariane\<close>

  
(* addC *)  
  
definition addC :: "nat SPF" where
"addC \<equiv> SPF2x1 add (c1, c2, c3)" 

lift_definition arianeComponent1 :: "nat SPS" is
  "{addC}"
  by(simp add: sps_well_def) 

(* append0C *)     
    
definition append0C :: "nat SPF" where
"append0C \<equiv> SPF1x1 (appendElem2 0) (c3,c2)"  
  
lift_definition arianeComponent2 :: "nat SPS" is
  "{append0C}"
  by(simp add: sps_well_def)
    
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
    
lift_definition arianeComponent3 :: "nat SPS" is
  "{ Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {}) \<leadsto> ([c5\<mapsto>s]\<Omega>)) | s :: nat stream. #s = \<infinity>}"
  using sps_well_def by fastforce 
    
(* addC2 *) 
    
definition addC2 :: "nat SPF" where
"addC2 \<equiv> SPF2x1 add (c3, c4, c5)" 

lift_definition arianeComponent4 :: "nat SPS" is
  "{addC2}"
  by(simp add: sps_well_def)
 
(* ariane *)  
    
definition ariane :: "nat SPS" where 
  "ariane \<equiv> arianeComponent1 \<Otimes> arianeComponent2 \<Otimes> arianeComponent3 \<Otimes> arianeComponent4"

lift_definition ariane2 :: "nat SPS" is
  "{ Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c5\<mapsto>add\<cdot>(sum4\<cdot>(sb . c1))\<cdot>s]\<Omega>)) | s :: nat stream. #s = \<infinity>}"
  
  sorry


section \<open>Evaluation\<close>
    
    
lemma finalLemma: assumes "f \<in> Rep_SPS ariane" and "sbDom\<cdot>sb = spsDom ariane"
  shows "snth n ((f\<rightleftharpoons>sb) . c6) \<ge> sum_snth n (sb . c1)"
proof - 
  fix n f
  have f0: "\<exists>s. f = (addC \<otimes> append0C \<otimes> (Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {}) \<leadsto> ([c5\<mapsto>(s :: nat stream)]\<Omega>))) \<otimes> addC2) \<and> #s=\<infinity>"
    sorry
  obtain s where f1: "f = (addC \<otimes> append0C \<otimes> (Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {}) \<leadsto> ([c5\<mapsto>(s :: nat stream)]\<Omega>))) \<otimes> addC2)"    
    sorry
  then have f2: "#s = \<infinity>"
    sorry
  
  have f3: "L (addC \<otimes> append0C) (Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {}) \<leadsto> ([c5\<mapsto>(s :: nat stream)]\<Omega>))) = {}"
    sorry
  have f4: "((addC \<otimes> append0C) \<rightleftharpoons> sb) . c3 = sum4\<cdot>(sb . c1)"
    sorry
  
  have f5: "pL (addC \<otimes> append0C \<otimes> (Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = {}) \<leadsto> ([c5\<mapsto>(s :: nat stream)]\<Omega>)))) addC2 = {}"    
    sorry
      
  show ?thesis
    sorry
qed  
  
  


    

end