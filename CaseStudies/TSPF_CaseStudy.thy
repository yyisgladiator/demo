
theory TSPF_CaseStudy
imports  "../TSPF"
begin

section \<open>Empty TSPF\<close>
(* TSPF with empty input and output *)  
  
lemma tspfEmpty_cont[simp]: "cont (\<lambda> x. (tsbDom\<cdot>x = {} ) \<leadsto> (empty \<Omega>))"
  by simp 
    
lemma tspfEmpty_cont2[simp]: "cont (\<lambda> x. (tsbDom\<cdot>x = {c1} ) \<leadsto> (empty \<Omega>))"
  by simp 

declare[[show_types]]
lift_definition tspfEmpty :: "'m TSPF"  is
"(\<Lambda> x. (tsbDom\<cdot>x = {} ) \<leadsto> (empty \<Omega>))"
proof - 
  have f0: "\<forall>tb. tsbDom\<cdot>(tb :: 'm TSB) = {} \<longrightarrow> Rep_TSB tb = empty"
    by (simp add: tsbdom_insert)
  then have f1: "dom (\<lambda> x. (tsbDom\<cdot>x = {}) \<leadsto> (empty \<Omega>)) = {(empty \<Omega>)}"
    apply(simp add: dom_def)
    by (smt Collect_cong bot_empty_eq bot_set_def dom_empty empty_iff insert_Collect tsb_eq tsb_well_exists tsbdom_rep_eq)
  moreover have f2: "{a::'a TSB. tsbDom\<cdot>a = {}} = {empty \<Omega>}"
    by (smt Abs_cfun_inverse2 Collect_cong bot_apply bot_set_def dom_empty insert_Collect insert_not_empty mem_Collect_eq tsbDom_def tsb_eq tsb_well_exists tsbdom_cont tsbdom_rep_eq)
  moreover have f3: "dom (Rep_cfun (\<Lambda> x. (tsbDom\<cdot>x = {}) \<leadsto> (empty \<Omega>))) = {(empty \<Omega>)}"
    apply(simp add: dom_def)
    using f2 by auto
  ultimately show ?thesis  
    apply(simp add: tspf_well_def)
    apply rule
    apply (auto simp add: tspf_type_def domIff2 tsbdom_rep_eq)
    apply(simp add: tsbTickCount_def)
      by blast
qed

lift_definition tspfEmpty2 :: "'m TSPF"  is
"(\<Lambda> x. (tsbDom\<cdot>x = {c1} ) \<leadsto> (empty \<Omega>))"
proof - 
  have f0: "tsbDom\<cdot>(tb :: 'm TSB) = {} \<Longrightarrow> Rep_TSB tb = empty"
    by (simp add: tsbdom_insert)
  then have f1: "dom (\<lambda> x. (tsbDom\<cdot>x = {c1}) \<leadsto> (empty \<Omega>)) = TSB {c1}"
    apply(simp only: dom_def TSB_def)
      by simp
  moreover have f2: "dom (Rep_cfun (\<Lambda> x. (tsbDom\<cdot>x = {c1}) \<leadsto> (empty \<Omega>))) = TSB {c1}"
    apply (simp only: dom_def TSB_def)
    by simp
  moreover have f3: "tsbDom\<cdot>(empty \<Omega>) = {}"
    by (simp add: tsbdom_rep_eq)
  moreover have f4: "\<forall>b. tsbDom\<cdot>(b :: 'm TSB) \<noteq> {c1} \<longrightarrow> b \<in> TSB {c1} = False"
    by auto
  ultimately show ?thesis  
    apply(simp add: tspf_well_def)
    apply rule
     apply(simp add: tspf_type_def)
     apply (smt domIff f1 tsb_tsbleast)
    apply(simp add: f1)
    by(simp add: tsbTickCount_def f3)
qed
  
lift_definition tspfEmpty3 :: "'m TSPF"  is
"(\<Lambda> x. None)"
proof - 
  have f1: "dom (\<lambda> x. None) = {}"
    by(simp add: dom_def)
  moreover then have f2: "dom (Rep_cfun (Abs_cfun Map.empty)) = {}"
    by simp
  ultimately show ?thesis  
    apply(simp add: tspf_well_def)
    apply(simp only: tspf_type_def)
     apply(simp add: f2) (* not true *)
    sorry
qed

end
