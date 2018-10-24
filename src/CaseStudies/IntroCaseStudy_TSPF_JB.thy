theory IntroCaseStudy_TSPF_JB
imports  "../TSPF"  "../SPF" TSPFCaseStudy
begin

lemma tsInfTick_tsbi_well[simp]:
 fixes x :: "'a TSB_inf" 
 shows "tsb_inf_well [c2 \<mapsto> tsInfTick]"
by(simp add: tsb_inf_well_def)

lemma tsInfTick_ran: assumes "b \<in> (\<lambda>tb::'a TSB_inf. (Abs_TSB_inf [c2 \<mapsto>tsInfTick])) ` TSBi {c1}"
  shows "tsbiDom\<cdot>b = {c2}"
by (metis Abs_TSB_inf_inverse assms dom_empty dom_fun_upd imageE mem_Collect_eq option.simps(3) tsInfTick_tsbi_well tsbidom_insert)

lemma tsInfTick_type: "tspf_type (\<lambda>tb. ((tsbiDom\<cdot>tb = {c1}) \<leadsto> (Abs_TSB_inf [c2 \<mapsto>tsInfTick])))"
apply(simp add: tspf_type_def, rule)
apply(simp add: domIff2)
apply auto[1]
by(simp add: part_ran2 tsInfTick_ran)

lemma tsInfTick_strong: "tspf_strongCausality (\<lambda>tb. ((tsbiDom\<cdot>tb = {c1}) \<leadsto> (Abs_TSB_inf [c2 \<mapsto>tsInfTick])))"
apply(rule tspf_strongCausalityI)
by(simp add: domIff2)




lift_definition tspfun:: "nat TSPF" is "\<lambda>tb. ((tsbiDom\<cdot>tb = {c1}) \<leadsto> (Abs_TSB_inf [c2 \<mapsto>tsInfTick]))" 
apply(simp add: tspf_well_def)
by(simp add: tsInfTick_type tsInfTick_strong)

lift_definition tspfunw:: "nat TSPFw" is "\<lambda>tb. ((tsbiDom\<cdot>tb = {c1}) \<leadsto> (Abs_TSB_inf [c2 \<mapsto>tsInfTick]))" 
apply(simp add: tspfw_well_def)
by(simp add: tsInfTick_type tspf_StrongImpWeak tsInfTick_strong)

end
