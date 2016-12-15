theory IntroCaseStudy_SPF_MW
imports SPF SPF_CaseStudy
begin

lemma oneComp_cont[simp] : "cont (\<lambda> sb :: nat SB . (sbDom\<cdot>sb = {c2}) \<leadsto> [c1 \<mapsto> \<up>1 \<bullet> (sb . c2)]\<Omega>)"
  apply(rule contSPF)
  apply(rule sb_eq)
   apply(simp add: sbdom_rep_eq sbdom_Lub20)
   apply(subst sbdom_Lub20)
    apply(rule chainI, rule sb_below)
     apply(simp add: sbdom_rep_eq)
    apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
    apply (simp add: monofun_cfun_arg monofun_cfun_fun po_class.chainE)
   apply(simp add: sbdom_rep_eq)
  apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
  apply meson
  apply(simp add: lub_insert)
  apply(subst lub_insert)
   apply(rule chainI, rule sb_below)
    apply(simp add: sbdom_rep_eq)
   apply(simp add: sbgetch_rep_eq)
   apply (rule impI)
   apply (simp add: monofun_cfun_arg monofun_cfun_fun po_class.chainE)
  by(simp add: sbgetch_rep_eq contlub_cfun_arg)

lift_definition OneCompSPF :: "nat SPF" is 
"\<Lambda> sb . (sbDom\<cdot>sb = {c2}) \<leadsto> [c1 \<mapsto> \<up>1 \<bullet> (sb . c2)]\<Omega>"
by(auto simp add: spf_well_def domIff2 sbdom_rep_eq)

end