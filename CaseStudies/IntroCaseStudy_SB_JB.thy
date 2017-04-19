theory IntroCaseStudy_SB_JB
imports SBTheorie TSBTheorie  StreamTheorie SPF StreamTheorie StreamCase_Study SPF_CaseStudy
begin


lift_definition streamBundle1 :: "nat SB" is "([c1\<mapsto><[1,2]>, c2\<mapsto><[3,4]>])"
by (simp add: sb_well_def)

lift_definition timedstreamBundle1 :: "nat TSB" is "([c1\<mapsto>tsInfTick, c2\<mapsto>tsInfTick])"
by (simp add: tsb_well_def) 

lemma constComp_cont : "cont (\<lambda> sb :: nat SB . (sbDom\<cdot>sb = {c2}) \<leadsto> [c1 \<mapsto> x \<bullet> (sb . c2)]\<Omega>)"
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

lift_definition a12Comp :: "nat SPF" is 
"\<Lambda> sb . (sbDom\<cdot>sb = {c2}) \<leadsto> [c1 \<mapsto> <[1,2]> \<bullet> (sb . c2)]\<Omega>"
apply(simp add: spf_well_def constComp_cont domIff2 sbdom_rep_eq)
by(auto)


end
