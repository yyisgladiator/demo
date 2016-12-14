theory IntroCaseStudy_TSPS_JB
imports TSPSTheorie TSPFCaseStudy IntroCaseStudy_TSPF_JB

begin

lift_definition tspsJB ::"nat TSPS" is "{tspfun, delayTspf}"
apply(simp add: tsps_well_def)
by (smt cr_TSPF_def domD dom_empty dom_fun_upd option.sel option.simps(3) tsInfTick_tsbi_well tsbidom_dom tsbidom_rep_eq tspfdom2ran tspfdom_insert tspfun.abs_eq tspfun.transfer)

end
