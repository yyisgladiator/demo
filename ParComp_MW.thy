theory ParComp_MW
imports SPF SBTheorie

begin

(* instantiation nat message *)

instantiation nat :: message
begin
  definition ctype_nat :: "channel \<Rightarrow> nat set" where
  "ctype c = range nat"

instance ..
end

lemma [simp]: "cs \<subseteq> ((ctype c) :: nat set)"
apply(simp add: ctype_nat_def)
by(metis subset_UNIV subset_image_iff transfer_int_nat_set_return_embed)

(* Definition of ID SPFs *)

definition id :: "nat stream \<rightarrow> nat stream" where
"id \<equiv> \<Lambda> x . x"

lemma spf_id_well[simp]:
  fixes sb :: "'a SB" 
  shows "ctype ch1 \<subseteq> ((ctype ch2) :: 'a set) \<Longrightarrow> ch1 \<in> sbDom\<cdot>sb \<Longrightarrow> sb_well [ch2 \<mapsto> (sb . ch1)]"
by (smt contra_subsetD dom_empty dom_fun_upd fun_upd_same option.sel option.simps(3) rep_well sb_well_def sbdom_insert sbgetch_insert singletonD subsetI)

lemma spf_id_mono[simp] : assumes "ctype ch1 \<subseteq> (ctype ch2)"
shows "monofun (\<lambda>sb. (sbDom\<cdot>sb = {ch1}) \<leadsto> ([ch2 \<mapsto> id\<cdot>(sb . ch1)]\<Omega>))"
apply(rule spf_mono2monofun)
apply(rule spf_monoI)
apply(simp add: domIff2)
apply(rule sb_below)
apply(simp add: sbdom_insert)
apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
apply(meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)
apply rule
by(simp add: domIff2)

lemma ID_chain[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {ch1} \<Longrightarrow> chain (\<lambda> i. [ch2 \<mapsto> id\<cdot>(Y i . ch1)]\<Omega>)"
apply(rule chainI)
apply(rule sb_below)
apply (simp add: sbdom_rep_eq)
apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
by (simp add: monofun_cfun po_class.chainE)

lemma ID_chain_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow> chain (\<lambda> i. [ch2 \<mapsto> id\<cdot>((Y i) . ch1)]\<Omega>)"
by (simp  add: sbChain_dom_eq2)

lemma spfID_chain[simp]: "chain Y \<Longrightarrow> chain(\<lambda> i. (sbDom\<cdot>(Y i) = {ch1}) \<leadsto> ([ch2 \<mapsto> id\<cdot>((Y i) . ch1)]\<Omega>))"
apply(rule chainI)
apply (simp add: sbChain_dom_eq2)
apply(rule impI, rule some_below, rule sb_below)
apply (simp add: sbdom_insert)
apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
by (simp add: monofun_cfun po_class.chainE)

lemma spfID_Lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow> (\<Squnion>i. id\<cdot>(Y i . c1)) = id\<cdot>((Lub Y) . c1)"
by (simp add: contlub_cfun_arg contlub_cfun_fun)

lemma spf_id_cont[simp] : assumes "ctype ch1 \<subseteq> (ctype ch2)"
shows "cont (\<lambda>sb. (sbDom\<cdot>sb = {ch1}) \<leadsto> ([ch2 \<mapsto> id\<cdot>(sb . ch1)]\<Omega>))"
apply(rule spf_cont2cont)
apply(rule spf_contlubI)
apply(simp add: domIff2 sbChain_dom_eq2)
apply(rule sb_below)
apply (simp add: sbdom_rep_eq)
apply(simp only: Cfun.contlub_cfun_arg ID_chain_lub)
apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
apply(simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
apply(simp add: contlub_cfun_arg)
sorry

lemma spf_id_ctype12[simp] : "ctype c1 \<subseteq> ctype c2"
sorry

lemma spf_id_ctype34[simp] : "ctype c3 \<subseteq> ctype c4"
sorry

lift_definition ID1 :: "nat SPF" is 
"\<Lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2 \<mapsto> id\<cdot>(sb . c1)]\<Omega>)"
by(auto simp add: spf_well_def domIff2 sbdom_rep_eq)

lift_definition ID2 :: "nat SPF" is 
"\<Lambda> sb. (sbDom\<cdot>sb = {c3}) \<leadsto> ([c4 \<mapsto> id\<cdot>(sb . c3)]\<Omega>)"
by(auto simp add: spf_well_def domIff2 sbdom_rep_eq)

lemma ID1_rep_eqC: "Rep_CSPF ID1 = (\<lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2 \<mapsto> id\<cdot>(sb . c1)]\<Omega>))"
  by(simp add: ID1.rep_eq Rep_CSPF_def)

lemma ID2_rep_eqC: "Rep_CSPF ID2 = (\<lambda> sb. (sbDom\<cdot>sb = {c3}) \<leadsto> ([c4 \<mapsto> id\<cdot>(sb . c3)]\<Omega>))"
  by(simp add: ID2.rep_eq Rep_CSPF_def)

(* Composition *)

lemma [simp]: "spfDom\<cdot>ID1 = {c1}"
apply(simp add: spfdom_insert ID1.rep_eq Rep_CSPF_def)
apply(simp add: domIff2)
by (meson sbleast_sbdom someI)

lemma [simp]: "spfRan\<cdot>ID1 = {c2}"
apply(simp add: spfran_least ID1_rep_eqC)
by(simp add: sbdom_insert)

lemma [simp]: "spfDom\<cdot>ID2 = {c3}"
apply(simp add: spfdom_insert ID2.rep_eq Rep_CSPF_def)
apply(simp add: domIff2)
by (meson sbleast_sbdom someI)

lemma [simp]: "spfRan\<cdot>ID2 = {c4}"
apply(simp add: spfran_least ID2_rep_eqC)
by(simp add: sbdom_insert)

lemma id_apply1: "(Rep_CSPF ID1) \<rightharpoonup> ([c1 \<mapsto> s]\<Omega>) . c2 = s"
sorry

lemma id_apply2: "(Rep_CSPF ID2) \<rightharpoonup> ([c3 \<mapsto> s]\<Omega>) . c4 = s"
sorry

lemma [simp]: "spfComp_well ID1 ID2"
by (simp add: spfComp_well_def)

lemma [simp]: "C ID1 ID2 = {c1,c2,c3,c4}"
by (auto simp add: C_def)

lemma [simp]: "L ID1 ID2 = {}"
by (auto simp add: L_def)

lemma [simp]: "Oc ID1 ID2 = {c2, c4}"
by (auto simp add: Oc_def)

lemma [simp]: "I ID1 ID2 = {c1, c3}"
by (auto simp add: I_def)

lemma [simp]: "sbDom\<cdot>([c1 \<mapsto> s, c3 \<mapsto> s2]\<Omega>) = I ID1 ID2"
sorry

lemma sb_rest: "([c1 \<mapsto> s, c3 \<mapsto> s2]\<Omega>)\<bar>{c1} = [c1 \<mapsto> s]\<Omega>"
sorry

lemma parCompNoIterate: "spfComp2 ID1 ID2 = Abs_CSPF(\<lambda> x. (sbDom\<cdot>x = I ID1 ID2) \<leadsto> ( x \<uplus> ((Rep_CSPF ID1)\<rightharpoonup>(x \<bar> spfDom\<cdot>ID1)) \<uplus> ((Rep_CSPF ID2)\<rightharpoonup>(x \<bar> spfDom\<cdot>ID2)))
                    \<bar> Oc ID1 ID2)"
sorry

lemma parCompNoIterate2:  "(Rep_CSPF (spfComp2 ID1 ID2)) \<rightharpoonup> sb = (\<lambda> x. (sbDom\<cdot>x = I ID1 ID2) \<leadsto> ( x \<uplus> ((Rep_CSPF ID1)\<rightharpoonup>(x \<bar> spfDom\<cdot>ID1)) \<uplus> ((Rep_CSPF ID2)\<rightharpoonup>(x \<bar> spfDom\<cdot>ID2)))
                    \<bar> Oc ID1 ID2) \<rightharpoonup> sb"
sorry

lemma spfCompParallelGetch: assumes "L f1 f2 = {}"
        and "sbDom\<cdot>sb = spfCompIn f1 f2"
        and "spfComp_well f1 f2"
        and "c\<in>spfRan\<cdot>f1"
        shows "Rep_CSPF(spfComp2 f1 f2) \<rightharpoonup> sb . c = Rep_CSPF(f1) \<rightharpoonup> (sb\<bar>spfDom\<cdot>f1) . c"
sorry

lemma spfParCompID: "(Rep_CSPF (spfComp2 ID1 ID2)) \<rightharpoonup> ([c1 \<mapsto> s, c3 \<mapsto> s2]\<Omega>) . c2 = s"
apply(simp add: spfCompParallelGetch)
apply(simp add: id_apply1 sb_rest)
done

end