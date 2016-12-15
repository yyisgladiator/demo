theory ParComp_MW
imports SPF SBTheorie

begin

(* Instantiation nat message *)

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
  fixes sb :: "nat SB" 
  shows "ctype ch1 \<subseteq> ((ctype ch2) :: nat set) \<Longrightarrow> ch1 \<in> sbDom\<cdot>sb \<Longrightarrow> sb_well [ch2 \<mapsto> (sb . ch1)]"
by (smt contra_subsetD dom_empty dom_fun_upd fun_upd_same option.sel option.simps(3) rep_well sb_well_def sbdom_insert sbgetch_insert singletonD subsetI)


lemma spf_id_mono[simp] : "monofun (\<lambda>sb. (sbDom\<cdot>sb = {ch1}) \<leadsto> ([ch2 \<mapsto> id\<cdot>(sb . ch1)]\<Omega>))"
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

lemma spf_id_cont[simp] : "cont (\<lambda>sb. (sbDom\<cdot>sb = {ch1}) \<leadsto> ([ch2 \<mapsto> id\<cdot>(sb . ch1)]\<Omega>))"
apply(rule spf_cont2cont)
apply(rule spf_contlubI)
apply(simp add: domIff2 sbChain_dom_eq2)
apply(rule sb_below)
apply (simp add: sbdom_rep_eq)
apply(simp only: Cfun.contlub_cfun_arg ID_chain_lub)
apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
apply(simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
apply(simp add: contlub_cfun_arg)
apply (simp add: monofun2spf_mono)
apply(simp add: domIff2)
by rule+ 

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

(* Composition prerequirements *)

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

lemma id_apply1: "((Rep_CSPF ID1) \<rightharpoonup> ([c1 \<mapsto> s]\<Omega>)) = ([c2 \<mapsto> (s:: nat stream)]\<Omega>)"
apply(simp add: id_def  Rep_CSPF_def ID1.rep_eq sbdom_rep_eq)
by(simp add: sbgetch_insert)

lemma id_apply2: "((Rep_CSPF ID2) \<rightharpoonup> ([c3 \<mapsto> s]\<Omega>)) = ([c4 \<mapsto> (s:: nat stream)]\<Omega>)"
apply(simp add: id_def Rep_CSPF_def ID2.rep_eq sbdom_rep_eq)
by(simp add: sbgetch_insert)

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

(* Bundles *)

lemma [simp]: "sbDom\<cdot>([c1 \<mapsto> (s::nat stream), c3 \<mapsto> (s2::nat stream)]\<Omega>) = I ID1 ID2"
by(auto simp add: sbdom_rep_eq)

lemma sb_rest: "([c1 \<mapsto> s, c3 \<mapsto> s2]\<Omega>)\<bar>{c1} = [c1 \<mapsto> (s::nat stream)]\<Omega>"
by(simp add: sbrestrict_insert)

(* Parallel Composition*)

(*
definition spfcomp :: "'m SPF => 'm SPF => 'm SPF"  where
"spfcomp f1 f2 \<equiv> 
let I1 = spfDom\<cdot>f1;
    I2 = spfDom\<cdot>f2;
    O1 = spfRan\<cdot>f1; 
    O2 = spfRan\<cdot>f2; 
    I  = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 - (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2);
    Oc = spfRan\<cdot>f1 \<union> spfRan\<cdot>f2 - (spfDom\<cdot>f1 \<union> spfDom\<cdot>f2);
    C  = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2    
in Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I) \<leadsto> \<Squnion>i. iterate i\<cdot>
   (\<Lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> I1)) \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> I2)))\<cdot>(sbLeast C) \<bar> Oc)"

lemma parCompNoIterate: "spfComp2 ID1 ID2 = Abs_CSPF(\<lambda> x. (sbDom\<cdot>x = I ID1 ID2) \<leadsto> ( x \<uplus> ((Rep_CSPF ID1)\<rightharpoonup>(x \<bar> spfDom\<cdot>ID1)) \<uplus> ((Rep_CSPF ID2)\<rightharpoonup>(x \<bar> spfDom\<cdot>ID2)))
                    \<bar> Oc ID1 ID2)"
sorry

lemma parCompNoIterate2:  "(Rep_CSPF (spfComp2 ID1 ID2)) \<rightharpoonup> sb = (\<lambda> x. (sbDom\<cdot>x = I ID1 ID2) \<leadsto> ( x \<uplus> ((Rep_CSPF ID1)\<rightharpoonup>(x \<bar> spfDom\<cdot>ID1)) \<uplus> ((Rep_CSPF ID2)\<rightharpoonup>(x \<bar> spfDom\<cdot>ID2)))
                    \<bar> Oc ID1 ID2) \<rightharpoonup> sb"
sorry*)
(* spfCompHelp2 *)

definition spfCompHelp2 :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SB \<Rightarrow> 'm SB \<rightarrow> 'm SB" where
"spfCompHelp2 f1 f2 x \<equiv> (\<Lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> spfDom\<cdot>f2)))"

lemma spfCompHFun_mono[simp]: "monofun (\<lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> spfDom\<cdot>f2)))"
using cont2mono spfCompHelp_cont  by blast

lemma spfCompHFun_cont[simp]: "cont (\<lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> spfDom\<cdot>f2)))"
using spfCompHelp_cont by blast

lemma test3 [simp]: "cont (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)"
sorry

lemma test4 [simp]: "spf_well (Abs_cfun (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2))"
sorry

lemma spfCompH2_dom [simp]: assumes "sbDom\<cdot>sb = C f1 f2"
  shows "sbDom\<cdot>((spfCompHelp2 f1 f2 x)\<cdot>sb) = (sbDom\<cdot>x \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
  apply (simp add: spfCompHelp2_def)
  proof -
    have f1: "spfDom\<cdot>f1 \<subseteq> sbDom\<cdot>sb"
      by (simp add: C_def Un_commute Un_left_commute assms)
    have "spfDom\<cdot>f2 \<subseteq> sbDom\<cdot>sb"
      using C_def assms by auto
    then show "sbDom\<cdot>x \<union> (sbDom\<cdot>Rep_CSPF f1\<rightharpoonup>(sb\<bar>spfDom\<cdot>f1)) \<union> (sbDom\<cdot>Rep_CSPF f2\<rightharpoonup>(sb\<bar>spfDom\<cdot>f2)) = (sbDom\<cdot>x \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
      using f1 by simp
  qed

(* Chain and iterate*)

lemma spfComp_parallel : assumes "L f1 f2 = {}" 
                       and "sbDom\<cdot>x = I f1 f2" 
                       and "spfComp_well f1 f2"
  shows "(iterate (Suc (Suc i))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
                  = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2 \<rightharpoonup> (x\<bar>spfDom\<cdot>f1)))" (is "?L = ?R")
sorry

lemma spfComp_parallelnf_chain: assumes "L f1 f2 = {}"
                              and "sbDom\<cdot>x = I f1 f2"
                              and "spfComp_well f1 f2"
  shows "chain (\<lambda>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"
apply(rule sbIterate_chain)
apply (simp add: assms C_def I_def)
by blast

lemma spfComp_parallel_max: assumes "L f1 f2 = {}"
                          and "sbDom\<cdot>x = I f1 f2" 
                          and "spfComp_well f1 f2"
  shows "max_in_chain 2 (\<lambda>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"
apply(rule max_in_chainI, subst Num.numeral_2_eq_2)
apply(subst spfComp_parallel)
apply(simp_all add: assms)
by (smt One_nat_def Suc_1 Suc_le_D Suc_le_lessD assms(1) assms(2) assms(3) le_simps(2) spfComp_parallel)

lemma spfComp_parallel_itconst1 [simp]: assumes "L f1 f2 = {}" 
                                      and "sbDom\<cdot>x = I f1 f2" 
                                      and "spfComp_well f1 f2"
  shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
               = iterate 2\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))"
  using assms(1) assms(2) assms(3) maxinch_is_thelub spfComp_parallel_max spfComp_parallelnf_chain by blast

lemma spfComp_parallel_itconst2 [simp]: assumes "L f1 f2 = {}" 
                                      and "sbDom\<cdot>x = I f1 f2" 
                                      and "spfComp_well f1 f2"
  shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
            = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2)\<rightharpoonup>((Rep_CSPF f1) \<rightharpoonup> (x\<bar>spfDom\<cdot>f1)))"
by (metis One_nat_def Suc_1 assms(1) assms(2) assms(3) spfComp_parallel spfComp_parallel_itconst1)

(* Parallel Comp  *)

lemma spfcomp_tospfH2: "(spfcomp f1 f2) 
                   = Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> 
                      (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2)"
sorry

lemma spfCompParallelGetch: assumes "L f1 f2 = {}"
                            and "sbDom\<cdot>sb = I f1 f2"
                            and "spfComp_well f1 f2"
                            and "c \<in> spfRan\<cdot>f1" 
  shows "(Rep_CSPF(spfcomp f1 f2) \<rightharpoonup> sb) . c = (Rep_CSPF(f1) \<rightharpoonup> (sb\<bar>spfDom\<cdot>f1)) . c"
apply(simp add: spfComp_parallel)
sledgehammer
sorry

lemma spfParCompID: "(Rep_CSPF (spfcomp ID1 ID2)) \<rightharpoonup> ([c1 \<mapsto> s, c3 \<mapsto> s2]\<Omega>) . c2 = s"
apply(simp add: spfCompParallelGetch)
apply(simp add: id_apply1 sb_rest)
by(simp add: sbGetCh_def)

end