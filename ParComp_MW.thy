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

lemma id_chain[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Y 0) = {ch1} \<Longrightarrow> chain (\<lambda> i. [ch2 \<mapsto> id\<cdot>(Y i . ch1)]\<Omega>)"
apply(rule chainI)
apply(rule sb_below)
apply (simp add: sbdom_rep_eq)
apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
by (simp add: monofun_cfun po_class.chainE)

lemma id_chain_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow> chain (\<lambda> i. [ch2 \<mapsto> id\<cdot>((Y i) . ch1)]\<Omega>)"
by (simp  add: sbChain_dom_eq2)

lemma spf_id_chain[simp]: "chain Y \<Longrightarrow> chain(\<lambda> i. (sbDom\<cdot>(Y i) = {ch1}) \<leadsto> ([ch2 \<mapsto> id\<cdot>((Y i) . ch1)]\<Omega>))"
apply(rule chainI)
apply (simp add: sbChain_dom_eq2)
apply(rule impI, rule some_below, rule sb_below)
apply (simp add: sbdom_insert)
apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
by (simp add: monofun_cfun po_class.chainE)

lemma spf_id_lub[simp]: "chain Y \<Longrightarrow> sbDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow> (\<Squnion>i. id\<cdot>(Y i . c1)) = id\<cdot>((Lub Y) . c1)"
by (simp add: contlub_cfun_arg contlub_cfun_fun)

lemma spf_id_cont[simp] : "cont (\<lambda>sb. (sbDom\<cdot>sb = {ch1}) \<leadsto> ([ch2 \<mapsto> id\<cdot>(sb . ch1)]\<Omega>))"
apply(rule spf_cont2cont)
apply(rule spf_contlubI)
apply(simp add: domIff2 sbChain_dom_eq2)
apply(rule sb_below)
apply (simp add: sbdom_rep_eq)
apply(simp only: Cfun.contlub_cfun_arg id_chain_lub)
apply(simp add: sbdom_rep_eq sbgetch_rep_eq)
apply(simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
apply(simp add: contlub_cfun_arg)
apply (simp add: monofun2spf_mono)
apply(simp add: domIff2)
by rule+ 

(* IDs *)

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

(* Helper Function  *)

definition spfCompHelp2 :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SB \<Rightarrow> 'm SB  \<rightarrow> 'm SB" where
"spfCompHelp2 f1 f2 x \<equiv> (\<Lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> spfDom\<cdot>f1)) 
                                 \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> spfDom\<cdot>f2)))"

lemma spfcomp_tospfH2: "(spfcomp f1 f2) = Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> 
                        (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2)"
apply (subst spfcomp_def, subst spfCompHelp2_def, subst C_def, subst I_def, subst Oc_def)
by (simp)

    (*TODO*)
lemma spfCom_dom: "sbDom\<cdot>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) = C f1 f2"
sorry

    (*TODO*)
lemma spfComp_mono[simp]: assumes "spfComp_well f1 f2"
shows "monofun (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)"
sorry

    (*TODO*)
lemma spfComp_cont [simp]: assumes "spfComp_well f1 f2"
shows "cont (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)"
sorry

lemma spfComp_well2 [simp]: assumes "spfComp_well f1 f2"
shows "spf_well (Abs_cfun (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>
                               (spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2))"
by(auto simp add: spf_well_def domIff2 sbdom_rep_eq spfCom_dom assms)

lemma spfcomp_repAbs: assumes "spfComp_well f1 f2" shows
 "Rep_CSPF (Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2))
            = (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)"
by (simp add: assms)

(* Parallel Composition general *)

lemma [simp]: assumes "c \<in> spfRan\<cdot>f1"
  shows "c \<notin> I f1 f2"
by (simp add: I_def assms(1))

lemma [simp]: assumes "L f1 f2 = {}"
  shows "spfDom\<cdot>f1 \<subseteq> I f1 f2"
apply(auto simp add: I_def)
using L_def assms apply fastforce
using L_def assms by fastforce

lemma[simp]: assumes "L f1 f2 = {}" 
  shows "I f1 f2 = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2"
by (metis Diff_triv I_def L_def assms)

lemma sbunion_getchM: assumes "c \<notin> sbDom\<cdot>b1"
                          and "c \<notin> sbDom\<cdot>b3"
  shows "b1\<uplus>b2\<uplus>b3 . c = b2 . c"
by (metis assms(1) assms(2) domIff sbdom_insert sbgetch_insert sbunion_getchL sbunion_getchR)

lemma spfComp_cInOc:  assumes "L f1 f2 = {}" 
                          and "spfComp_well f1 f2"
                          and "c \<in> spfRan\<cdot>f1" 
  shows "c \<in> Oc f1 f2"
using L_def Oc_def assms(1) assms(3) by fastforce

(* Parallel Composition *)

    (*TODO*)
lemma spfComp_parallel_itconst: assumes "L f1 f2 = {}" 
                                    and "sbDom\<cdot>x = I f1 f2" 
                                    and "spfComp_well f1 f2"
  shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
            = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2))"
sorry

(* Final lemma *)

lemma spfCompParallelGetch: assumes "L f1 f2 = {}"
                                and "sbDom\<cdot>sb = I f1 f2"
                                and "spfComp_well f1 f2"
                                and "c \<in> spfRan\<cdot>f1" 
  shows "(Rep_CSPF(spfcomp f1 f2) \<rightharpoonup> sb) . c = (Rep_CSPF(f1) \<rightharpoonup> (sb\<bar>spfDom\<cdot>f1)) . c"
apply(simp add: spfcomp_tospfH2)
apply(simp only: spfcomp_repAbs assms, simp_all)
apply(simp only: spfComp_parallel_itconst assms)
apply(simp_all add: spfComp_cInOc assms)
apply(subst sbunion_getchM, simp_all)
apply(simp_all add: assms)
apply(metis L_def UnCI assms(1) assms(4) disjoint_iff_not_equal)
by (meson assms(3) assms(4) disjoint_iff_not_equal spfComp_well_def)

lemma spfParCompID: "(Rep_CSPF (spfcomp ID1 ID2)) \<rightharpoonup> ([c1 \<mapsto> s, c3 \<mapsto> s2]\<Omega>) . c2 = s"
apply(simp add: spfCompParallelGetch)
apply(simp add: id_apply1 sb_rest)
by(simp add: sbGetCh_def)

end