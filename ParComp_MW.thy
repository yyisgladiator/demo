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
lemma spfComp_dom: "sbDom\<cdot>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) = C f1 f2"
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
by(auto simp add: spf_well_def domIff2 sbdom_rep_eq spfComp_dom assms)

lemma spfcomp_repAbs: assumes "spfComp_well f1 f2" shows
 "Rep_CSPF (Abs_CSPF (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2))
            = (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)"
by (simp add: assms)

lemma spfCompH2_dom [simp]: assumes "sbDom\<cdot>sb = C f1 f2"
  shows "sbDom\<cdot>((spfCompHelp2 f1 f2 x)\<cdot>sb) = (sbDom\<cdot>x \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
  apply (simp add: spfCompHelp2_def)
  proof -
    have f1: "spfDom\<cdot>f1 \<subseteq> sbDom\<cdot>sb"
      by (simp add: C_def Un_commute Un_left_commute assms)
    have "spfDom\<cdot>f2 \<subseteq> sbDom\<cdot>sb"
      using C_def assms by auto
    then show "sbDom\<cdot>x \<union> (sbDom\<cdot>Rep_CSPF f1\<rightharpoonup>(sb\<bar>spfDom\<cdot>f1)) \<union> (sbDom\<cdot>Rep_CSPF f2\<rightharpoonup>(sb\<bar>spfDom\<cdot>f2)) 
                = (sbDom\<cdot>x \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
      using f1 by simp
  qed

lemma spfComp_itCompH2_dom[simp]: assumes "sbDom\<cdot>x = I f1 f2"
  shows "sbDom\<cdot>(iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) = C f1 f2"
  apply (induct_tac i)
   apply auto[1]
  by (simp add: C_def I_def assms inf_sup_aci(6))

(* Parallel Composition general *)

lemma [simp]: assumes "c \<in> spfRan\<cdot>f1"
  shows "c \<notin> I f1 f2"
by (simp add: I_def assms(1))

lemma [simp]: assumes "c \<in> spfRan\<cdot>f1"
                  and "L f1 f2 = {}"
                  and "spfComp_well f1 f2"
  shows "c \<notin> spfRan\<cdot>f2"
by (meson assms(1) assms(3) disjoint_iff_not_equal spfComp_well_def)

lemma [simp]: assumes "c \<in> spfRan\<cdot>f1"
                  and "L f1 f2 = {}"
  shows "c \<notin> spfDom\<cdot>f1 \<and> c \<notin> spfDom\<cdot>f2"
using L_def assms(1) assms(2) by blast

lemma [simp]: assumes "L f1 f2 = {}"
  shows "spfDom\<cdot>f1 \<subseteq> I f1 f2"
apply(auto simp add: I_def)
using L_def assms apply fastforce
using L_def assms by fastforce

lemma  spfComp_I_domf1f2_eq[simp]: assumes "L f1 f2 = {}" 
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

lemma spfComp_domranf1: assumes "L f1 f2 = {}"
                        and "sbDom\<cdot>sb = I f1 f2" 
                        and "spfComp_well f1 f2" 
  shows "(sbDom\<cdot>Rep_CSPF f1\<rightharpoonup>(sb\<bar>spfDom\<cdot>f1)) = spfRan\<cdot>f1"
by(simp add: assms)

(* Iterate *)

lemma spfComp_getChI: assumes "sbDom\<cdot>x = I f1 f2" 
                      and "spfComp_well f1 f2"
                      and "c \<in> I f1 f2"
  shows "(iterate (Suc i)\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) . c = x .c"
  apply (unfold iterate_Suc, subst spfCompHelp2_def)
  apply (simp)
  apply (subst sbunion_getchL)
  apply (metis C_def DiffD2 I_def UnI2 assms(1) assms(3) inf_sup_ord(4) 
               le_supI1 spfComp_itCompH2_dom spfRanRestrict)
  apply (subst sbunion_getchL)
   apply (metis C_def DiffD2 I_def UnI1 Un_upper1 assms(1) assms(3) 
                le_supI1 spfComp_itCompH2_dom spfRanRestrict)
   by (simp)

lemma spfComp_resI: assumes "sbDom\<cdot>x = I f1 f2" 
                    and "spfComp_well f1 f2"
  shows "(iterate (Suc i)\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) \<bar> (I f1 f2) = x"
  apply (rule sb_eq)
   apply (simp add: assms(1) inf_sup_aci(1) inf_sup_aci(6))
   using assms(1) assms(2) spfComp_getChI by fastforce

lemma spfComp_parallelf1 : assumes" L f1 f2 = {}"
                       and "sbDom\<cdot>x = I f1 f2" 
                       and "spfComp_well f1 f2"
                       and "c \<in> spfRan\<cdot>f1" 
  shows "(iterate (Suc (Suc i))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) . c
                  = (x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2))) . c"
apply(subst iterate_Suc)
apply(subst spfCompHelp2_def, simp)
apply(subst sbunion_getchL)
apply (metis (no_types, hide_lams) C_def Un_subset_iff assms(2) assms(3) assms(4) disjoint_iff_not_equal iterate_Suc spfComp_itCompH2_dom spfComp_well_def spfRanRestrict sup_ge1)
apply(subst sbunion_getchR)
apply (simp add: assms(1) assms(2) assms(4) inf_sup_aci(6))
apply(subst sbunion_getchL)
using assms(1) assms(2) assms(3) assms(4) spfComp_I_domf1f2_eq apply auto[1]
apply(subst sbunion_getchR)
using assms(1) assms(2) assms(3) assms(4) spfComp_domranf1 apply blast
by (smt Int_absorb1 Un_assoc Un_upper1 assms(1) assms(2) assms(3) iterate_Suc sb_eq sbrestrict2sbgetch sbrestrict_sbdom set_mp spfCompH2_dom spfComp_I_domf1f2_eq spfComp_itCompH2_dom spfComp_resI)

lemma spfComp_parallelf2 : assumes" L f1 f2 = {}"
                       and "sbDom\<cdot>x = I f1 f2" 
                       and "spfComp_well f1 f2"
                       and "c \<in> spfRan\<cdot>f2" 
  shows "(iterate (Suc (Suc i))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) . c
                  = (x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2))) . c"
apply(subst iterate_Suc)
apply(subst spfCompHelp2_def, simp)
apply(subst sbunion_getchR)
apply(smt Un_commute assms(1) assms(2) assms(4) inf_sup_aci(6) spfCompH2_dom spfComp_I_domf1f2_eq spfComp_itCompH2_dom spfRanRestrict sup_ge1)
apply(subst sbunion_getchR)
apply(simp add: assms(1) assms(2) assms(4))
sorry

lemma spfComp_parallel : assumes" L f1 f2 = {}"
                       and "sbDom\<cdot>x = I f1 f2" 
                       and "spfComp_well f1 f2"
  shows "(iterate (Suc (Suc i))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
                  = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2))" (is "?L = ?R")
  apply(rule sb_eq)
apply (metis C_def assms(1) assms(2) assms(3) inf_sup_ord(4) sbunionDom spfComp_I_domf1f2_eq spfComp_domranf1 spfComp_itCompH2_dom spfRanRestrict spfdom_insert)
by (metis (no_types, lifting) UnE assms(1) assms(2) assms(3) iterate_Suc sbunionDom sbunion_getchL spfCompH2_dom spfComp_I_domf1f2_eq spfComp_domranf1 spfComp_getChI spfComp_itCompH2_dom spfComp_parallelf1 spfComp_parallelf2 spfRanRestrict sup_ge2)


(* LUB *)

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
apply(subst spfComp_parallel, simp_all add: assms)
by (smt One_nat_def Suc_1 Suc_le_D Suc_le_lessD assms(1) assms(2) assms(3) le_simps(2) spfComp_parallel)

lemma spfComp_parallel_itconst1 [simp]: assumes "L f1 f2 = {}"
                                      and "sbDom\<cdot>x = I f1 f2" 
                                      and "spfComp_well f1 f2"
  shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
               = iterate 2\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))"
using assms(1) assms(2) assms(3) 
    maxinch_is_thelub spfComp_parallel_max spfComp_parallelnf_chain by blast

lemma spfComp_parallel_itconst2: assumes "L f1 f2 = {}" 
                                    and "sbDom\<cdot>x = I f1 f2" 
                                    and "spfComp_well f1 f2"
  shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
            = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2))"
by (metis One_nat_def Suc_1 assms(1) assms(2) assms(3) 
    spfComp_parallel spfComp_parallel_itconst1)

(* Parallel Composition *)

(*I intended to proof this with fix but didnt find a way to proof the second lemma 
lemma iterate_const: "(\<Squnion>i. iterate i\<cdot>(\<Lambda> x. c)\<cdot>z) = c"
apply(simp add: iterate_def)
sorry

lemma test: assumes "L f1 f2 = {}"
                and "sbDom\<cdot>x = I f1 f2"
                and "spfComp_well f1 f2"
  shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
            = (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(x \<bar> spfDom\<cdot>f1)) 
                                 \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(x \<bar> spfDom\<cdot>f2)))\<cdot>(sbLeast (C f1 f2)))"
sorry
*)

lemma spfCompParallelGetch: assumes "L f1 f2 = {}"
                                and "sbDom\<cdot>sb = I f1 f2"
                                and "spfComp_well f1 f2"
                                and "c \<in> spfRan\<cdot>f1" 
  shows "(Rep_CSPF(spfcomp f1 f2) \<rightharpoonup> sb) . c = (Rep_CSPF(f1) \<rightharpoonup> (sb\<bar>spfDom\<cdot>f1)) . c"
apply(simp add: spfcomp_tospfH2)
apply(simp only: spfcomp_repAbs assms, simp_all)
apply(simp only: spfComp_parallel_itconst2 assms)
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