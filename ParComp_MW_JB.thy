(*  Title: ParComp_MW_JB
    Author: Marc Wiartalla, Jens Christoph Bürger
    e-mail: marc.wiartalla@rwth-aachen.de, jens.buerger@rwth-aachen.de

    Description: Based on original ParComp_MW but fully proved with SerComp
                  \<Rightarrow> Makes ParComp_MW obsolete
*)

theory ParComp_MW_JB
imports SPF SBTheorie SerComp_JB

begin




(* ID Definitions *)
lift_definition ID1 :: "nat SPF" is 
"\<Lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2 \<mapsto> sb_id\<cdot>(sb . c1)]\<Omega>)"
by(auto simp add: spf_well_def domIff2 sbdom_rep_eq)

lift_definition ID2 :: "nat SPF" is 
"\<Lambda> sb. (sbDom\<cdot>sb = {c3}) \<leadsto> ([c4 \<mapsto> sb_id\<cdot>(sb . c3)]\<Omega>)"
by(auto simp add: spf_well_def domIff2 sbdom_rep_eq)

lemma ID1_rep_eqC: "Rep_CSPF ID1 = (\<lambda> sb. (sbDom\<cdot>sb = {c1}) \<leadsto> ([c2 \<mapsto> sb_id\<cdot>(sb . c1)]\<Omega>))"
by(simp add: ID1.rep_eq Rep_CSPF_def)

lemma ID2_rep_eqC: "Rep_CSPF ID2 = (\<lambda> sb. (sbDom\<cdot>sb = {c3}) \<leadsto> ([c4 \<mapsto> sb_id\<cdot>(sb . c3)]\<Omega>))"
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

lemma sb_id_apply1: "((Rep_CSPF ID1) \<rightharpoonup> ([c1 \<mapsto> s]\<Omega>)) = ([c2 \<mapsto> (s:: nat stream)]\<Omega>)"
by(simp add: sb_id_def  Rep_CSPF_def ID1.rep_eq sbdom_rep_eq)

lemma sb_id_apply2: "((Rep_CSPF ID2) \<rightharpoonup> ([c3 \<mapsto> s]\<Omega>)) = ([c4 \<mapsto> (s:: nat stream)]\<Omega>)"
by(simp add: sb_id_def  Rep_CSPF_def ID2.rep_eq sbdom_rep_eq)

lemma [simp]: "spfComp_well ID1 ID2"
by (simp add: spfComp_well_def)

lemma [simp]: "no_selfloops ID1 ID2"
by(simp add: no_selfloops_def)

lemma [simp]: "C ID1 ID2 = {c1,c2,c3,c4}"
by (auto simp add: C_def)

lemma [simp]: "L ID1 ID2 = {}"
by (auto simp add: L_def)

lemma [simp]: "Oc ID1 ID2 = {c2, c4}"
by (auto simp add: Oc_def)

lemma [simp]: "I ID1 ID2 = {c1, c3}"
by (auto simp add: I_def)




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

lemma spfComp_cInOc1:  assumes "L f1 f2 = {}" 
                          and "spfComp_well f1 f2"
                          and "c \<in> spfRan\<cdot>f1" 
  shows "c \<in> Oc f1 f2"
  using L_def Oc_def assms(1) assms(3) by fastforce

lemma spfComp_cInOc2:  assumes "L f1 f2 = {}" 
                          and "spfComp_well f1 f2"
                          and "c \<in> spfRan\<cdot>f2" 
  shows "c \<in> Oc f1 f2"
using L_def Oc_def assms(1) assms(3) by fastforce

lemma spfComp_domranf1: assumes "L f1 f2 = {}"
                        and "sbDom\<cdot>sb = I f1 f2" 
                        and "spfComp_well f1 f2" 
  shows "(sbDom\<cdot>Rep_CSPF f1\<rightharpoonup>(sb\<bar>spfDom\<cdot>f1)) = spfRan\<cdot>f1"
by (simp add: assms(1) assms(2))

  
  
(* Iterate *)
lemma spfComp_parallelf1 : assumes" L f1 f2 = {}"
                              and "sbDom\<cdot>x = I f1 f2" 
                              and "spfComp_well f1 f2"
                              and "c \<in> spfRan\<cdot>f1" 
  shows "(iterate (Suc (Suc i))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) . c
                  = (x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2))) . c"
  apply(subst iterate_Suc)
  apply(subst spfCompHelp2_def, simp)
   apply(subst sbunion_getchL)
   apply (metis (no_types, hide_lams) C_def assms(2) assms(3) assms(4) disjoint_iff_not_equal iterate_Suc spfCompH2_itDom spfComp_well_def spfRanRestrict subsetI sup.bounded_iff)
    by (smt Int_absorb1 SerComp_JB.spfCompH2_itResI spfI_sub_C assms(1) assms(2) assms(3) assms(4) inf_sup_ord(4) iterate_Suc sb_eq sbrestrict2sbgetch sbrestrict_sbdom sbunion_associative sbunion_commutative sbunion_getchR spfComp_I_domf1f2_eq spfCompH2_itDom spfComp_well_def spfRanRestrict subsetCE sup.bounded_iff sup_ge1)
  
lemma spfComp_parallelf2 : assumes" L f1 f2 = {}"
                              and "sbDom\<cdot>x = I f1 f2" 
                              and "spfComp_well f1 f2"
                              and "c \<in> spfRan\<cdot>f2" 
  shows "(iterate (Suc (Suc i))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) . c
                  = (x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2))) . c"
  apply(subst iterate_Suc)
  apply(subst spfCompHelp2_def, simp)
  apply(subst sbunion_getchR)
  apply (metis spfI_sub_C assms(1) assms(2) assms(3) assms(4) spfCompHelp2_dom spfComp_I_domf1f2_eq spfCompH2_itDom spfComp_well_def spfRanRestrict sup.bounded_iff)
    apply(subst sbunion_getchR)
   apply(simp add: assms(1) assms(2) assms(4))
     by (smt Int_absorb1 SerComp_JB.spfCompH2_itResI spfI_sub_C assms(1) assms(2) assms(3) assms(4) inf_sup_ord(4) iterate_Suc sb_eq sbrestrict2sbgetch sbrestrict_sbdom sbunion_associative sbunion_commutative sbunion_getchR spfComp_I_domf1f2_eq spfCompH2_itDom spfComp_well_def spfRanRestrict subsetCE sup.bounded_iff sup_ge1)
 
lemma spfComp_parallel : assumes" L f1 f2 = {}"
                            and "sbDom\<cdot>x = I f1 f2" 
                            and "spfComp_well f1 f2"
  shows "(iterate (Suc (Suc i))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
                  = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2))" (is "?L = ?R")
apply(rule sb_eq)
apply (metis C_def assms(1) assms(2) assms(3) inf_sup_ord(4) sbunionDom spfComp_I_domf1f2_eq spfComp_domranf1 spfCompH2_itDom spfRanRestrict)   
by (metis (no_types, lifting) UnE assms(1) assms(2) assms(3) iterate_Suc sbunion_getchL SPF.spfCompH2_dom spfComp_I_domf1f2_eq spfComp_domranf1 spfCompH2_itgetChI spfCompH2_itDom spfComp_parallelf1 spfComp_parallelf2 spfRanRestrict sup_ge2)
 
    
lemma spfComp_parallel_max: assumes "L f1 f2 = {}" 
                                and "sbDom\<cdot>x = I f1 f2" 
                                and "spfComp_well f1 f2"
  shows "max_in_chain 2 (\<lambda>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"
apply(rule max_in_chainI, subst Num.numeral_2_eq_2)
apply(subst spfComp_parallel, simp_all add: assms)
by (smt One_nat_def Suc_1 Suc_le_D Suc_le_lessD assms(1) assms(2) assms(3) le_simps(2) spfComp_parallel)

  
  
(* LUB *)  
lemma spfComp_parallel_itconst1 [simp]: assumes "L f1 f2 = {}"
                                            and "sbDom\<cdot>x = I f1 f2" 
                                            and "spfComp_well f1 f2"
  shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
               = iterate 2\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))"
using assms(1) assms(2) assms(3) 
    maxinch_is_thelub spfComp_parallel_max SPF.spfComp_serialnf_chain by blast

lemma spfComp_parallel_itconst2 [simp]: assumes "L f1 f2 = {}" 
                                     and "sbDom\<cdot>x = I f1 f2" 
                                     and "spfComp_well f1 f2"
  shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
            = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2))"
by (metis One_nat_def Suc_1 assms(1) assms(2) assms(3) 
    spfComp_parallel spfComp_parallel_itconst1)  
  

(* show that spfcomp can be simplified to SPF without iterate if the assumtion hold *)
lemma spfComp_parallel_iterconst_eq1 [simp]:  assumes "L f1 f2 = {}" 
                                              and "spfComp_well f1 f2" shows
"(\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)
              = (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(  x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2)) )\<bar>Oc f1 f2)"
proof -
    have "\<forall>s. (sbDom\<cdot>s \<noteq> I f1 f2  \<or> (Some ((\<Squnion>n. iterate n\<cdot>(spfCompHelp2 f1 f2 s)\<cdot> (sbLeast (C f1 f2)))\<bar>Oc f1 f2) = Some (s \<uplus> (Rep_CSPF f1\<rightharpoonup>(s\<bar>spfDom\<cdot>f1)) \<uplus>  ((Rep_CSPF f2) \<rightharpoonup> (s\<bar>spfDom\<cdot>f2))\<bar>Oc f1 f2)))"
     by (metis assms(1) assms(2) spfComp_parallel_itconst2)
  then show ?thesis
    by meson
qed
  
(* show that iterconst ist cont, mono and a spf *)  
lemma parallel_iterconst_cont[simp]:     assumes "L f1 f2 = {}" 
                                         and "spfComp_well f1 f2" 
shows "cont (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                                    \<uplus> (f2 \<rightleftharpoons>(x\<bar>spfDom\<cdot>f2)) )\<bar>Oc f1 f2)"
proof -
   have "cont (\<lambda>s. (Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))"
     by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
   hence "cont (\<lambda>s. sbUnion\<cdot> (s  \<uplus>  ((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1)))) \<and> cont (\<lambda>s. Rep_SPF f2\<cdot>(s\<bar>spfDom\<cdot>f2))"
     by simp
   hence "cont (\<lambda>s. s  \<uplus>  ((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))   \<uplus>  ((Rep_cfun (Rep_SPF f2))\<rightharpoonup>(s\<bar>spfDom\<cdot>f2))  )"
     using cont2cont_APP cont_compose op_the_cont by blast 
   thus ?thesis
     by(simp add: Rep_CSPF_def)
  qed
       
lemma parallel_iterconst_monofun[simp]:  assumes "L f1 f2 = {}" 
                                         and "spfComp_well f1 f2" 
shows "monofun (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                                    \<uplus> (f2 \<rightleftharpoons>(x\<bar>spfDom\<cdot>f2)) )\<bar>Oc f1 f2)"
  using cont2mono parallel_iterconst_cont assms by blast
    
lemma parallel_iterconst_well[simp]: assumes "L f1 f2 = {}" 
                                         and "spfComp_well f1 f2"
shows "spf_well (Abs_cfun (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                                    \<uplus> (f2 \<rightleftharpoons>(x\<bar>spfDom\<cdot>f2)) )\<bar>Oc f1 f2))"
  apply (simp add: spf_well_def domIff2 sbdom_rep_eq assms)
    by auto
 

      
  
(* FINAL LEMMATA *)  
lemma spfCompParallelGetch1: assumes "L f1 f2 = {}"
                                and "sbDom\<cdot>sb = I f1 f2"
                                and "spfComp_well f1 f2"
                                and "c \<in> spfRan\<cdot>f1" 
  shows "(Rep_CSPF(spfcomp f1 f2) \<rightharpoonup> sb) . c = (Rep_CSPF(f1) \<rightharpoonup> (sb\<bar>spfDom\<cdot>f1)) . c"
  apply(simp add: spfcomp_tospfH2)
  apply (subst  spfComp_parallel_iterconst_eq1,  simp_all add: assms)
  apply(simp_all add: spfComp_cInOc1 assms)
  apply(subst sbunion_getchM, simp_all)
  apply(simp_all add: assms)
  apply(metis L_def UnCI assms(1) assms(4) disjoint_iff_not_equal)
  by (meson assms(3) assms(4) disjoint_iff_not_equal spfComp_well_def)
    
lemma spfCompParallelGetch2: assumes "L f1 f2 = {}"
                                and "sbDom\<cdot>sb = I f1 f2"
                                and "spfComp_well f1 f2"
                                and "c \<in> spfRan\<cdot>f2" 
  shows "(Rep_CSPF(spfcomp f1 f2) \<rightharpoonup> sb) . c = (Rep_CSPF(f2) \<rightharpoonup> (sb\<bar>spfDom\<cdot>f2)) . c"
  apply(simp add: spfcomp_tospfH2)
  apply (subst  spfComp_parallel_iterconst_eq1,  simp_all add: assms)
  by(simp_all add: spfComp_cInOc2 assms)