theory SPF_MW
imports SPF SerComp_JB ParComp_MW_JB SPF_Composition_JB SPF_Templates
begin

(* operator for parallel composition *)

definition parcomp :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF" ("_\<parallel>_") where
"parcomp f1 f2 \<equiv> Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))"

(* operator for serial composition *)

definition sercomp :: "'m SPF => 'm SPF => 'm SPF"  ("_\<circ>_") where
"sercomp f1 f2 \<equiv> Abs_CSPF (\<lambda> x. (sbDom\<cdot>x =  spfDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> x) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))"

(* spfDom spfcomp *)

lemma spfDomAbs: assumes "cont (\<lambda> x. (sbDom\<cdot>x = cs ) \<leadsto> f(x))" and "spf_well (Abs_cfun (\<lambda> x. (sbDom\<cdot>x = cs ) \<leadsto> f(x)))"
    shows "spfDom\<cdot>(Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = cs ) \<leadsto> f(x))) = cs" 
apply(simp add: spfDom_def)
apply(simp_all add: assms)
by (smt domIff option.discI sbleast_sbdom someI_ex)

lemma spfComp_dom_I: assumes "spfComp_well f1 f2" shows "spfDom\<cdot>(spfcomp f1 f2) = I f1 f2"
apply(simp add: spfcomp_tospfH2, subst spfDomAbs)
by(simp_all add: assms)

(* spfRan spfcomp *)

lemma sbDomIterate: "sbDom\<cdot>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 (sbLeast (I f1 f2)))\<cdot>sb)  = sbDom\<cdot>((spfCompHelp2 f1 f2 (sbLeast (I f1 f2)))\<cdot>sb)"
apply(simp add: sbDom_def spfCompHelp2_def)
(* in SPF *)
  oops
    

lemma spfDomHelp: assumes "spfDom\<cdot>f1 \<subseteq> sbDom\<cdot>sb" shows "sbDom\<cdot>f1\<rightleftharpoons>sb\<bar>spfDom\<cdot>f1 = spfRan\<cdot>f1"
by (simp add: assms)

lemma sbDomH2: assumes "spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 \<subseteq> sbDom\<cdot>sb2" shows "sbDom\<cdot>((spfCompHelp2 f1 f2 sb1)\<cdot>sb2) = sbDom\<cdot>sb1 \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2"
apply(simp add: spfCompHelp2_def)
apply(subst spfDomHelp)
using assms apply auto[1]
apply(subst spfDomHelp)
using assms apply auto[1]
by simp

lemma spfComp_ran_Oc: assumes "spfComp_well f1 f2" shows "spfRan\<cdot>(spfcomp f1 f2) = Oc f1 f2"
  apply(simp add: spfcomp_tospfH2)
  apply(simp add:  spfran_least)
  by(subst spfDomAbs, simp_all add: assms inf.absorb2)


(* hide *)

definition hide :: "'m SPF \<Rightarrow>  channel set \<Rightarrow> 'm SPF" ("_\<h>_") where
"hide f cs \<equiv> Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(spfRan\<cdot>f - cs)))"

lemma hidecont_helper[simp]:  
  shows "cont (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(spfRan\<cdot>f - cs)))"
apply(subst if_then_cont, simp_all)
by (simp add: cont_compose)

  
(* TODO  assumes "spf_well (Abs_cfun (Rep_CSPF(f)))"  *)  
lemma hidespfwell_helper[simp]: assumes "spf_well (Abs_cfun (Rep_CSPF(f)))" 
  shows "spf_well ((\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(spfRan\<cdot>f - cs))))"
  apply(simp add: spf_well_def)
  apply(simp only: domIff2)
  apply(auto simp add: sbdom_rep_eq)
sorry

lemma spfDomHide: "spfDom\<cdot>(f \<h> cs) = spfDom\<cdot>f"
  apply(simp add: hide_def)
    by(simp add: spfDomAbs hidecont_helper hidespfwell_helper)

lemma hideSbRestrict: assumes "sbDom\<cdot>sb = spfDom\<cdot>f" 
   shows "(hide f cs)\<rightleftharpoons>sb = (f\<rightleftharpoons>sb)\<bar>(spfRan\<cdot>f - cs)"
  apply(simp add: hide_def)
  apply(simp add: hidecont_helper hidespfwell_helper)
    by (simp add: assms)

lemma hideSbRestrictCh: assumes "sbDom\<cdot>sb = spfDom\<cdot>f" and "c \<notin> cs"
   shows "(hide f cs)\<rightleftharpoons>sb . c = (f\<rightleftharpoons>sb) . c"
  apply(simp add: hide_def)
  apply(simp add: hidecont_helper hidespfwell_helper assms)
  by (smt DiffI Diff_subset Int_absorb1 assms(1) assms(2) domIff option.exhaust_sel sbleast_sbdom sbrestrict2sbgetch sbrestrict_sbdom sbunion_getchL sbunion_idL spfLeastIDom spf_sbdom2dom spfran2sbdom)
    
lemma hideSpfRan: "spfRan\<cdot>(hide f cs) = spfRan\<cdot>f - cs"
  apply(subst spfran_least)
  apply(simp add: spfDomHide)
  apply(subst hideSbRestrict)
  apply(simp)
  apply(subst sbrestrict_sbdom)
  by (simp add: Diff_subset Int_absorb1 spfran_least)

lemma hideSubset: "spfRan\<cdot>(hide f cs) \<subseteq> spfRan\<cdot>f"
  using hideSpfRan by auto

(* lemmas about parallel composition *)

lemma LtopL: "L f1 f2 = {} \<Longrightarrow> pL f1 f2 = {}"
  using spfpl_sub_L by blast

lemma unionRestrictCh: assumes "sbDom\<cdot>sb1 \<inter> cs = {}"
                           and "sbDom\<cdot>sb2 \<union> sbDom\<cdot>sb3 = cs"
                           and "c \<in> cs"
   shows "(sb1 \<uplus> sb2 \<uplus> sb3 \<bar> cs) . c = (sb2 \<uplus> sb3) . c"
by (metis (no_types, lifting) Un_upper2 assms(1) assms(2) inf_sup_distrib1 inf_sup_ord(3) sbrestrict_id sbunion_commutative sbunion_restrict2 sbunion_restrict3 sup_eq_bot_iff)

lemma unionRestrict: assumes "sbDom\<cdot>sb1 \<inter> cs = {}"
                         and "sbDom\<cdot>sb2 \<union> sbDom\<cdot>sb3 = cs"
   shows "sb1 \<uplus> sb2 \<uplus> sb3 \<bar> cs = sb2 \<uplus> sb3"
  by (metis assms(2) sbunionDom sbunion_associative sbunion_restrict)

lemma parCompHelp2Eq: assumes "L f1 f2 = {}"
                          and "spfComp_well f1 f2"
                          and "sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2"    
   shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2 = (f1\<rightleftharpoons>(x\<bar>spfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x\<bar>spfDom\<cdot>f2))" 
apply(subst spfComp_parallel_itconst2, simp_all add: assms)
apply(simp add: Oc_def)
apply(subst unionRestrict)
apply(simp_all add: assms)
by (metis Diff_triv L_def assms(1) inf_commute)

lemma parCompHelp2Eq2: assumes "L f1 f2 = {}"
                           and "spfComp_well f1 f2" 
   shows " (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2) \<leadsto> ((\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)
         = (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2) \<leadsto> ((f1\<rightleftharpoons>(x\<bar>spfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x\<bar>spfDom\<cdot>f2)))"
using assms(1) assms(2) parCompHelp2Eq by fastforce

lemma parallelOperatorEq: assumes "L f1 f2 = {}"
                              and "spfComp_well f1 f2"  
   shows "(f1 \<otimes> f2) = (f1 \<parallel> f2)"
apply(simp add: parcomp_def spfcomp_tospfH2)
apply(subst spfComp_I_domf1f2_eq, simp_all add: assms)
apply(subst parCompHelp2Eq2)
by(simp_all add: assms)

lemma parCompDom: assumes "L f1 f2 = {}"
                  and "spfComp_well f1 f2" shows "spfDom\<cdot>(f1 \<parallel> f2) = spfDom\<cdot>(spfcomp f1 f2)"
  by (simp add: assms(1) assms(2) parallelOperatorEq)

lemma parCompRan: assumes "L f1 f2 = {}"
                  and "spfComp_well f1 f2" shows "spfRan\<cdot>(f1 \<parallel> f2) = spfRan\<cdot>(spfcomp f1 f2)"
  by (simp add: assms(1) assms(2) parallelOperatorEq)

(* lemmas about serial composition *)

lemma pLEmptyNoSelfloops: assumes "pL f1 f2 = {}"
  shows "no_selfloops f1 f2"
  apply(simp add: no_selfloops_def)
  using assms pL_def by auto
    
lemma spfComp_I_domf1_eq: assumes "pL f1 f2 = {}"
                              and "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                              and "spfComp_well f1 f2"
   shows "I f1 f2 = spfDom\<cdot>f1"
  using SerComp_JB.spfComp_I_domf1_eq assms(1) assms(2) assms(3) pLEmptyNoSelfloops spfComp_dom_I spfdom_insert by blast

     
lemma serCompHelp2Eq: assumes "pL f1 f2 = {}"
                          and "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                          and "spfComp_well f1 f2"
                          and "sbDom\<cdot>x = spfDom\<cdot>f1" 
   shows "(\<Squnion>i. iterate i\<cdot>(SPF.spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2 = ((f1 \<rightleftharpoons> x)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))" 
  apply(subst spfComp_serial_itconst2)
       apply(simp_all add: assms)
    apply(subst spfComp_I_domf1_eq, simp_all add: assms)
    apply(simp add: pLEmptyNoSelfloops assms)
  apply(simp add: Oc_def)
   apply(subst unionRestrict, simp_all add: assms)
   using pL_def assms(1) assms(2) apply blast
   by (metis (no_types, lifting) assms(2) assms(4) domIff option.collapse sbleast_sbdom spfLeastIDom spf_sbdom2dom spfran2sbdom)

lemma serCompHelp2Eq2: assumes "pL f1 f2 = {}"
                           and "spfComp_well f1 f2"
                           and "spfRan\<cdot>f1 = spfDom\<cdot>f2"
   shows " (sbDom\<cdot>x = spfDom\<cdot>f1) \<leadsto> ((\<Squnion>i. iterate i\<cdot>(SPF.spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)
         = (sbDom\<cdot>x = spfDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> x) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
  by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) lub_eq serCompHelp2Eq)

lemma serialOperatorEq: assumes "pL f1 f2 = {}"
                            and "spfComp_well f1 f2"
                            and "spfRan\<cdot>f1 = spfDom\<cdot>f2"
   shows "(f1 \<otimes> f2) = (f1 \<circ> f2)"
apply(simp add: sercomp_def SerComp_JB.spfcomp_tospfH2)
apply(subst spfComp_I_domf1_eq, simp_all add: assms)
apply(subst serCompHelp2Eq2)
by(simp_all add: assms)

(* general lemmas for cont and spf_well *)

lemma conthelper: assumes "cont (Rep_CSPF f)" and "spfDom\<cdot>f = cs" shows "cont (\<lambda> z. (f\<rightleftharpoons>(z\<bar>cs)))"
by (metis Rep_CSPF_def cont_Rep_cfun2 cont_compose op_the_cont)

lemma conthelper2: assumes "cs = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2"
                       and "cont (Rep_CSPF f1)" 
                       and "cont (Rep_CSPF f2)"
  shows "cont (\<lambda> x. (sbDom\<cdot>x = cs)\<leadsto>((f1\<rightleftharpoons>(x\<bar>spfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x\<bar>spfDom\<cdot>f2))))"
apply(subst if_then_cont, simp_all)
apply(subst cont2cont_APP)
apply (metis Rep_CSPF_def cont_Rep_cfun2 cont_compose conthelper)
using conthelper apply auto[1]
by auto

lemma spfwellhelper: assumes "cs = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2" 
                         and "cont (Rep_CSPF f1)" 
                         and "cont (Rep_CSPF f2)"
  shows "spf_well (\<Lambda> x. (sbDom\<cdot>x = cs)\<leadsto>((f1\<rightleftharpoons>(x\<bar>spfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x\<bar>spfDom\<cdot>f2))))"
apply(simp add: spf_well_def domIff2 sbdom_rep_eq)
apply(subst Abs_cfun_inverse2)
apply(subst conthelper2, simp_all add: assms)
apply(subst Abs_cfun_inverse2)
apply(subst conthelper2, simp_all add: assms)
apply(subst Abs_cfun_inverse2)
   apply(subst conthelper2, simp_all add: assms)
oops

end