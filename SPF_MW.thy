theory SPF_MW
imports SPF SerComp_JB ParComp_MW (*InnerProd_Case_StudyTSPFTheorie*)
begin

(* operator for parallel composition *)

definition parcomp :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF" ("_\<parallel>_") where
"parcomp f1 f2 \<equiv> Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))"

(* spfDom *)

lemma spfDomAbs: "spfDom\<cdot>(Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = cs ) \<leadsto> f(x))) = cs" 
apply(simp add: spfDom_def dom_def)
sorry

lemma sbDomIterate: "sbDom\<cdot>(\<Squnion>i. iterate i\<cdot>F\<cdot>sb)  = sbDom\<cdot>(F\<cdot>sb)"
sorry

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
apply(simp add: spfcomp_tospfH2 spfran_least spfDomAbs)
apply(subst spfcomp_repAbs, simp_all add: assms)
apply(subst sbDomIterate)
apply(subst sbDomH2, simp)
using C_def apply blast
using Oc_def by auto

lemma spfComp_dom_I: "spfDom\<cdot>(spfcomp f1 f2) = I f1 f2"
by(simp add: spfcomp_def spfDomAbs ) 

(* hide *)

definition hide :: "'m SPF \<Rightarrow>  channel set \<Rightarrow> 'm SPF" where
"hide f cs \<equiv> Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(spfRan\<cdot>f - cs)))"

lemma[simp]: assumes "cont (Rep_CSPF(f))" shows "cont (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(spfRan\<cdot>f - cs)))"
sorry

lemma[simp]: "spf_well (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(spfRan\<cdot>f - cs)))"
apply(auto simp add: spf_well_def domIff2 sbdom_rep_eq)
sorry

lemma spfDomHide: "spfDom\<cdot>(hide f cs) = spfDom\<cdot>f"
apply(simp add: hide_def)
by(simp add: spfDomAbs)

lemma hideSbRestrict: assumes "sbDom\<cdot>sb = spfDom\<cdot>f" 
   shows "(hide f cs)\<rightleftharpoons>sb = (f\<rightleftharpoons>sb)\<bar>(spfRan\<cdot>f - cs)"
apply(simp add: hide_def)
using assms by blast

lemma hideSbRestrictCh: assumes "sbDom\<cdot>sb = spfDom\<cdot>f" and "c \<notin> cs"
   shows "(hide f cs)\<rightleftharpoons>sb . c = (f\<rightleftharpoons>sb) . c"
apply(simp add: hide_def)
by (metis (no_types, lifting) DiffI Int_commute Un_Diff_Int assms(1) assms(2) domIff inf_sup_absorb option.collapse sbdom_insert sbgetch_insert sbleast_sbdom sbrestrict2sbgetch sbrestrict_sbdom spfLeastIDom spf_sbdom2dom spfran2sbdom)

lemma hideSpfRan: "spfRan\<cdot>(hide f cs) = spfRan\<cdot>f - cs"
apply(subst spfran_least)
apply(simp add: spfDomHide)
apply(subst hideSbRestrict)
apply (simp add:assms)
apply(subst sbrestrict_sbdom)
by (simp add: Diff_subset Int_absorb1 spfran_least)

lemma hideSubset: "spfRan\<cdot>(hide f cs) \<subseteq> spfRan\<cdot>f"
using hideSpfRan by auto

(* inner prod *)

(*definition innerProd :: "nat SPF" where
"innerProd \<equiv> hide ((mult1 \<parallel> mult2) \<otimes> addC) {c5, c6}"
*)

(* lemmas about parallel composition *)

lemma LtopL: "L f1 f2 = {} \<Longrightarrow> pL f1 f2 = {}"
apply(simp add: L_def pL_def)
by (simp add: Int_Un_distrib inf_sup_distrib2)

lemma unionRestrictCh: assumes "sbDom\<cdot>sb1 \<inter> cs = {}"
                           and "sbDom\<cdot>sb2 \<union> sbDom\<cdot>sb3 = cs"
                           and "c \<in> cs"
   shows "(sb1 \<uplus> sb2 \<uplus> sb3 \<bar> cs) . c = (sb2 \<uplus> sb3) . c"
by (metis (no_types, lifting) Un_upper2 assms(1) assms(2) inf_sup_distrib1 inf_sup_ord(3) sbrestrict_id sbunion_commutative sbunion_restrict2 sbunion_restrict3 sup_eq_bot_iff)

lemma unionRestrict: assumes "sbDom\<cdot>sb1 \<inter> cs = {}"
                         and "sbDom\<cdot>sb2 \<union> sbDom\<cdot>sb3 = cs"
   shows "sb1 \<uplus> sb2 \<uplus> sb3 \<bar> cs = sb2 \<uplus> sb3"
apply(rule sb_eq)
apply(simp_all add: assms)
apply (simp add: Int_absorb1 assms(2) sup_assoc)
by (metis Un_iff assms(2) sbunion_getchL sbunion_getchR)

lemma parCompHelp2Eq: assumes "L f1 f2 = {}"
                          and "spfComp_well f1 f2"
                          and "sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2"    
   shows "(\<Squnion>i. iterate i\<cdot>(ParComp_MW.spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2 = (f1\<rightleftharpoons>(x\<bar>spfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x\<bar>spfDom\<cdot>f2))" 
apply(subst spfComp_parallel_itconst2, simp_all add: assms)
apply(simp add: Oc_def)
apply(subst unionRestrict)
apply(simp_all add: assms)
by (metis Diff_triv L_def assms(1) inf_commute)

lemma parCompHelp2Eq2: assumes "L f1 f2 = {}"
                           and "spfComp_well f1 f2" 
   shows " (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2) \<leadsto> ((\<Squnion>i. iterate i\<cdot>(ParComp_MW.spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2)
         = (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2) \<leadsto> ((f1\<rightleftharpoons>(x\<bar>spfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x\<bar>spfDom\<cdot>f2)))"
using assms(1) assms(2) parCompHelp2Eq by fastforce

lemma parallelOperatorEq: assumes "L f1 f2 = {}"
                              and "spfComp_well f1 f2"  
   shows "(spfcomp f1 f2) = (f1 \<parallel> f2)"
apply(simp add: parcomp_def spfcomp_tospfH2)
apply(subst spfComp_I_domf1f2_eq, simp_all add: assms)
apply(subst parCompHelp2Eq2)
by(simp_all add: assms)

lemma parCompDom: assumes "L f1 f2 = {}"
                  and "spfComp_well f1 f2" shows "spfDom\<cdot>(f1 \<parallel> f2) = spfDom\<cdot>(spfcomp f1 f2)"
by(simp add: parallelOperatorEq assms)

lemma parCompRan: assumes "L f1 f2 = {}"
                  and "spfComp_well f1 f2" shows "spfRan\<cdot>(f1 \<parallel> f2) = spfRan\<cdot>(spfcomp f1 f2)"
by(simp add: parallelOperatorEq assms)

end