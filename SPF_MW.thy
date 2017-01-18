theory SPF_MW
imports SPF SerComp_JB ParComp_MW InnerProd_Case_Study(*TSPFTheorie*)
begin

(* operator for parallel composition *)

definition parcomp :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF" ("_\<parallel>_") where
"parcomp f1 f2 \<equiv> Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))"

(* hide *)

definition hide :: "'m SPF \<Rightarrow>  channel set \<Rightarrow> 'm SPF" where
"hide f cs \<equiv>
let newO = spfRan\<cdot>f - cs
in Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f ) \<leadsto> (((Rep_CSPF f) \<rightharpoonup> x)\<bar>newO))"

lemma hideSpfRan: "spfRan\<cdot>(hide f cs) = spfRan\<cdot>f - cs"
sorry

lemma hideSubset: "spfRan\<cdot>(hide f cs) \<subseteq> spfRan\<cdot>f"
using hideSpfRan by auto

(* new spfComp *)

definition Oc3 :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> channel set" where
"Oc3 f1 f2 \<equiv> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2"

definition spfcomp3 :: "'m SPF => 'm SPF => 'm SPF"  where
"spfcomp3 f1 f2 \<equiv> 
let I1 = spfDom\<cdot>f1;
    I2 = spfDom\<cdot>f2;
    O1 = spfRan\<cdot>f1; 
    O2 = spfRan\<cdot>f2; 
    I  = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 - (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2);
    Oc = spfRan\<cdot>f1 \<union> spfRan\<cdot>f2;
    C  = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2    
in Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I) \<leadsto> (\<Squnion>i. iterate i\<cdot>
   (\<Lambda> z. x \<uplus> (f1\<rightleftharpoons>(z \<bar> I1)) \<uplus> (f2\<rightleftharpoons>(z \<bar> I2)))\<cdot>(sbLeast C)) \<bar> Oc)"

(* inner prod *)

definition innerProd :: "nat SPF" where
"innerProd \<equiv> hide ((mult1 \<parallel> mult2) \<otimes> addC) {c5, c6}"

(* lemmas about composition *)

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

end