theory SPF_MW
imports SPF SerComp_JB ParComp_MW TSPFTheorie
begin

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
   (\<Lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> I1)) \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> I2)))\<cdot>(sbLeast C)) \<bar> Oc)"

(* feedback stüber *)

definition add :: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream" where
"add \<equiv> \<Lambda> s1 s2. smap (\<lambda> s3. (fst s3) + (snd s3)) \<cdot> (szip \<cdot>s1\<cdot>s2)"

definition sum4 :: "nat stream \<rightarrow> nat stream" where
"sum4 \<equiv> \<Lambda> x. (fix\<cdot>(\<Lambda> z. add\<cdot>x\<cdot>(\<up>0 \<bullet> (z))))"

primrec tspfMu_helper :: "nat \<Rightarrow> 'm TSPF \<Rightarrow> 'm TSB_inf \<Rightarrow> 'm TSB" where
"tspfMu_helper 0 f1 tb = tsbLeast (tspfDom\<cdot>f1 \<union> tspfRan\<cdot>f1) " |
"tspfMu_helper (Suc n) f1 tb =( let last = tspfMu_helper n f1 tb in
 (tb \<uplus> (f1 \<rightharpoondown> (last \<bar> tspfDom\<cdot>f1)) \<down> (Suc n) ))"

definition tspfMu :: "'m TSPF \<Rightarrow> 'm TSPF"  where
"tspfMu f1 \<equiv> Abs_TSPF (\<lambda> tb. (tsbiDom\<cdot>tb=(tspfDom\<cdot>f1 - tspfRan\<cdot>f1)) \<leadsto>
 (tsb2tsbInf (\<Squnion> i. tspfMu_helper i f1 tb ) \<bar> (tspfRan\<cdot>f1 - tspfDom\<cdot>f1)) )"

(* lemmas about composition *)

lemma LtopL: "L f1 f2 = {} \<Longrightarrow> pL f1 f2 = {}"
apply(simp add: L_def pL_def)
by (simp add: Int_Un_distrib inf_sup_distrib2)

lemma spfComp_parallel_noFix: assumes "L f1 f2 = {}"
                                         and "sbDom\<cdot>x = I f1 f2" 
                                         and "spfComp_well f1 f2"
  shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
               = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2))"
by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) lub_eq spfComp_parallel_itconst2)

lemma spfComp_serial_noFix: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                                and "sbDom\<cdot>x = I f1 f2" 
                                and "spfComp_well f1 f2"
                                and "pL f1 f2 = {}"
  shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
            = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2)\<rightharpoonup>((Rep_CSPF f1) \<rightharpoonup> (x\<bar>spfDom\<cdot>f1)))"
by (metis (no_types, lifting) ParComp_MW.spfCompHelp2_def SerComp_JB.spfCompHelp2_def SerComp_JB.spfComp_serial_itconst2 assms(1) assms(2) assms(3) assms(4) lub_eq)

lemma parallelOperatorEq: assumes "L f1 f2 = {}"
                              and "sbDom\<cdot>sb = I f1 f2"
                            shows "(f1 \<otimes> f2)\<rightleftharpoons>sb = (f1 \<parallel> f2)\<rightleftharpoons>sb"
sorry

lemma serialOperatorEq: assumes "pL f1 f2 = {}"
                            and "sbDom\<cdot>sb = I f1 f2"
                            and "c \<in> spfRan\<cdot>f2"
  shows "(spfComp2 f1 f2)\<rightleftharpoons>sb . c  = (sercomp f1 f2)\<rightleftharpoons>sb . c"
apply(simp add: sercomp_def)
sorry

end