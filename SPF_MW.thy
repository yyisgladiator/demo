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

lemma spfComp_parallel : assumes" L f1 f2 = {}"
                            and "sbDom\<cdot>x = I f1 f2" 
                            and "spfComp_well f1 f2"
  shows "(iterate (Suc (Suc i))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
                  = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2))" (is "?L = ?R")
apply(rule sb_eq)
apply (metis C_def assms(1) assms(2) assms(3) inf_sup_ord(4) sbunionDom spfComp_I_domf1f2_eq spfComp_domranf1 spfComp_itCompH2_dom spfRanRestrict spfdom_insert)
by (metis (no_types, lifting) UnE assms(1) assms(2) assms(3) iterate_Suc sbunionDom sbunion_getchL spfCompH2_dom spfComp_I_domf1f2_eq spfComp_domranf1 spfComp_getChI spfComp_itCompH2_dom spfComp_parallelf1 spfComp_parallelf2 spfRanRestrict sup_ge2)


lemma spfComp_serial : assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                       and "sbDom\<cdot>x = I f1 f2" 
                       and "spfComp_well f1 f2"
                       and "pL f1 f2 = {}"
  shows "(iterate (Suc (Suc (Suc i)))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))
                  = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) 
                      \<uplus> ((Rep_CSPF f2)\<rightharpoonup>((Rep_CSPF f1) \<rightharpoonup> (x\<bar>spfDom\<cdot>f1)))" (is "?L = ?R")
  apply(rule sb_eq)
  apply (smt C_def assms(1) assms(2) assms(3) assms(4) inf_sup_ord(4) sbunionDom sbunion_restrict 
             spfComp_I_domf1_eq spfComp_domranf1 spfCompH2_itDom spfRanRestrict sup.right_idem)
  by (smt assms(1) assms(2) assms(3) assms(4) inf_sup_ord(4) iterate_Suc sbunionDom 
          sbunion_getchL sbunion_getchR sbunion_restrict spfComp_domranf1 spfCompH2_getch_outofrange 
          spfCompH2_itDom spfComp_serialf1 spfComp_serialf2 spfRanRestrict)




end