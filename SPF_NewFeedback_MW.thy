theory SPF_NewFeedback_MW
imports "CaseStudies/StreamCase_Study" SPF_Comp SPF_Templates SPF_FeedComp SPF_Feedback_JB 

begin

section \<open> general lemmas about sercomp and parcomp \<close>  

  
(* Should already be proven somewhere*)  
lemma parcomp_cont[simp]: "cont (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))"
sorry  
  
lemma parcomp_spf_well[simp]: "spf_well (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))"  
sorry

lemma sercomp_cont[simp]: "cont (\<lambda> x. (sbDom\<cdot>x =  spfDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> x) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))"
sorry  
  
lemma sercomp_spf_well[simp]: "spf_well (\<Lambda> x. (sbDom\<cdot>x =  spfDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> x) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))"  
sorry  

lemma parcomp_repAbs: "Rep_CSPF (Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))) 
                      = (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))"
  by simp
    
lemma sercomp_repAbs: "Rep_CSPF (Abs_CSPF (\<lambda> x. (sbDom\<cdot>x =  spfDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> x) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))) 
                      = (\<lambda> x. (sbDom\<cdot>x =  spfDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> x) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))"
  by simp
  
section \<open> Feedback Definitions \<close>  

  
definition MapIdFunct :: "(channel \<rightharpoonup> channel) \<Rightarrow> channel \<Rightarrow> channel" where
"MapIdFunct m \<equiv> (\<lambda> c. case m c of None \<Rightarrow> c | Some y \<Rightarrow> y )" 

definition the_inv_into :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)"
  where "the_inv_into A f = (\<lambda>x. THE y. y \<in> A \<and> f y = x)"
    
definition map_inverse :: "(channel \<rightharpoonup> channel) \<Rightarrow> (channel \<rightharpoonup> channel)" where
"map_inverse m \<equiv> (\<lambda>x. if (x \<in> (ran m)) then Some ((\<lambda> y. (THE z. m z = Some y)) x) else None)"
    
definition sbRenameChMap :: "'m SB \<Rightarrow> (channel \<rightharpoonup> channel) \<Rightarrow> 'm SB" where
"sbRenameChMap sb m \<equiv> Abs_SB (\<lambda>c. Rep_SB(sb)((MapIdFunct (map_inverse m))(c)))"  
  
definition spfRename :: "'a SPF \<Rightarrow> (channel \<rightharpoonup> channel) \<Rightarrow> 'a SPF" where
"spfRename f m \<equiv> Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m)) \<leadsto> (f \<rightleftharpoons> (sbRenameChMap sb m)))" 
  
definition spfFeedbackOperator_new :: "'a SPF \<Rightarrow> (channel \<rightharpoonup> channel) \<Rightarrow> 'a SPF" where
"spfFeedbackOperator_new f m \<equiv> spfFeedbackOperator (spfRename f m)"   

subsection \<open> cont, spf_well, rename lemmas \<close>

lemma spfRename_spfDom: "spfDom\<cdot>(spfRename f m) = (spfDom\<cdot>f - ran(m)) \<union> dom(m)"
  sorry
    
lemma spfRename_spfRan: "spfRan\<cdot>(spfRename f m) = spfRan\<cdot>f"
  sorry    

lemma spfRename_cont: "cont (\<lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m)) \<leadsto> (f \<rightleftharpoons> (sbRenameChMap sb m)))"
  sorry
    
lemma spfRename_spf_well: "spf_well (\<Lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m)) \<leadsto> (f \<rightleftharpoons> (sbRenameChMap sb m)))"
  sorry
    
lemma spfRename_RepAbs: "Rep_CSPF (Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m)) \<leadsto> (f \<rightleftharpoons> (sbRenameChMap sb m)))) = 
  (\<lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m)) \<leadsto> (f \<rightleftharpoons> (sbRenameChMap sb m)))"
  by(simp add: spfRename_cont spfRename_spf_well)

subsection \<open>rename lemmas \<close> 
  
(* to solve this lemmata it may be neccessary to redefine sbRenameChMap*)
  
lemma sbRenameChMap_sbDom: "sbDom\<cdot>(sbRenameChMap sb m) = (sbDom\<cdot>sb - dom(m)) \<union> ran(m)" 
  sorry
 
lemma t10: "sb_well (\<lambda>c. Rep_SB(sb)((MapIdFunct (map_inverse m))(c)))"    
  sorry
  
lemma sbRenameChMap_getCh: assumes "(m ch1) = Some ch2" and "\<not>(\<exists> ch3. ((m ch3) = Some ch2))" shows "(sbRenameChMap sb m) . ch2 = sb . ch1"
proof - 
  have f1: "ch2 \<in> ran m"
    by (meson assms ranI)
  have f2: " Rep_SB sb \<rightharpoonup> ch1 = sb . ch1"
    by (simp add: sbGetCh_def)
  have f3: "(THE z. (m z = Some ch2)) = ch1"
    using assms(1) assms(2) by auto
  show ?thesis  
    apply(simp add: sbRenameChMap_def)
    apply(subst sbGetCh_def, simp)
    apply(subst rep_abs, simp add: t10)
    apply(simp add: MapIdFunct_def map_inverse_def f1)
    by(simp add: f3 f2)
qed
    
lemma sbRenameChMap_getCh2: assumes "\<not>(\<exists> ch2. ((m ch2) = Some ch1))"  shows "(sbRenameChMap sb m) . ch1 = sb . ch1" 
proof - 
  have f1: "ch1 \<notin> ran m"
    by (meson assms ran2exists)
  have f2: " Rep_SB sb \<rightharpoonup> ch1 = sb . ch1"
    by (simp add: sbGetCh_def)
  show ?thesis  
    apply(simp add: sbRenameChMap_def)
    apply(subst sbGetCh_def, simp)
    apply(subst rep_abs, simp add: t10)
    apply(simp add: MapIdFunct_def map_inverse_def f1)
    by(simp add: f2)
qed
    
section \<open> SPF Definitions \<close>
  
definition idC :: "nat SPF" where
"idC \<equiv> SPF1x1 sb_id (c1, c3)"

definition append0C :: "nat SPF" where
"append0C \<equiv> SPF1x1 (appendElem2 0) (c2,c4)"

definition addC :: "nat SPF" where
"addC \<equiv> SPF2x1 add (c3, c4, c5)" 

abbreviation innerSum4SPF :: "nat SPF" where
  "innerSum4SPF \<equiv> ((idC \<parallel> append0C) \<circ> addC)"

definition sum4SPF :: "nat SPF" where
"sum4SPF \<equiv> spfFeedbackOperator_new ((idC \<parallel> append0C) \<circ> addC) [c5 \<mapsto> c2]"

abbreviation innerFeedbackSum4SPF :: "nat SPF" where
"innerFeedbackSum4SPF \<equiv> (spfRename innerSum4SPF [c5 \<mapsto> c2])"

subsection \<open> requirements \<close>

lemma [simp]: "spfDom\<cdot>idC = {c1}"
  by(auto simp add: idC_def SPF1x1_dom)
    
lemma [simp]: "spfRan\<cdot>idC = {c3}"
  by(auto simp add: idC_def SPF1x1_ran)

lemma [simp]: "spfDom\<cdot>append0C = {c2}"
  by(auto simp add: append0C_def SPF2x1_dom)
    
lemma [simp]: "spfRan\<cdot>append0C = {c4}"
  by(auto simp add: append0C_def SPF2x1_ran)

lemma [simp]: "spfDom\<cdot>addC = {c3, c4}"
  by(auto simp add: addC_def SPF1x1_dom)
    
lemma [simp]: "spfRan\<cdot>addC = {c5}"
  by(auto simp add: addC_def SPF1x1_ran)    
    
lemma [simp]: "I idC append0C = {c1, c2}"
by (auto simp add: I_def)

lemma [simp]: "Oc idC append0C = {c3, c4}"
by (auto simp add: Oc_def)

lemma [simp]: "L idC append0C = {}"
by (auto simp add: L_def)

lemma [simp]: "spfComp_well idC append0C"
by (simp add: spfComp_well_def)  
  
lemma domIdAppend[simp]: "spfDom\<cdot>(idC \<parallel> append0C) = {c1, c2}"
apply(subst parCompDom, simp_all)
apply(subst spfComp_dom_I)
by simp_all

lemma ranIdAppend[simp]: "spfRan\<cdot>(idC \<parallel> append0C) = {c3, c4}"
apply(subst parCompRan, simp_all)
apply(subst spfComp_ran_Oc)
by simp_all  

lemma [simp]: "I (idC \<parallel> append0C) addC = {c1, c2}"
  by(simp add: I_def)
    
lemma [simp]: "Oc (idC \<parallel> append0C) addC = {c3, c4, c5}"
  by(auto simp add: Oc_def)

lemma [simp]: "L (idC \<parallel> append0C) addC = {c3, c4}"
  by(auto simp add: L_def) 
    
lemma [simp]: "pL (idC \<parallel> append0C) addC = {}"
  by(auto simp add: pL_def) 
  
lemma domInnerSum4SPF[simp]: "spfDom\<cdot>(innerSum4SPF) = {c1, c2}"
  sorry

lemma ranInnerSum4SPF[simp]: "spfRan\<cdot>(innerSum4SPF) = {c3, c4, c5}"
  sorry 

lemma domInnerFeedbackSum4SPF: "spfDom\<cdot>(innerFeedbackSum4SPF) = {c1, c5}"
  sorry   

lemma ranInnerFeedbackSum4SPF: "spfRan\<cdot>(innerFeedbackSum4SPF) = {c5}"
  sorry
    
lemma ranInnerFeedbackSum4SPF_sb: assumes "sbDom\<cdot>sb = {c5}" shows "sbDom\<cdot>(innerFeedbackSum4SPF\<rightleftharpoons>sb) = spfRan\<cdot>(innerFeedbackSum4SPF)"
  sorry
  
lemma [simp]: "spfDom\<cdot>sum4SPF = {c1}"
sorry  

lemma [simp]: "spfDom\<cdot>sum4SPF = {c3, c4, c5}"
sorry      

  
subsection \<open> apply lemmas \<close>    

  
lemma innerSum4SPF_c5_eq: assumes "sbDom\<cdot>sb = I (idC \<parallel> append0C) addC" shows "(innerSum4SPF \<rightleftharpoons> sb) . c5 = add\<cdot>(sb . c1)\<cdot>(\<up>0\<bullet>(sb . c2))"
proof - 
  have f1: "{c1, c2} = {c2, c1}"
    by auto
  have f2: "sbDom\<cdot>([c3 \<mapsto> sb_id\<cdot>(sb . c1)]\<Omega>) \<union> sbDom\<cdot>([c4 \<mapsto> appendElem2 0\<cdot>(sb . c2)]\<Omega>) = {c3, c4}"
    apply(simp add: sbdom_rep_eq)
    by auto
  have f3: "(([c3 \<mapsto> sb_id\<cdot>(sb . c1)]\<Omega>) \<uplus> ([c4 \<mapsto> appendElem2 0\<cdot>(sb . c2)]\<Omega>)) . c3 = sb_id\<cdot>(sb . c1)"
    apply(subst sbunion_getchL)
     apply(simp add: sbdom_rep_eq)
      by simp
  have f4: "(([c3 \<mapsto> sb_id\<cdot>(sb . c1)]\<Omega>) \<uplus> ([c4 \<mapsto> appendElem2 0\<cdot>(sb . c2)]\<Omega>)) . c4 = appendElem2 0\<cdot>(sb . c2)"
    apply(subst sbunion_getchR)
     apply(simp add: sbdom_rep_eq)
      by simp
      (* doesn't work with variables *)
    have f5: "([c3 \<mapsto> sb_id\<cdot>(sb . c1)]\<Omega>) \<uplus> ([c4 \<mapsto> appendElem2 0\<cdot>(sb . c2)]\<Omega>) 
            \<uplus> ([c5 \<mapsto> add\<cdot>(sb_id\<cdot>(sb . c1))\<cdot>(appendElem2 0\<cdot>(sb . c2))]\<Omega>) . c5
            = add\<cdot>(sb_id\<cdot>(sb . c1))\<cdot>(appendElem2 0\<cdot>(sb . c2))"
    apply(subst sbunion_getchR)
     apply(simp add: sbdom_rep_eq)
       by(simp)
  show ?thesis  
    apply(simp only: sercomp_def)
    apply(simp only: sercomp_repAbs, simp add: assms)
    apply(simp only: parcomp_def)
    apply(simp only: parcomp_repAbs, simp add: assms f1)
    apply(simp add: idC_def append0C_def addC_def)
    apply(simp add: SPF1x1_rep_eq SPF2x1_rep_eq assms)
    apply(simp add: f2 f3 f4)
    apply(simp only: f5)
    by(simp add: sb_id_def appendElem2_def)
qed  
  
lemma innerFeedbackSum4SPF_c5_eq: assumes "sbDom\<cdot>sb = {c1}" and "sbDom\<cdot>z = {c5}" shows
    "(innerFeedbackSum4SPF \<rightleftharpoons> ((sb \<uplus> z)\<bar> {c1, c5})) . c5 = add\<cdot>(sb . c1)\<cdot>(\<up>0\<bullet>(z . c5))"
proof - 
  have f1: "(sbRenameChMap ((sb \<uplus> z)\<bar>{c1, c5}) [c5 \<mapsto> c2]) . c1 = sb . c1"
    apply(simp add: assms)
    apply(subst sbRenameChMap_getCh2)
    by(simp_all add: assms)
  have f2: "(sbRenameChMap ((sb \<uplus> z)\<bar>{c1, c5}) [c5 \<mapsto> c2]) . c2 = z . c5"
    apply(simp add: assms)
    apply(subst sbRenameChMap_getCh)
      apply(simp)
      apply (metis channel.distinct(61) ranInnerFeedbackSum4SPF ranInnerSum4SPF singleton_insert_inj_eq' spfRename_spfRan)
    by (simp add: assms(2))
  have f3: "sbDom\<cdot>(sbRenameChMap ((sb \<uplus> z)\<bar>{c1, c5}) [c5 \<mapsto> c2]) = I (idC\<parallel>append0C) addC"
    apply(simp add: assms)
    apply(simp add: sbRenameChMap_sbDom assms)
    by auto
  show ?thesis 
  apply(simp only: spfRename_def)
  apply(subst spfRename_RepAbs) 
    apply(simp add: assms)
    apply(subst innerSum4SPF_c5_eq)
     apply(simp add: f3)
    apply(subst f1)
    apply(subst f2)
      by auto
qed
    
  
section \<open> eq proof \<close>

  
lemma t5: assumes "sbDom\<cdot>sb = {c1}" shows 
    "cont (\<lambda> z. (innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> z)\<bar> {c1, c5})))"
  by (metis domInnerFeedbackSum4SPF spfFeedH_cont)

lemma t4: assumes "sbDom\<cdot>sb = {c1}" and "sbDom\<cdot>x = {c5} " shows
    "(\<Lambda> z. (innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> z)\<bar> {c1, c5})))\<cdot>x = (\<Lambda> z. [c5 \<mapsto> add\<cdot>(sb . c1)\<cdot>(appendElem2 0\<cdot>(z . c5))]\<Omega>)\<cdot>x" 
proof - 
  have f1: "sbDom\<cdot>(innerFeedbackSum4SPF\<rightleftharpoons>(sb \<uplus> x)) = {c5}"
    by (metis channel.distinct(61) ranInnerFeedbackSum4SPF ranInnerSum4SPF singleton_insert_inj_eq' spfRename_spfRan)
  have f2: "sbDom\<cdot>([c5 \<mapsto> add\<cdot>(sb . c1)\<cdot>(appendElem2 0\<cdot>(x . c5))]\<Omega>) = {c5}"
    by(simp add: sbdom_rep_eq)
  have f3: "innerFeedbackSum4SPF\<rightleftharpoons>(sb \<uplus> x) = innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> x)\<bar> {c1, c5})"
    by (simp add: assms(1) assms(2))
  show ?thesis  
    apply(simp add: assms)
    apply(subst Abs_cfun_inverse2)
     apply(subst t5)
      apply(simp_all add: assms)
    apply(subst sb_eq, simp_all)
     apply(simp add: f1 f2)
    apply(simp add: f1)
    apply(subst f3)
    apply(subst innerFeedbackSum4SPF_c5_eq)
      by(simp_all add: assms appendElem2_def)
qed
  
lemma sbDomSB_eq: assumes "sbDom\<cdot>sb = {ch1}" shows "sb = ([ch1 \<mapsto> sb . ch1]\<Omega>)"
  apply(subst sb_eq, simp_all)
   apply (metis Rep_SB_inverse assms dom_eq_singleton_conv fun_upd_same insertI1 sbdom_insert sbgetchE)
    by (metis Rep_SB_inverse assms dom_eq_singleton_conv fun_upd_same sbdom_insert sbgetchE singletonD)

lemma t2: assumes "sbDom\<cdot>sb = {c1}" shows
  "iterate i\<cdot>(\<Lambda> z. (innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> z)\<bar> {c1, c5})))\<cdot>({c5}^\<bottom>) =  
   iterate i\<cdot>(\<Lambda> z. [c5 \<mapsto> add\<cdot>(sb . c1)\<cdot>(appendElem2 0\<cdot>(z . c5))]\<Omega>)\<cdot>({c5}^\<bottom>)"
proof (induction i)
  case 0
  then show ?case 
    by(simp add: iterate_def)
next
  case (Suc i)
  have f2: "sbfun_io_eq (iterate i\<cdot>(\<Lambda> z. (innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> z)\<bar> {c1, c5})))) {c5}"
    proof (induction i)
      case 0
      then show ?case
        by(simp)
    next
      have f3: "sbDom\<cdot>z = {c5} \<Longrightarrow> sbDom\<cdot>((innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> z)\<bar> {c1, c5}))) = {c5}"
        by (metis Int_insert_right domInnerFeedbackSum4SPF hidespfwell_helper ranInnerFeedbackSum4SPF ranInnerFeedbackSum4SPF_sb sbrestrict_sbdom sbunion_restrict)
      case (Suc i)
      then show ?case
        apply(subst iterate_Suc)
        apply(subst Abs_cfun_inverse2)
         apply(subst t5, simp add: assms, simp)
          by (smt domInnerFeedbackSum4SPF option.collapse ranInnerFeedbackSum4SPF ranInnerFeedbackSum4SPF_sb sbunion_restrict spfdom2sbdom spfran2sbdom)
    qed       
  show ?case 
    apply(subst iterate_Suc)
    apply(simp)
    apply(subst (1) t4)
     apply(simp_all add: f2 assms)
      using Suc.IH by presburger
qed

lemma spf_gen_fix_sb_eq_lub: assumes "sbDom\<cdot>sb = {c1}" shows
   "(\<Squnion>i. iterate (i)\<cdot>(\<Lambda> z. ([c5 \<mapsto> add\<cdot>(sb . c1)\<cdot>((appendElem2 0)\<cdot>(z . c5))]\<Omega>))\<cdot>({c5}^\<bottom>)) . c5
    = (\<Squnion>i. iterate (i)\<cdot>(\<Lambda> z. ([c5 \<mapsto> add\<cdot>(sb . c1)\<cdot>((appendElem2 0)\<cdot>(z . c5))]\<Omega>))\<cdot>({c5}^\<bottom>) . c5)"
   by (simp add: spf_feed_sb_inout1_lub_getch)
     
lemma spf_gen_fix_sb_eq: assumes "sbDom\<cdot>sb = {c1}" shows
   "(gen_fix add (appendElem2 0))\<cdot>(sb . c1) = 
  (\<Squnion>i. iterate (i)\<cdot>(\<Lambda> z. ([c5 \<mapsto> add\<cdot>(sb . c1)\<cdot>((appendElem2 0)\<cdot>(z . c5))]\<Omega>))\<cdot>({c5}^\<bottom>)) . c5"
  apply(simp)
  apply(subst spf_gen_fix_sb_eq_lub, simp add: assms)
    using spf_feed_sb_inout1_iter_eq by auto
    
lemma spf_spfFeedH_sb_eq: assumes "sbDom\<cdot>sb = {c1}" shows
   "(\<Squnion>i. iter_sbfix (spfFeedH (spfRename innerSum4SPF [c5 \<mapsto> c2])) i {c5} sb) . c5 = 
  (\<Squnion>i. iterate (i)\<cdot>(\<Lambda> z. (innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> z)\<bar> {c1, c5})))\<cdot>({c5}^\<bottom>)) . c5"
  apply(simp add: spfFeedH_def)
    by(simp add: domInnerFeedbackSum4SPF)
 
lemma iter_spfCompH3_eq_iter_sbfix_spfFeedH: assumes "sbDom\<cdot>sb = {c1}" shows
  "(\<Squnion>i. iter_sbfix (spfFeedH (spfRename innerSum4SPF [c5 \<mapsto> c2])) i {c5} sb) . c5
    =  (gen_fix add (appendElem2 0))\<cdot>(sb . c1)" 
  apply(subst spf_gen_fix_sb_eq, simp add: assms)
  apply(subst spf_spfFeedH_sb_eq, simp add: assms)
    by (simp add: assms t2)
      
      
section \<open> result \<close>
  
lemma finalLemma: assumes "sbDom\<cdot>sb = spfDom\<cdot>sum4SPF" shows "(sum4SPF \<rightleftharpoons> sb) . c5 =  sum4\<cdot>(sb . c1)"
proof -
  have f1: "{c1} = {c1, c5} - {c5}"
    by auto
  have f2: "sum4\<cdot>(sb . c1) = (gen_fix add (appendElem2 0))\<cdot>(sb . c1)"
    by (simp add: sum4_def appendElem2_def fix_def)
  show ?thesis
    apply(simp only: sum4SPF_def)
    apply(simp only: spfFeedbackOperator_new_def)
    apply(subst spfFeedbackOperator2_iter_spfFeedH)
    apply(simp add: assms)
    apply(simp add: domInnerFeedbackSum4SPF ranInnerFeedbackSum4SPF)
    apply(subst f1, simp, subst f1, simp) (* why isn't this directly solved by simp add: f1 or auto? *)
    apply(subst f2)
    apply(subst iter_spfCompH3_eq_iter_sbfix_spfFeedH)
      by(simp_all add: assms)
qed
      
end