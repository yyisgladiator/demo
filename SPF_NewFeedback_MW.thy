theory SPF_NewFeedback_MW
imports "CaseStudies/StreamCase_Study" SPF_Comp SPF_Templates SPF_FeedComp SPF_Feedback_JB 

begin

section \<open>Feedback Definitions\<close>


definition mapIdFunct :: "(channel \<rightharpoonup> channel) \<Rightarrow> channel \<Rightarrow> channel" where
"mapIdFunct m \<equiv> (\<lambda> c. case m c of None \<Rightarrow> c | Some y \<Rightarrow> y )" 
 
definition map_inverse :: "(channel \<rightharpoonup> channel) \<Rightarrow> (channel \<rightharpoonup> channel)" where
"map_inverse m \<equiv> (\<lambda>x. if (x \<in> (ran m)) then Some ((\<lambda> y. (THE z. m z = Some y)) x) else None)"
    
definition sbRenameChMap :: "'m SB \<Rightarrow> (channel \<rightharpoonup> channel) \<Rightarrow> 'm SB" where
"sbRenameChMap sb m \<equiv> Abs_SB (\<lambda>c. if (c \<in> (sbDom\<cdot>sb \<inter> dom(m) - ran(m))) then None else Rep_SB(sb)((mapIdFunct (map_inverse m))(c)))"  
  
definition spfRename :: "'a SPF \<Rightarrow> (channel \<rightharpoonup> channel) \<Rightarrow> 'a SPF" where
"spfRename f m \<equiv> Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m)) \<leadsto> (f \<rightleftharpoons> (sbRenameChMap sb m)))" 
  
definition spfFeedbackOperator_new :: "'a SPF \<Rightarrow> (channel \<rightharpoonup> channel) \<Rightarrow> 'a SPF" where
"spfFeedbackOperator_new f m \<equiv> spfFeedbackOperator (spfRename f m)"   

definition map_injective :: "(channel \<rightharpoonup> channel) \<Rightarrow> bool" where
"map_injective m \<longleftrightarrow> (\<forall> x \<in> dom(m). \<forall> y \<in> dom(m). m x = m y \<longrightarrow> x = y)"

definition rename_map_well :: "'m SB \<Rightarrow> (channel \<rightharpoonup> channel) \<Rightarrow> bool" where
"rename_map_well sb m \<longleftrightarrow> map_injective m \<and> (dom(m) \<subseteq> sbDom\<cdot>sb)"
  
subsection \<open>map_inverse\<close>
  
  


  
subsection \<open>sbRenameChMap\<close>
  
 
lemma t10: assumes "map_injective m" 
  shows "sb_well (\<lambda>c. if (c \<in> (sbDom\<cdot>sb \<inter> dom(m) - ran(m))) then None else Rep_SB(sb)((mapIdFunct (map_inverse m))(c)))" 
  sorry
    
lemma t13: assumes "map_injective m" 
  shows "sb_well (\<lambda>c. if (c \<in> sbDom\<cdot>sb \<and> c \<in> dom m \<and> c \<notin> ran m) then None else Rep_SB(sb)((mapIdFunct (map_inverse m))(c)))" 
  sorry

lemma t11: assumes "map_injective m" and "c \<notin> ran(m)" shows "(mapIdFunct (map_inverse m) c) = c"
  apply(simp add: mapIdFunct_def map_inverse_def)
  by (simp add: assms)
    
lemma t12: assumes "map_injective m" and "(m ch1) = Some ch2" shows "(mapIdFunct (map_inverse m) ch2) = ch1"
proof - 
  have f1: "ch2 \<in> ran m"
    by (meson assms ranI)
  show ?thesis
    using f1 apply(simp add: mapIdFunct_def map_inverse_def)
    proof -
      have "\<And>c. \<not> map_injective m \<or> ch1 \<notin> dom m \<or> c \<notin> dom m \<or> m c \<noteq> Some ch2 \<or> c = ch1"
        by (metis assms(2) map_injective_def)
      then have f1: "\<And>c. ch1 \<notin> dom m \<or> c \<notin> dom m \<or> m c \<noteq> Some ch2 \<or> c = ch1"
        by (metis assms(1))
      obtain cc :: "(channel \<Rightarrow> bool) \<Rightarrow> channel \<Rightarrow> channel" where
        f2: "\<And>p c. (\<not> p c \<or> p (cc p c) \<or> The p = c) \<and> (\<not> p c \<or> cc p c \<noteq> c \<or> The p = c)"
        by (metis (no_types) the_equality)
      then have "\<And>c. m c \<noteq> Some ch2 \<or> ch1 \<notin> dom m \<or> cc (\<lambda>c. m c = Some ch2) c \<notin> dom m \<or> (THE c. m c = Some ch2) = c \<or> cc (\<lambda>c. m c = Some ch2) c = ch1"
        using f1 by meson
      then have "\<And>c. m c \<noteq> Some ch2 \<or> ch1 \<notin> dom m \<or> m (cc (\<lambda>c. m c = Some ch2) c) = None \<or> (THE c. m c = Some ch2) = c \<or> cc (\<lambda>c. m c = Some ch2) c = ch1"
        by (simp add: domIff)
      then have "\<And>c. m c \<noteq> Some ch2 \<or> ch1 \<notin> dom m \<or> Some ch2 = None \<or> (THE c. m c = Some ch2) = c \<or> cc (\<lambda>c. m c = Some ch2) c = ch1"
        using f2 by (metis (mono_tags, lifting))
      then have f3: "\<And>c. m c \<noteq> Some ch2 \<or> ch1 \<notin> dom m \<or> (THE c. m c = Some ch2) = c \<or> cc (\<lambda>c. m c = Some ch2) c = ch1"
        by (simp add: option.distinct(1))
      have "m ch1 = Some ch2 \<and> ch1 \<in> dom m \<and> (THE c. m c = Some ch2) \<noteq> ch1 \<or> (THE c. m c = Some ch2) = ch1"
        by (simp add: assms(2) domIff)
      then show "(THE c. m c = Some ch2) = ch1"
        using f3 f2 by meson
    qed
qed
    
lemma sbRenameChMap_getCh: assumes "(m ch1) = Some ch2" and "map_injective m" shows "(sbRenameChMap sb m) . ch2 = sb . ch1"
proof - 
  have f1: "ch2 \<in> ran m"
    by (meson assms ranI)
  have f2: " Rep_SB sb \<rightharpoonup> ch1 = sb . ch1"
    by (simp add: sbGetCh_def)
  have f3: "(THE z. (m z = Some ch2)) = ch1"
    proof -
      have f1: "\<And>c. ch1 \<notin> dom m \<or> c \<notin> dom m \<or> m c \<noteq> Some ch2 \<or> c = ch1"
        by (metis assms(1) assms(2) map_injective_def)
      have f2: "ch1 \<in> dom m"
        using assms(1) by blast
      obtain cc :: "(channel \<Rightarrow> bool) \<Rightarrow> channel \<Rightarrow> channel" where
        f3: "\<And>p c. (\<not> p c \<or> p (cc p c) \<or> The p = c) \<and> (\<not> p c \<or> cc p c \<noteq> c \<or> The p = c)"
        by (metis (no_types) the_equality)
      then have "\<And>c. m c \<noteq> Some ch2 \<or> ch1 \<notin> dom m \<or> cc (\<lambda>c. m c = Some ch2) c \<notin> dom m \<or> (THE c. m c = Some ch2) = c \<or> cc (\<lambda>c. m c = Some ch2) c = ch1"
        using f1 by meson
      then have "\<And>c. m c \<noteq> Some ch2 \<or> ch1 \<notin> dom m \<or> m (cc (\<lambda>c. m c = Some ch2) c) = None \<or> (THE c. m c = Some ch2) = c \<or> cc (\<lambda>c. m c = Some ch2) c = ch1"
        by blast
      then have "\<And>c. m c \<noteq> Some ch2 \<or> ch1 \<notin> dom m \<or> Some ch2 = None \<or> (THE c. m c = Some ch2) = c \<or> cc (\<lambda>c. m c = Some ch2) c = ch1"
        using f3 by (metis (mono_tags, lifting))
      then have "\<And>c. m c \<noteq> Some ch2 \<or> ch1 \<notin> dom m \<or> (THE c. m c = Some ch2) = c \<or> cc (\<lambda>c. m c = Some ch2) c = ch1"
        by blast
      then show ?thesis
        using f3 f2 by (meson assms(1))
    qed
  show ?thesis  
    apply(simp only: sbRenameChMap_def)
    apply(simp add: sbGetCh_def)
    apply(subst rep_abs)
    apply(simp add: t13 assms)
    apply(simp add: mapIdFunct_def map_inverse_def f1)
    by(simp add: f3 f2)
qed
    
lemma sbRenameChMap_getCh2: assumes "\<not>(\<exists> ch2. ((m ch2) = Some ch1))" and "ch1 \<notin> (sbDom\<cdot>sb \<inter> dom(m) - ran(m))" and "map_injective m" 
                            shows "(sbRenameChMap sb m) . ch1 = sb . ch1" 
proof - 
  have f1: "ch1 \<notin> ran m"
    by (meson assms ran2exists)
  have f2: " Rep_SB sb \<rightharpoonup> ch1 = sb . ch1"
    by (simp add: sbGetCh_def)
  have f3: "(ch1 \<in> sbDom\<cdot>sb \<and> ch1 \<in> dom m \<and> ch1 \<notin> ran m) = False"
    using assms(2) by auto
  show ?thesis  
    apply(simp add: sbRenameChMap_def)
    apply(subst sbGetCh_def, simp)
    apply(subst rep_abs)
     apply(simp add: t13 assms)
      apply(simp add: f3)
    apply(simp add: mapIdFunct_def map_inverse_def f1)
    by(simp add: f2)
qed  

lemma sbRenameChMap_sbDom: assumes "rename_map_well sb m" shows "sbDom\<cdot>(sbRenameChMap sb m) = (sbDom\<cdot>sb - dom(m)) \<union> ran(m)"
proof - 
  have f0: "map_injective m"
    using assms rename_map_well_def by auto
  have f11: "\<And>x. (x \<in> ran m \<longrightarrow> (THE z. m z = Some x) \<in> dom(m))"
    using f0 mapIdFunct_def map_inverse_def ran2exists t12 by fastforce
  have f12: "\<And>x. (x \<in> ran m \<longrightarrow> (THE z. m z = Some x) \<in> sbDom\<cdot>sb)"
    using assms f11 rename_map_well_def by blast
  have f1: "\<And>x. (x \<in> ran m \<longrightarrow> (\<exists>y. Rep_SB sb (THE z. m z = Some x) = Some y))"
    by (metis f12 sbgetchE)
  have f21: "\<And>x. (x \<in> dom m \<longrightarrow> x \<in> sbDom\<cdot>sb)"
    using assms rename_map_well_def by auto
  have f2: "\<And>x. (x \<notin> ran m \<longrightarrow> (x \<in> dom m \<longrightarrow> x \<notin> sbDom\<cdot>sb) \<longrightarrow> (\<exists>y. Rep_SB sb x = Some y) = (x \<in> sbDom\<cdot>sb \<and> x \<notin> dom m))"
    apply(simp add: f21)
    using sbdom_insert by fastforce
  show ?thesis
    apply(simp add: sbRenameChMap_def)
    apply(subst sbDom_def, simp add: t10)
    apply(subst rep_abs)
    apply(simp add: t13 f0 map_inverse_def)
    apply(simp only: mapIdFunct_def f0 map_inverse_def)
    apply(subst dom_def)
    apply(subst set_eqI)
    apply(simp_all)
     using f1 f2 by auto 
qed
  
  
subsection \<open>spfRename\<close>

  
lemma spfRename_cont: "cont (\<lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m)) \<leadsto> (f \<rightleftharpoons> (sbRenameChMap sb m)))"
  sorry
    
lemma spfRename_spf_well: "spf_well (\<Lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m)) \<leadsto> (f \<rightleftharpoons> (sbRenameChMap sb m)))"
  apply(simp add: spf_well_def spfRename_cont)
  apply(simp only: domIff2)
  apply(simp add: sbdom_rep_eq)
  sorry
    
lemma spfRename_RepAbs: "Rep_CSPF (Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m)) \<leadsto> (f \<rightleftharpoons> (sbRenameChMap sb m)))) = 
  (\<lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m)) \<leadsto> (f \<rightleftharpoons> (sbRenameChMap sb m)))"
  by(simp add: spfRename_cont spfRename_spf_well)
    
lemma spfRename_spfDom: "spfDom\<cdot>(spfRename f m) = (spfDom\<cdot>f - ran(m)) \<union> dom(m)"
  apply(simp add: spfRename_def)
  apply(subst spfDomAbs)
    by (simp_all add: spfRename_cont spfRename_spf_well)

lemma spfRename_spfRan: "spfRan\<cdot>(spfRename f m) = spfRan\<cdot>f"
  sorry  

    
subsection \<open>spfFeedbackOperator_new\<close>
  
  
lemma spfFeedbackOperator_new_spfDom: "spfDom\<cdot>(spfFeedbackOperator_new f m) = (spfDom\<cdot>f - ran(m)) \<union> dom(m)"
  apply(simp add: spfFeedbackOperator_new_def)
  apply(simp add: spfRename_spfDom spfRename_spfRan)
  sorry

lemma spfFeedbackOperator_new_spfRan: "spfRan\<cdot>(spfFeedbackOperator_new f m) = spfRan\<cdot>f"
  sorry   
  
  
section \<open>General lemmas parcomp and sercomp\<close>  

  
(* Should already be proven somewhere*)  
lemma parcomp_cont[simp]: "cont (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))"
  sorry  
  
lemma parcomp_spf_well[simp]: "spf_well (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))"  
  apply(simp add: spf_well_def)
  apply(simp only: domIff2)
  apply(simp add: sbdom_rep_eq)
  by(auto) 

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
    
  
section \<open>SPF Definitions\<close>

  
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
  
  
subsection \<open>Requirements\<close>

subsubsection \<open>spfDom, spfRan\<close>

  
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
  
  
subsubsection \<open>Composition par\<close>

  
lemma [simp]: "I idC append0C = {c1, c2}"
by (auto simp add: I_def)

lemma [simp]: "Oc idC append0C = {c3, c4}"
by (auto simp add: Oc_def)

lemma [simp]: "L idC append0C = {}"
by (auto simp add: L_def)  

lemma [simp]: "spfComp_well idC append0C"
  by (simp add: spfComp_well_def) 
    

subsubsection \<open>spfDom, spfRan\<close>
  
  
lemma domIdAppend[simp]: "spfDom\<cdot>(idC \<parallel> append0C) = {c1, c2}"
apply(subst parCompDom, simp_all)
apply(subst spfComp_dom_I)
by simp_all

lemma ranIdAppend[simp]: "spfRan\<cdot>(idC \<parallel> append0C) = {c3, c4}"
apply(subst parCompRan, simp_all)
apply(subst spfComp_ran_Oc)
by simp_all    
  
    
subsubsection \<open>Composition ser\<close>
  
  
lemma [simp]: "I (idC \<parallel> append0C) addC = {c1, c2}"
  by(simp add: I_def)
    
lemma [simp]: "Oc (idC \<parallel> append0C) addC = {c3, c4, c5}"
  by(auto simp add: Oc_def)

lemma [simp]: "L (idC \<parallel> append0C) addC = {c3, c4}"
  by(auto simp add: L_def) 
    
lemma [simp]: "pL (idC \<parallel> append0C) addC = {}"
  by(auto simp add: pL_def)   
  
    
subsubsection \<open>Feedback\<close>
  
  
lemma domInnerSum4SPF[simp]: "spfDom\<cdot>(innerSum4SPF) = {c1, c2}"
  sorry

lemma ranInnerSum4SPF[simp]: "spfRan\<cdot>(innerSum4SPF) = {c3, c4, c5}"
  sorry 

lemma domInnerFeedbackSum4SPF: "spfDom\<cdot>(innerFeedbackSum4SPF) = {c1, c5}"
proof -
  have f1: "\<And>z c s. z = None \<or> insert c (spfDom\<cdot>(s::nat SPF) - ran (Map.empty(c := z))) = spfDom\<cdot>(spfRename s (Map.empty(c := z)))"
    by (simp add: spfRename_spfDom sup_bot.right_neutral)
  have "c2 \<notin> {c1}"
    by blast
  then have "insert c5 ({c1, c2} - {c2}) = {c1, c5}"
    by fastforce
  then show ?thesis
    using f1 by (metis domInnerSum4SPF option.simps(3) ran_empty ran_map_upd)
qed
  

lemma ranInnerFeedbackSum4SPF: "spfRan\<cdot>(innerFeedbackSum4SPF) = {c3, c4, c5}"
  by (simp add: spfRename_spfRan)
    
lemma ranInnerFeedbackSum4SPF_sb: assumes "sbDom\<cdot>sb = {c1, c5}" shows "sbDom\<cdot>(innerFeedbackSum4SPF\<rightleftharpoons>sb) = spfRan\<cdot>(innerFeedbackSum4SPF)"
  sorry
  
lemma [simp]: "spfDom\<cdot>sum4SPF = {c1}"
  sorry  

lemma [simp]: "spfRan\<cdot>sum4SPF = {c3, c4, c5}"
  sorry  
  
  
subsubsection \<open>Apply lemmas\<close>
  
  
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
  
lemma innerFeedbackSum4SPF_c5_eq: assumes "sbDom\<cdot>sb = {c1}" and "c5 \<in> sbDom\<cdot>z" shows
    "(innerFeedbackSum4SPF \<rightleftharpoons> ((sb \<uplus> z)\<bar> {c1, c5})) . c5 = add\<cdot>(sb . c1)\<cdot>(\<up>0\<bullet>(z . c5))"
proof - 
  have f0: "insert c5 ({c1, c2} - {c2}) = {c1, c5}"
    by auto
  have f1: "(sbRenameChMap ((sb \<uplus> z)\<bar>{c1, c5}) [c5 \<mapsto> c2]) . c1 = sb . c1"
    sorry
    (*apply(simp add: assms)
    apply(subst sbRenameChMap_getCh2)
    by(simp_all add: assms map_injective_def)*)
  have f2: "(sbRenameChMap ((sb \<uplus> z)\<bar>{c1, c5}) [c5 \<mapsto> c2]) . c2 = z . c5"
    sorry
    (*apply(simp add: assms)
    apply(subst sbRenameChMap_getCh)
    apply(simp)
    by (simp_all add: assms(2) map_injective_def)*)
  have f3: "sbDom\<cdot>(sbRenameChMap ((sb \<uplus> z)\<bar>{c1, c5}) [c5 \<mapsto> c2]) = I (idC\<parallel>append0C) addC"
    apply(simp add: assms)
    apply(subst sbRenameChMap_sbDom)
     apply(simp_all add: rename_map_well_def map_injective_def assms)
    by auto
  show ?thesis 
  apply(simp only: spfRename_def)
  apply(subst spfRename_RepAbs) 
    apply(simp add: assms)
    apply(subst innerSum4SPF_c5_eq)
     apply (metis (no_types, lifting) Diff_insert_absorb channel.distinct(1) f3 insert_absorb insert_commute singleton_insert_inj_eq')
    apply(subst f0, subst f0, subst f0) (* why? *)
    apply(subst f1, subst f2)
      by auto
qed  

lemma innerFeedbackSum4SPF_c3_eq: assumes "sbDom\<cdot>sb = {c1}" and "c5 \<in> sbDom\<cdot>z" shows
    "(innerFeedbackSum4SPF \<rightleftharpoons> ((sb \<uplus> z)\<bar> {c1, c5})) . c3 = sb . c1"
  sorry
    
lemma innerFeedbackSum4SPF_c4_eq: assumes "sbDom\<cdot>sb = {c1}" and "c5 \<in> sbDom\<cdot>z" shows
    "(innerFeedbackSum4SPF \<rightleftharpoons> ((sb \<uplus> z)\<bar> {c1, c5})) . c4 = (appendElem2 0\<cdot>(z . c5))"
 sorry    
  
  
section \<open>Equality proof\<close>

(* requirements *)

lemma t6: assumes "sbDom\<cdot>sb = {c1}" shows 
    "cont (\<lambda> z. (innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> z)\<bar> {c1, c5})))"
  by (metis domInnerFeedbackSum4SPF spfFeedH_cont)  

lemma t7: assumes "sbDom\<cdot>sb = {c1}" shows 
    "cont (\<lambda> z. [c3 \<mapsto> (sb . c1), c4 \<mapsto> (appendElem2 0\<cdot>(z . c5)), c5 \<mapsto> add\<cdot>(sb . c1)\<cdot>(appendElem2 0\<cdot>(z . c5))]\<Omega>)"
  sorry    
    
lemma t5: "c5 \<in> sbDom\<cdot>(iterate i\<cdot>(\<Lambda> z. innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> z)\<bar>{c1, c5}))\<cdot>({c3, c4, c5}^\<bottom>))"  
  sorry
  
lemma t4: assumes "sbDom\<cdot>sb = {c1}" and "c5 \<in> sbDom\<cdot>x" shows
    "((\<Lambda> z. (innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> z)\<bar> {c1, c5})))\<cdot>x)= 
     ((\<Lambda> z. [c3 \<mapsto> (sb . c1), c4 \<mapsto> (appendElem2 0\<cdot>(z . c5)), c5 \<mapsto> add\<cdot>(sb . c1)\<cdot>(appendElem2 0\<cdot>(z . c5))]\<Omega>)\<cdot>x)"
proof - 
  have f1: "sbDom\<cdot>(innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> x)\<bar>{c1, c5})) = {c3, c4, c5}"
    sorry
  have f2: "sbDom\<cdot>([c3 \<mapsto> (sb . c1), c4 \<mapsto> (appendElem2 0\<cdot>(x . c5)), c5 \<mapsto> add\<cdot>(sb . c1)\<cdot>(appendElem2 0\<cdot>(x . c5))]\<Omega>) = {c3, c4, c5}"
    by(auto simp add: sbdom_rep_eq)
  show ?thesis
    apply(subst Abs_cfun_inverse2)
    apply(subst t6, simp add: assms, simp)
    apply(subst Abs_cfun_inverse2)
     apply(subst t7, simp add: assms, simp)
    apply(subst sb_eq, simp_all)
    apply(simp_all add: f1 f2)
    apply(case_tac c)
    apply(simp_all)
     apply(subst innerFeedbackSum4SPF_c3_eq, simp_all add: assms)
     apply(simp add: sbgetch_rep_eq)
      apply(subst innerFeedbackSum4SPF_c4_eq, simp_all add: assms)
      apply(simp add: sbgetch_rep_eq)
      apply(subst innerFeedbackSum4SPF_c5_eq, simp_all add: assms)
      apply(simp add: sbgetch_rep_eq)
    sorry
qed

lemma t8: assumes "sbDom\<cdot>sb = {c1}" shows 
        "sbfun_io_eq (\<Lambda> z. [c3 \<mapsto> (sb . c1), c4 \<mapsto> (appendElem2 0\<cdot>(z . c5)), c5 \<mapsto> add\<cdot>(sb . c1)\<cdot>(appendElem2 0\<cdot>(z . c5))]\<Omega>) {c3, c4, c5}"
    apply(subst Abs_cfun_inverse2)
     apply(subst t7, simp_all add: assms)
    apply(simp add: sbdom_rep_eq)
  by auto
    
lemma t22: "([c3 \<mapsto> sb . c1, c4 \<mapsto> appendElem2 0\<cdot>(z . c5), c5 \<mapsto> add\<cdot>(sb . c1)\<cdot>(appendElem2 0\<cdot>(z . c5))]\<Omega>) . c5 = 
            add\<cdot>(sb . c1)\<cdot>(appendElem2 0\<cdot>(z . c5))"    
  by (simp add: sbgetch_rep_eq)

(* iterate eq lemmas *)  
  
lemma t2: assumes "sbDom\<cdot>sb = {c1}" shows
  "(iterate i\<cdot>(\<Lambda> z. (innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> z)\<bar> {c1, c5})))\<cdot>({c3, c4, c5}^\<bottom>)) =  
   (iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> (sb . c1), c4 \<mapsto> (appendElem2 0\<cdot>(z . c5)), c5 \<mapsto> add\<cdot>(sb . c1)\<cdot>(appendElem2 0\<cdot>(z . c5))]\<Omega>)\<cdot>({c3, c4, c5}^\<bottom>))"
proof (induction i)
  case 0
  then show ?case 
    by(simp add: iterate_def)
  case (Suc i)
  then show ?case
    apply(subst iterate_Suc)
    apply(subst iterate_Suc)
    apply(subst (1) t4)
     apply(simp add: t5 assms)
     apply(simp add: t5 assms)
      by presburger
qed  


lemma t9: assumes "sbDom\<cdot>sb = {c1}" shows "iterate i\<cdot>(\<Lambda> z. add\<cdot>(sb . c1)\<cdot>(appendElem2 0\<cdot>z))\<cdot>\<epsilon> =
            iterate i\<cdot>(\<Lambda> z. [c3 \<mapsto> sb . c1, c4 \<mapsto> appendElem2 0\<cdot>(z . c5), c5 \<mapsto> add\<cdot>(sb . c1)\<cdot>(appendElem2 0\<cdot>(z . c5))]\<Omega>)\<cdot>({c3, c4, c5}^\<bottom>) . c5"
proof (induction i)
  case 0
  then show ?case
    by simp
  next
  case (Suc i)
  then show ?case
    apply (unfold iterate_Suc)
    apply(subst Abs_cfun_inverse2, simp)
    apply(subst Abs_cfun_inverse2)
    apply(subst t7, simp add: assms, simp)
    apply(subst t22)
    by presburger
qed
  
(* eq lemmas *) 
  
lemma spf_gen_fix_sb_eq: assumes "sbDom\<cdot>sb = {c1}" shows
   "(gen_fix add (appendElem2 0))\<cdot>(sb . c1) = 
    (\<Squnion>i. iterate (i)\<cdot>(\<Lambda> z. ([c3 \<mapsto> (sb . c1), c4 \<mapsto> (appendElem2 0\<cdot>(z . c5)), c5 \<mapsto> add\<cdot>(sb . c1)\<cdot>((appendElem2 0)\<cdot>(z . c5))]\<Omega>))\<cdot>({c3, c4, c5}^\<bottom>)) . c5"
apply (subst sbgetch_lub)
 apply(rule sbIterate_chain)
  apply(simp add: t8 assms)
by(simp add: t9 assms)
    
lemma spf_spfFeedH_sb_eq: assumes "sbDom\<cdot>sb = {c1}" shows
   "(\<Squnion>i. iter_sbfix (spfFeedH (spfRename innerSum4SPF [c5 \<mapsto> c2])) i {c3, c4, c5} sb) . c5 = 
    (\<Squnion>i. iterate (i)\<cdot>(\<Lambda> z. (innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> z)\<bar> {c1, c5})))\<cdot>({c3, c4, c5}^\<bottom>)) . c5"
  apply(simp add: spfFeedH_def)
  by(simp add: domInnerFeedbackSum4SPF)
  
lemma iter_spfCompH3_eq_iter_sbfix_spfFeedH: assumes "sbDom\<cdot>sb = {c1}" shows
  "(\<Squnion>i. iter_sbfix (spfFeedH (spfRename innerSum4SPF [c5 \<mapsto> c2])) i {c3, c4, c5} sb) . c5
    =  (gen_fix add (appendElem2 0))\<cdot>(sb . c1)"
proof - 
  have f1: "sbfun_io_eq (\<Lambda> z. innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> z)\<bar>{c1, c5})) {c3, c4, c5}"
    apply(subst Abs_cfun_inverse2)
     apply(subst t6, simp_all add: assms)
    apply(subst ranInnerFeedbackSum4SPF_sb)
    using assms apply auto[1]
      by (simp add: ranInnerFeedbackSum4SPF)
  show ?thesis
    apply(subst spf_gen_fix_sb_eq, simp add: assms)
    apply(subst spf_spfFeedH_sb_eq, simp add: assms)
    apply(subst sbgetch_lub)
     apply(rule sbIterate_chain)
      apply(simp add: f1)
    apply(subst sbgetch_lub)
     apply(rule sbIterate_chain)
     apply(simp add: t8 assms sbdom_rep_eq)
    by (simp add: assms t2)  
qed
  
  
section \<open>Final lemma\<close>  
  
  
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
    apply(simp add: f1)
    apply(subst f2)
    apply(subst iter_spfCompH3_eq_iter_sbfix_spfFeedH)
      by(simp_all add: assms)
qed
  
  
end