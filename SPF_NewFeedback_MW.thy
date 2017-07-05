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

definition sb_rename_map_well :: "'m SB \<Rightarrow> (channel \<rightharpoonup> channel) \<Rightarrow> bool" where
"sb_rename_map_well sb m \<longleftrightarrow> (map_injective m \<and> (dom(m) \<subseteq> sbDom\<cdot>sb))"

definition spf_rename_map_well :: "'m SPF \<Rightarrow> 'm SB \<Rightarrow> (channel \<rightharpoonup> channel) \<Rightarrow> bool" where 
"spf_rename_map_well f sb m \<longleftrightarrow> map_injective m \<and> sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m) \<and> spfDom\<cdot>f = (sbDom\<cdot>sb - dom(m)) \<union> ran(m)"

definition spf_map_well :: "'m SPF \<Rightarrow> (channel \<rightharpoonup> channel) \<Rightarrow> bool" where 
"spf_map_well f m \<longleftrightarrow> map_injective m \<and> (dom(m) \<inter> spfDom\<cdot>f = {}) \<and> (ran(m) \<subseteq> spfDom\<cdot>f)"


subsection \<open>map_inverse\<close>
  
  
lemma t32: assumes "map_injective m" and "c \<in> ran(m)"
  shows "\<exists> x. (THE z. m z = Some c) = x"
  by simp


  
subsection \<open>sbRenameChMap\<close>

  
(*
  have f1: "ch \<in> ((sbDom\<cdot>sb - dom(m)) \<union> {c \<in> ran(m). \<exists> x. sb . c = x}) \<longrightarrow>
          (\<lambda>c. if (c \<in> (sbDom\<cdot>sb \<inter> dom(m) - ran(m))) then None else Rep_SB(sb)((mapIdFunct (map_inverse m))(c))) ch \<noteq> None"
    sorry
  have f2: "ch \<notin> ((sbDom\<cdot>sb - dom(m)) \<union> {c \<in> ran(m). \<exists> x. sb . c = x}) \<longrightarrow>
          (\<lambda>c. if (c \<in> (sbDom\<cdot>sb \<inter> dom(m) - ran(m))) then None else Rep_SB(sb)((mapIdFunct (map_inverse m))(c))) ch = None" 
    sorry
*)
  
lemma t31: assumes "map_injective m" 
  shows "dom (\<lambda>c. if (c \<in> (sbDom\<cdot>sb \<inter> dom(m) - ran(m))) then None else Rep_SB(sb)((mapIdFunct (map_inverse m))(c))) 
      = (((sbDom\<cdot>sb - dom(m)) - ran(m)) \<union> {c \<in> ran(m). (THE z. m z = Some c) \<in> sbDom\<cdot>sb})"  
  sorry
      
lemma t30: assumes "map_injective m" and "c \<in> (((sbDom\<cdot>sb - dom(m)) - ran(m)) \<union> {c \<in> ran(m). (THE z. m z = Some c) \<in> sbDom\<cdot>sb})" 
  shows "sdom\<cdot>((\<lambda>c. if (c \<in> (sbDom\<cdot>sb \<inter> dom(m) - ran(m))) then None else Rep_SB(sb)((mapIdFunct (map_inverse m))(c)))\<rightharpoonup>c) \<subseteq> ctype c"  
proof - 
  have f1: "\<not>(c \<in> sbDom\<cdot>sb \<and> c \<in> dom m \<and> c \<notin> ran m)"
    apply(simp)
    using assms(2) by blast
  (*have f20: "c \<in> ran(m) \<longrightarrow> c \<in> {c \<in> ran(m). (THE z. m z = Some c) \<in> sbDom\<cdot>sb}"
    using assms(2) by auto
  have f21: "c \<in> ran(m) \<longrightarrow> (THE z. m z = Some c) \<in> sbDom\<cdot>sb"
    using f20 by auto*)
  have f22: "\<And>ch. (THE z. m z = Some c) = ch \<longrightarrow>  sdom\<cdot>((Rep_SB sb)\<rightharpoonup>ch) \<subseteq> ctype c"
    sorry
  have f2: "sdom\<cdot>Rep_SB sb\<rightharpoonup>mapIdFunct (map_inverse m) c \<subseteq> ctype c"
    apply(case_tac "c \<notin> ran(m)")
     apply(simp add: mapIdFunct_def map_inverse_def)
      apply (metis (no_types, lifting) Abs_cfun_inverse2 Diff_subset Un_iff assms(2) mem_Collect_eq rep_well sbDom_def sb_well_def sbdom_cont subsetCE)
    apply(simp add: mapIdFunct_def map_inverse_def)
    apply(subst f22)
      by(simp_all)
  show ?thesis  
    apply(simp add: assms f1)
    by(simp add: f2)  
qed
    
lemma t10: assumes "map_injective m" 
  shows "sb_well (\<lambda>c. if (c \<in> (sbDom\<cdot>sb \<inter> dom(m) - ran(m))) then None else Rep_SB(sb)((mapIdFunct (map_inverse m))(c)))" 
  apply(simp only: sb_well_def)
  apply(subst t31, simp add: assms)
  using assms t30 by blast
    
lemma t13: assumes "map_injective m" 
  shows "sb_well (\<lambda>c. if (c \<in> sbDom\<cdot>sb \<and> c \<in> dom m \<and> c \<notin> ran m) then None else Rep_SB(sb)((mapIdFunct (map_inverse m))(c)))" 
proof - 
  have f1: " \<forall>c. (c \<in> sbDom\<cdot>sb \<and> c \<in> dom m \<and> c \<notin> ran m) = (c \<in> (sbDom\<cdot>sb \<inter> dom(m) - ran(m)))"
    by simp
  show ?thesis
    apply(subst f1)
    apply(subst t10)
    by(simp_all add: assms)
qed

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

lemma sbRenameChMap_sbDom: assumes "sb_rename_map_well sb m" shows "sbDom\<cdot>(sbRenameChMap sb m) = (sbDom\<cdot>sb - dom(m)) \<union> ran(m)"
proof - 
  have f0: "map_injective m"
    using assms sb_rename_map_well_def by auto
  have f11: "\<And>x. (x \<in> ran m \<longrightarrow> (THE z. m z = Some x) \<in> dom(m))"
    using f0 mapIdFunct_def map_inverse_def ran2exists t12 by fastforce
  have f12: "\<And>x. (x \<in> ran m \<longrightarrow> (THE z. m z = Some x) \<in> sbDom\<cdot>sb)"
    using assms f11 sb_rename_map_well_def by blast
  have f1: "\<And>x. (x \<in> ran m \<longrightarrow> (\<exists>y. Rep_SB sb (THE z. m z = Some x) = Some y))"
    by (metis f12 sbgetchE)
  have f21: "\<And>x. (x \<in> dom m \<longrightarrow> x \<in> sbDom\<cdot>sb)"
    using assms sb_rename_map_well_def by auto
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
    
lemma t40: assumes "map_injective m" and "c \<in> ((sbDom\<cdot>sb - dom(m)) - ran(m))" shows "(sbRenameChMap sb m) . c = sb . c"
proof - 
  have f1: "\<not>(c \<in> sbDom\<cdot>sb \<and> c \<in> dom m \<and> c \<notin> ran m)"
    using assms(2) by blast
  have f2: "c \<notin> ran(m)"
    using assms(2) by auto
  show ?thesis
    apply(simp add: sbRenameChMap_def)
    apply(subst sbGetCh_def, simp)
    apply(subst rep_abs)
     apply(simp add: t13 assms)
    apply(simp add: f1)
    apply(simp add: mapIdFunct_def map_inverse_def)
      apply(simp add: f2)
    by (simp add: sbgetch_insert) 
qed
    
(* can be removed later *)    
lemma t41: assumes "map_injective m" and "m x = Some c" and "x \<in> sbDom\<cdot>sb" shows "(sbRenameChMap sb m) . c = sb . x"
  by(simp add: sbRenameChMap_getCh assms)

(* a more general version of sbRenameChMap_sbDom *)
lemma sbRenameChMap_sbDom2: assumes "map_injective m" 
  shows "sbDom\<cdot>(sbRenameChMap sb m) = (((sbDom\<cdot>sb - dom(m)) - ran(m)) \<union> {c \<in> ran(m). (THE z. m z = Some c) \<in> sbDom\<cdot>sb})"
proof - 
  show ?thesis
    apply(simp add: sbRenameChMap_def)
    apply(subst sbDom_def, simp add: t10)
    apply(subst rep_abs)
    apply(simp add: t13 assms)
    apply(simp only: mapIdFunct_def map_inverse_def)
    apply(subst dom_def)
    apply(subst set_eqI)
     apply(simp_all)
    apply(case_tac "x \<in> ((sbDom\<cdot>sb - dom(m)) - ran(m))")
     apply(simp)
    apply (metis (no_types) sbgetchE)
    apply(simp)
    using sbdom_insert by fastforce
qed
    
lemma sbRenameChMap_cont: assumes "map_injective m" shows "cont (\<lambda> sb. (sbRenameChMap sb m))"
proof - 
  have f00: "\<forall>x y. x \<sqsubseteq> y \<longrightarrow>  sbDom\<cdot>x = sbDom\<cdot>y" 
    using sbdom_eq by blast
  have f01: "\<forall>x y. x \<sqsubseteq> y \<longrightarrow> sbDom\<cdot>(sbRenameChMap x m) = sbDom\<cdot>(sbRenameChMap y m)"
    by (metis (mono_tags, lifting) Collect_cong assms f00 sbRenameChMap_sbDom2)
  have f02: "\<forall>x y c. x \<sqsubseteq> y \<longrightarrow>  c \<in> sbDom\<cdot>(sbRenameChMap x m) \<longrightarrow> (sbRenameChMap x m) . c \<sqsubseteq> (sbRenameChMap y m) . c"
    by (smt assms domIff f00 monofun_cfun_arg monofun_cfun_fun sbRenameChMap_getCh sbRenameChMap_getCh2 sbRenameChMap_sbDom2 t31)
  with f01 have f0: "monofun (\<lambda> sb. (sbRenameChMap sb m))"
    apply(simp add: monofun_def)
    by (smt f01 f02 sb_below)
  have f1: "\<And>Y. chain Y \<Longrightarrow> chain (\<lambda> i. (sbRenameChMap (Y i) m))"
    using ch2ch_monofun f0 by auto
  have f2: "\<And>Y. chain Y \<Longrightarrow> (\<Squnion>i. (sbRenameChMap (Y i) m)) = (sbRenameChMap (Lub Y) m)"
    sorry
  show ?thesis
    by (simp add: f0 f2 mycontI2)
qed  
  
  
subsection \<open>spfRename\<close>

  
lemma t21: assumes "spf_map_well f m" shows "(sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m)) \<longrightarrow> spfDom\<cdot>f = (sbDom\<cdot>sb - dom(m)) \<union> ran(m)" 
  by (smt Diff_Int Diff_cancel Diff_empty Diff_eq_empty_iff Diff_partition Diff_subset Un_Diff assms inf_sup_aci(5) spf_map_well_def)

lemma t20: assumes "spf_map_well f m" shows "(sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m)) \<longrightarrow> sbDom\<cdot>(sbRenameChMap sb m) = spfDom\<cdot>f"
  by (metis assms sbRenameChMap_sbDom sb_rename_map_well_def spf_map_well_def sup_ge2 t21)    
    
lemma spfRename_cont: assumes "spf_map_well f m" shows "cont (\<lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m)) \<leadsto> (f \<rightleftharpoons> (sbRenameChMap sb m)))"
proof - 
  have f0: "cont (\<lambda> sb. (sbRenameChMap sb m))"
    apply(subst sbRenameChMap_cont, simp_all)
    using assms spf_map_well_def by auto
  have f1: "cont (\<lambda> sb. (f \<rightleftharpoons> (sbRenameChMap sb m)))"
    by (metis (full_types) Rep_CSPF_def cont_Rep_cfun2 cont_compose f0 op_the_cont)
  show ?thesis
    using f1 by auto
qed
    
lemma spfRename_spf_well: assumes "spf_map_well f m" shows "spf_well (\<Lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m)) \<leadsto> (f \<rightleftharpoons> (sbRenameChMap sb m)))"
  apply(simp add: spf_well_def spfRename_cont assms)
  apply(simp only: domIff2)
  apply(simp add: sbdom_rep_eq)
    by (metis assms hidespfwell_helper t20)
    
lemma spfRename_RepAbs: assumes "spf_map_well f m" shows "Rep_CSPF (Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m)) \<leadsto> (f \<rightleftharpoons> (sbRenameChMap sb m)))) = 
  (\<lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - ran(m)) \<union> dom(m)) \<leadsto> (f \<rightleftharpoons> (sbRenameChMap sb m)))"
  by(simp add: spfRename_cont spfRename_spf_well assms)
    
lemma spfRename_spfDom: assumes "spf_map_well f m" shows "spfDom\<cdot>(spfRename f m) = (spfDom\<cdot>f - ran(m)) \<union> dom(m)"
  apply(simp add: spfRename_def)
  apply(subst spfDomAbs)
    by (simp_all add: spfRename_cont spfRename_spf_well assms)

lemma t23: assumes "spf_map_well f m" and "sbDom\<cdot>sb = spfDom\<cdot>f - ran m \<union> dom m" shows "((spfRename f m)\<rightleftharpoons>sb = a) \<longrightarrow> (sbDom\<cdot>a=spfRan\<cdot>f)"
  by (metis (no_types, lifting) assms(1) assms(2) hidespfwell_helper spfRename_RepAbs spfRename_def spfRename_spfDom spfran2sbdom t20)


lemma spfRename_spfRan: assumes "spf_map_well f m" shows "spfRan\<cdot>(spfRename f m) = spfRan\<cdot>f"
  by (metis assms sbleast_sbdom spfRename_spfDom spfran_least t23)

    
subsection \<open>spfFeedbackOperator_new\<close>
  
  
lemma spfFeedbackOperator_new_spfDom: assumes "spf_map_well f m" shows "spfDom\<cdot>(spfFeedbackOperator_new f m) = ((spfDom\<cdot>f - ran(m)) \<union> dom(m)) - spfRan\<cdot>f"
  apply(simp add: spfFeedbackOperator_new_def)
  by(simp add: spfRename_spfDom spfRename_spfRan assms)

lemma spfFeedbackOperator_new_spfRan: assumes "spf_map_well f m" shows "spfRan\<cdot>(spfFeedbackOperator_new f m) = spfRan\<cdot>f"
  by (simp add: spfFeedbackOperator_new_def spfRename_spfRan assms) 
  
  
section \<open>General lemmas parcomp and sercomp\<close>  

  
(* Should already be proven somewhere*)  
lemma parcomp_cont[simp]: "cont (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))"
proof - 
  have  "cont (\<lambda>s. (Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))"
    by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
  then have f1: "cont (\<lambda>x. (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)))"
    by (metis Rep_CSPF_def)
  have f3: "cont (\<lambda>x. (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f2)))"
  proof -
    have f1: "\<And>s. cont (\<lambda>sa. s::'a SPF\<rightleftharpoons>(sa\<bar>spfDom\<cdot>s))"
      using Rep_CSPF_def contSPFRestrict by auto
    have "\<not> cont (\<lambda>s. (f2\<rightleftharpoons>(s\<bar>spfDom\<cdot>f2))) \<or> \<not> cont (\<lambda>s. sbUnion\<cdot> (f1\<rightleftharpoons>(s\<bar>spfDom\<cdot>f1))) \<or> cont (\<lambda>s. (f1\<rightleftharpoons>(s\<bar>spfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(s\<bar>spfDom\<cdot>f2)))"
      using cont2cont_APP by blast
    then have ?thesis
      using f1 cont_Rep_cfun2 cont_compose by blast
    then show ?thesis
      by force
  qed
  show ?thesis
    apply(subst if_then_cont)
    by (simp_all add: f3)
qed
  
lemma parcomp_spf_well[simp]: "spf_well (\<Lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))"  
  apply(simp add: spf_well_def)
  apply(simp only: domIff2)
  apply(simp add: sbdom_rep_eq)
  by(auto) 

lemma sercomp_cont[simp]: "cont (\<lambda> x. (sbDom\<cdot>x =  spfDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
proof -
  have "cont (the::'a SB option \<Rightarrow> _) \<and> cont (\<lambda>s. Rep_SPF f2\<cdot>Rep_cfun (Rep_SPF f1)\<rightharpoonup>s)"
    by (metis cont_Rep_cfun2 cont_compose op_the_cont)
  then have "cont (\<lambda>s. Rep_cfun (Rep_SPF f2)\<rightharpoonup>Rep_cfun (Rep_SPF f1)\<rightharpoonup>s)"
    by (metis cont_compose)
  then have "cont (\<lambda>s. (sbDom\<cdot>s = spfDom\<cdot> f1)\<leadsto>((Rep_cfun (Rep_SPF f2))\<rightharpoonup>((Rep_cfun (Rep_SPF f1))\<rightharpoonup>s)))"
    using if_then_cont by blast
  then show ?thesis
    by (metis (no_types) Rep_CSPF_def)
qed
  
lemma sercomp_spf_well[simp]: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" shows "spf_well (\<Lambda> x. (sbDom\<cdot>x =  spfDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"  
  apply(simp add: spf_well_def)
  apply(simp only: domIff2)
  apply(simp add: sbdom_rep_eq)
  by (metis (full_types) assms hidespfwell_helper)

lemma parcomp_repAbs: "Rep_CSPF (Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))) 
                      = (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))"
  by simp
    
lemma sercomp_repAbs: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" shows "Rep_CSPF (Abs_CSPF (\<lambda> x. (sbDom\<cdot>x =  spfDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))) 
                      = (\<lambda> x. (sbDom\<cdot>x =  spfDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
  by (simp add: assms)

lemma sercomp_dom: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" shows "spfDom\<cdot>(f1 \<circ> f2) = spfDom\<cdot>f1"
  apply(simp add: sercomp_def, subst spfDomAbs)
  by (simp_all add: assms)
    
lemma t24: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" and "sbDom\<cdot>sb = spfDom\<cdot>f1" shows "((f1 \<circ> f2)\<rightleftharpoons>sb = a) \<longrightarrow> (sbDom\<cdot>a=spfRan\<cdot>f2)"
  apply(simp add: sercomp_def sercomp_repAbs assms)
  using assms(1) assms(2) hidespfwell_helper by blast

lemma sercomp_ran: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" shows "spfRan\<cdot>(f1 \<circ> f2) = spfRan\<cdot>f2"
  by (metis assms sbleast_sbdom sercomp_dom spfran_least t24)
    
  
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
  by(simp add: sercomp_dom)

lemma ranInnerSum4SPF[simp]: "spfRan\<cdot>(innerSum4SPF) = {c5}"
  by(simp add: sercomp_ran)

lemma domInnerFeedbackSum4SPF: "spfDom\<cdot>(innerFeedbackSum4SPF) = {c1, c5}"
  apply(subst spfRename_spfDom)
  apply(simp_all add: spf_map_well_def map_injective_def)
  by auto

lemma ranInnerFeedbackSum4SPF: "spfRan\<cdot>(innerFeedbackSum4SPF) = {c5}"
  apply(subst spfRename_spfRan)
  by(simp_all add: spf_map_well_def map_injective_def)
    
lemma ranInnerFeedbackSum4SPF_sb: assumes "sbDom\<cdot>sb = {c1, c5}" shows "sbDom\<cdot>(innerFeedbackSum4SPF\<rightleftharpoons>sb) = spfRan\<cdot>(innerFeedbackSum4SPF)"
  by (simp add: assms domInnerFeedbackSum4SPF hidespfwell_helper)
  
lemma [simp]: "spfDom\<cdot>sum4SPF = {c1}"
  apply (simp only: sum4SPF_def)
  apply(subst spfFeedbackOperator_new_spfDom)
  by(auto simp add: spf_map_well_def map_injective_def) 

lemma [simp]: "spfRan\<cdot>sum4SPF = {c5}"
  apply (simp only: sum4SPF_def) 
  apply(subst spfFeedbackOperator_new_spfRan)
    by(simp_all add: spf_map_well_def map_injective_def)
  
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
  show ?thesis  
    apply(simp only: sercomp_def)
    apply(subst sercomp_repAbs)
    apply(simp_all add: assms)
    apply(simp only: parcomp_def)
    apply(simp only: parcomp_repAbs, simp add: assms f1)
    apply(simp add: idC_def append0C_def addC_def)
    apply(simp add: SPF1x1_rep_eq SPF2x1_rep_eq assms)
    apply(simp add: f2 f3 f4)
    by(simp add: sb_id_def appendElem2_def)
qed  
  
lemma innerFeedbackSum4SPF_c5_eq: assumes "sbDom\<cdot>sb = {c1}" and "sbDom\<cdot>z = {c5}" shows
    "(innerFeedbackSum4SPF \<rightleftharpoons> ((sb \<uplus> z)\<bar> {c1, c5})) . c5 = add\<cdot>(sb . c1)\<cdot>(\<up>0\<bullet>(z . c5))"
proof - 
  have f1: "(sbRenameChMap ((sb \<uplus> z)\<bar>{c1, c5}) [c5 \<mapsto> c2]) . c1 = sb . c1"
    apply(simp add: assms)
    apply(subst sbRenameChMap_getCh2)
    by(simp_all add: assms map_injective_def)
  have f2: "(sbRenameChMap ((sb \<uplus> z)\<bar>{c1, c5}) [c5 \<mapsto> c2]) . c2 = z . c5"
    apply(simp add: assms)
    apply(subst sbRenameChMap_getCh)
    apply(simp)
    by (simp_all add: assms(2) map_injective_def)
  have f3: "sbDom\<cdot>(sbRenameChMap ((sb \<uplus> z)\<bar>{c1, c5}) [c5 \<mapsto> c2]) = I (idC\<parallel>append0C) addC"
    apply(simp add: assms)
    apply(subst sbRenameChMap_sbDom)
     apply(simp_all add: sb_rename_map_well_def map_injective_def assms)
    by auto
  show ?thesis 
  apply(simp only: spfRename_def)
    apply(subst spfRename_RepAbs)
     apply(simp add: spf_map_well_def map_injective_def)
    apply(simp add: assms)
    apply(subst innerSum4SPF_c5_eq)
     apply(simp add: f3)
    apply(subst f1)
    apply(subst f2)
      by auto
qed  
  
  
section \<open>Equality proof\<close>

  
lemma t5: assumes "sbDom\<cdot>sb = {c1}" shows 
    "cont (\<lambda> z. (innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> z)\<bar> {c1, c5})))"
  by (metis domInnerFeedbackSum4SPF spfFeedH_cont)

lemma t4: assumes "sbDom\<cdot>sb = {c1}" and "sbDom\<cdot>x = {c5} " shows
    "(\<Lambda> z. (innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> z)\<bar> {c1, c5})))\<cdot>x = (\<Lambda> z. [c5 \<mapsto> add\<cdot>(sb . c1)\<cdot>(appendElem2 0\<cdot>(z . c5))]\<Omega>)\<cdot>x" 
proof - 
  have f1: "sbDom\<cdot>(innerFeedbackSum4SPF\<rightleftharpoons>(sb \<uplus> x)) = {c5}"
    by (metis assms(1) assms(2) insert_is_Un ranInnerFeedbackSum4SPF ranInnerFeedbackSum4SPF_sb sbunionDom)
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
        by (metis assms domInnerFeedbackSum4SPF insert_absorb2 insert_is_Un ranInnerFeedbackSum4SPF sbunionDom spfRanRestrict subset_insertI)
      have f4: "sbfun_io_eq (iterate i\<cdot>(\<Lambda> z. innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> z)\<bar>{c1, c5}))) {c5} 
            \<Longrightarrow> sbDom\<cdot>(iterate i\<cdot>(\<Lambda> z. innerFeedbackSum4SPF\<rightleftharpoons>((sb \<uplus> z)\<bar>{c1, c5}))\<cdot>({c5}^\<bottom>)) = {c5}"
        by blast
      case (Suc i)
      then show ?case
        apply(subst iterate_Suc)
        apply(subst Abs_cfun_inverse2)
         apply(subst t5, simp add: assms, simp)
          by (smt Int_insert_right Un_insert_right assms insertI1 insert_commute ranInnerFeedbackSum4SPF ranInnerFeedbackSum4SPF_sb sbrestrict_sbdom sbunionDom sbunion_restrict sup_bot.right_neutral)
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
  
  
subsection \<open>Result\<close>
    

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