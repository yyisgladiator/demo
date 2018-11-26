theory UFun_Comp_MW
  imports fun.UFun_Comp
begin

lemma ufcomp_fix_f1: assumes "comp_well uf1 uf2" and "ubclDom\<cdot>sb = ufCompI uf1 uf2"
  shows "((uf1 \<otimes> uf2) \<rightleftharpoons> sb) \<bar> ufRan\<cdot>uf1 = uf1 \<rightleftharpoons> ((sb \<uplus> ((uf1 \<otimes> uf2) \<rightleftharpoons> sb)) \<bar> ufDom\<cdot>uf1)"
proof - 
  have "ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2) = (ufCompH uf1 uf2 sb)\<cdot>(ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2))"
    apply(subst ubfix_eq)
    apply (simp add: assms(2) ubcldom_least_cs)
    by blast
  then have "(ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)) = 
    (uf1 \<rightleftharpoons> ((sb \<uplus> (ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)))  \<bar> ufDom\<cdot>uf1)) \<uplus> 
    (uf2 \<rightleftharpoons> ((sb \<uplus> (ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)))  \<bar> ufDom\<cdot>uf2))"
    by (metis ufcomph_insert)
  then have "(ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)) \<bar> ufRan\<cdot>uf1 = (uf1 \<rightleftharpoons> ((sb \<uplus> (ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2))) \<bar> ufDom\<cdot>uf1))"
    using ubclunion_restrict2 ufcomph_insert
    by (smt Un_Diff_cancel assms(1) assms(2) comp_well_def inf_sup_aci(1) subset_Un_eq sup_commute sup_left_commute sup_left_idem ubclunion_restrict3 ubclunion_ubcldom ufCompI_def ufCompO_def ufRanRestrict ufcomp_well_h)
  then show ?thesis
    apply(subst ufcomp_repabs)
    using assms(1) comp_well_def apply auto[1]
    apply(subst ufcomp_repabs)
    using assms(1) comp_well_def apply auto[1]
    by(simp add: assms(2))
qed

lemma ufcomp_fix_f2: assumes "comp_well uf1 uf2" and "ubclDom\<cdot>sb = ufCompI uf1 uf2"
  shows "((uf1 \<otimes> uf2) \<rightleftharpoons> sb) \<bar> ufRan\<cdot>uf2 = uf2 \<rightleftharpoons> ((((uf1 \<otimes> uf2) \<rightleftharpoons> sb) \<uplus> sb) \<bar> ufDom\<cdot>uf2)"
proof - 
  have "ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2) = (ufCompH uf1 uf2 sb)\<cdot>(ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2))"
    apply(subst ubfix_eq)
    apply (simp add: assms(2) ubcldom_least_cs)
    by blast
  then have "(ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)) = 
    (uf1 \<rightleftharpoons> ((sb \<uplus> (ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)))  \<bar> ufDom\<cdot>uf1)) \<uplus> 
    (uf2 \<rightleftharpoons> ((sb \<uplus> (ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)))  \<bar> ufDom\<cdot>uf2))"
    by (metis ufcomph_insert)
  then have "(ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2)) \<bar> ufRan\<cdot>uf2 = (uf2 \<rightleftharpoons> ((sb \<uplus> (ubFix (ufCompH uf1 uf2 sb) (ufRan\<cdot>uf1 \<union> ufRan\<cdot>uf2))) \<bar> ufDom\<cdot>uf2))"
    using ubclunion_restrict2 ufcomph_insert
    by (smt Un_Diff_cancel assms(1) assms(2) comp_well_def inf_sup_aci(1) subset_Un_eq sup_commute sup_left_commute sup_left_idem ubclunion_restrict3 ubclunion_ubcldom ufCompI_def ufCompO_def ufRanRestrict ufcomp_well_h)
  then show ?thesis
    apply(subst ufcomp_repabs)
    using assms(1) comp_well_def apply auto[1]
    apply(subst ufcomp_repabs)
    using assms(1) comp_well_def apply auto[1]
    apply(simp add: assms(2))
    by (metis  assms(1) assms(2) comp_well_def ubclunion_commu ufcomp_I_inter_Oc_empty ufcomp_well_h)
qed

lemma ufcomp_fix: assumes "comp_well uf1 uf2" and "ubclDom\<cdot>sb = ufCompI uf1 uf2"
  shows "(uf1 \<otimes> uf2) \<rightleftharpoons> sb = (uf1 \<rightleftharpoons> ((((uf1 \<otimes> uf2) \<rightleftharpoons> sb) \<uplus> sb) \<bar> ufDom\<cdot>uf1)) \<uplus> (uf2 \<rightleftharpoons> ((((uf1 \<otimes> uf2) \<rightleftharpoons> sb) \<uplus> sb) \<bar> ufDom\<cdot>uf2))"
  by (metis (no_types, lifting) assms(1) assms(2) comp_well_def ubclunion_commu ubclunion_ubclrestrict_id ufCompO_def ufcomp_I_inter_Oc_empty ufcomp_dom ufcomp_fix_f1 ufcomp_fix_f2 ufcomp_ran ufran_2_ubcldom2) 




end