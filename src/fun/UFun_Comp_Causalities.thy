theory UFun_Comp_Causalities
  imports UFun_Comp bundle.UBundle_Conc
begin

default_sort uscl_conc

declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]

section{* ufSerComp *}

lemma ufsercomp_ufisweak: 
  assumes "ufIsWeak uf1"
  and     "ufIsWeak uf2"
  and     "sercomp_well uf1 uf2"
shows     "ufIsWeak (uf1 \<circ> uf2)"
proof(rule ufisweakI)
  fix ub::"'a"
  assume ub_dom: "ubclDom\<cdot>ub = ufDom\<cdot>(uf1 \<circ> uf2)"
  have comp_apply: "(uf1 \<circ> uf2)\<rightleftharpoons> ub = uf2 \<rightleftharpoons> (uf1 \<rightleftharpoons> ub)"
    by (metis assms ub_dom ufSerComp_apply ufSerComp_dom)
  moreover have "ubclLen ub \<le> ubclLen (uf1 \<rightleftharpoons> ub)"
    by (metis assms ub_dom ufSerComp_dom ufisweakE)
  moreover have "ubclLen (uf1 \<rightleftharpoons> ub) \<le> ubclLen (uf2 \<rightleftharpoons> (uf1 \<rightleftharpoons> ub))"
    by (metis assms ub_dom ufSerComp_dom ufisweakE ufran_2_ubcldom2)
  ultimately have "ubclLen ub \<le> ubclLen (uf2 \<rightleftharpoons> (uf1 \<rightleftharpoons> ub))"
    using trans_lnle by blast
  then show "ubclLen ub \<le> ubclLen ((uf1 \<circ> uf2) \<rightleftharpoons> ub)"
    by(simp add: comp_apply)
qed

lemma ufsercomp_ufisstrong1:
  assumes "ufIsStrong uf1"
  and     "ufIsWeak uf2"
  and     "sercomp_well uf1 uf2"
shows     "ufIsStrong (uf1 \<circ> uf2)"
proof(rule ufisstrongI)
  fix ub::"'a"
  assume ub_dom: "ubclDom\<cdot>ub = ufDom\<cdot>(uf1 \<circ> uf2)"
  have comp_apply: "(uf1 \<circ> uf2) \<rightleftharpoons> ub = uf2 \<rightleftharpoons> (uf1 \<rightleftharpoons> ub)"
    by (metis assms(3) ub_dom ufSerComp_apply ufSerComp_dom)
  moreover have "lnsuc\<cdot>(ubclLen ub) \<le> ubclLen (uf1  \<rightleftharpoons> ub)"
    by (metis assms(1) assms(3) ub_dom ufSerComp_dom ufisstrongE)
  moreover have "ubclLen(uf1 \<rightleftharpoons> ub) \<le> ubclLen (uf2 \<rightleftharpoons> (uf1 \<rightleftharpoons> ub))"
    by (metis assms(2) assms(3) ub_dom ufSerComp_dom ufisweakE ufran_2_ubcldom2)  
  ultimately have "lnsuc\<cdot>(ubclLen ub) \<le> ubclLen (uf2 \<rightleftharpoons> (uf1 \<rightleftharpoons> ub))"
    using lnsuc_lnle_emb trans_lnle by blast
  then show "lnsuc\<cdot>(ubclLen ub) \<le> ubclLen ((uf1 \<circ> uf2) \<rightleftharpoons> ub)"
    by(simp add: comp_apply)
qed 

lemma ufsercomp_ufisstrong2:
  assumes "ufIsWeak uf1"
  and     "ufIsStrong uf2"
  and     "sercomp_well uf1 uf2"
shows     "ufIsStrong (uf1 \<circ> uf2)"
proof(rule ufisstrongI)
  fix ub::"'a"
  assume ub_dom: "ubclDom\<cdot>ub = ufDom\<cdot>(uf1 \<circ> uf2)"
  have comp_apply: "(uf1 \<circ> uf2) \<rightleftharpoons> ub = uf2 \<rightleftharpoons> (uf1 \<rightleftharpoons> ub)"
    by (metis assms(3) ub_dom ufSerComp_apply)
  moreover have "ubclLen ub \<le> ubclLen (uf1  \<rightleftharpoons> ub)"
    by (metis assms(1) assms(3) ub_dom ufSerComp_dom ufisweakE)
  moreover have "lnsuc\<cdot>(ubclLen(uf1 \<rightleftharpoons> ub)) \<le> ubclLen (uf2 \<rightleftharpoons> (uf1 \<rightleftharpoons> ub))"
    by (metis assms(2) assms(3) ub_dom ufSerComp_dom ufisstrongE ufran_2_ubcldom2)
  ultimately have "lnsuc\<cdot>(ubclLen ub) \<le> ubclLen (uf2 \<rightleftharpoons> (uf1 \<rightleftharpoons> ub))"
    using lnsuc_lnle_emb trans_lnle by blast
  then show "lnsuc\<cdot>(ubclLen ub) \<le> ubclLen ((uf1 \<circ> uf2) \<rightleftharpoons> ub)" 
    by(simp add: comp_apply)
qed 
  
lemma ufsercomp_ufisstrong:
  assumes "ufIsWeak uf1"
  and     "ufIsWeak uf2"
  and     "ufIsStrong uf1 \<or> ufIsStrong uf2"
  and     "sercomp_well uf1 uf2"
shows     "ufIsStrong (uf1 \<circ> uf2)"
  apply(cases "ufIsStrong uf1")
  apply(subst ufsercomp_ufisstrong1)
  apply(simp_all add: assms)
  using assms(4) apply blast
  apply(subst ufsercomp_ufisstrong2)
  apply(simp_all add: assms)
  using assms(3) assms(4) by blast+

subsection{* ufParComp *}

lemma ufparcomp_ufisweak:
  fixes uf1 uf2::"('a::uscl_pcpo ubundle, 'b::uscl_pcpo ubundle) ufun"
  assumes "ufIsWeak uf1"
  and     "ufIsWeak uf2"
  and     "parcomp_well uf1 uf2"
shows     "ufIsWeak (ufParComp uf1  uf2)"
proof(rule ufisweakI)
  fix ub::"'a::uscl_pcpo ubundle"
  assume "ubclDom\<cdot>ub = ufDom\<cdot>(uf1 \<parallel> uf2)"
  then have  ub_dom: "ubclDom\<cdot>ub = ufDom\<cdot>uf1 \<union> ufDom\<cdot>uf2"
    using assms(3) ufParComp_dom by blast
 have comp_apply: "(uf1 \<parallel> uf2) \<rightleftharpoons> ub = (uf1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>uf1)\<cdot>ub)) \<uplus> (uf2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>uf2)\<cdot>ub))"
   by (simp add: assms(3) parcomp_func_h2 ub_dom ubclRestrict_ubundle_def)
  have "ubLen ub \<le> ubLen (ubRestrict (ufDom\<cdot>uf1)\<cdot>ub)"
    by (simp add: ubrestrict_ublen)
  then have uf1_len:"ubLen ub \<le> ubLen (uf1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>uf1)\<cdot>ub))"
    by (metis (no_types, lifting) Un_upper1 assms ub_dom dual_order.trans 
        ubclLen_ubundle_def ubclRestrict_ubundle_def ubrestrict_dom2 ufisweakE)
   have "ubLen ub \<le> ubLen (ubRestrict (ufDom\<cdot>uf2)\<cdot>ub)"
    by (simp add: ubrestrict_ublen)
  moreover have "ubLen (ubRestrict (ufDom\<cdot>uf2)\<cdot>ub) \<le> ubLen (uf2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>uf2)\<cdot>ub))"
    by (metis Int_absorb1 Un_upper1 assms ub_dom sup_commute ubclDom_ubundle_def ubclLen_ubundle_def 
        ubrestrict_ubdom2 ufisweakE)
  ultimately have uf2_len: "ubLen ub \<le> ubLen (uf2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>uf2)\<cdot>ub))"
     by (metis order_trans)
  show "ubclLen ub \<le> ubclLen ((uf1 \<parallel> uf2) \<rightleftharpoons> ub)"
    by (simp add: local.comp_apply ubclLen_ubundle_def ubclUnion_ubundle_def ubunion_len_le uf1_len uf2_len)
qed


section{* ufHide *}

lemma ufhide_ufisweak_ubundle:
  fixes f::"('a::uscl_pcpo ubundle, 'b::uscl_pcpo ubundle ) ufun"
  assumes "ufIsWeak f"
  shows   "ufIsWeak (ufHide f cs)"
proof(rule ufisweakI)
  fix ub::"'a ubundle"
  assume "ubclDom\<cdot>ub = ufDom\<cdot>(f \<h> cs)"
  then have ub_dom: "ubDom\<cdot>ub = ufDom\<cdot>f"
    by (simp add: ubclDom_ubundle_def ufhide_dom)
 have "ubLen ub \<le> ubLen (f \<rightleftharpoons> ub)"
   by (metis assms ub_dom ubclDom_ubundle_def ubclLen_ubundle_def ufisweakE)
  moreover have "\<And> cs. ubLen (f \<rightleftharpoons> ub) \<le> ubLen (ubRestrict cs\<cdot>(f \<rightleftharpoons> ub))" 
    by (simp add: ubrestrict_ublen)
  ultimately show "ubclLen ub \<le> ubclLen (f \<h> cs \<rightleftharpoons> ub)"
    by(simp add: ufhide_apply assms ub_dom ubclRestrict_ubundle_def trans_lnle ubclDom_ubundle_def ubclLen_ubundle_def)
qed

lemma ufhide_ufisweak:
  assumes "ufIsWeak f"
  shows   "ufIsWeak (ufHide f cs)"
  oops

section{* ufComp *}

subsection {* ufCompH*}

lemma ufcomph_len:
  assumes "ubDom\<cdot>ub = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"
      and "ubDom\<cdot>x = ufCompI f1 f2"
      and "ufIsWeak f1" 
      and "ufIsWeak f2"
      and "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"                   
    shows "min (ubLen ub) (ubLen x) \<le> ubLen ((ufCompH f1 f2 x)\<cdot>ub)"
proof -
 have in_dom: "ubDom\<cdot>(x \<uplus> ub) \<supseteq> ufDom\<cdot>f1 \<union> ufDom\<cdot>f2"
   by(simp add: ubclUnion_ubundle_def assms ufCompI_def)
  obtain n where min_len: "n = min (ubLen ub) (ubLen x)"
    by simp
   
  have in_len: "n \<le> ubLen (x \<uplus> ub)"
    by (simp add: min_def min_len ubclUnion_ubundle_def ubunion_len_le)
  
  have "n \<le> ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub))"
    using in_len trans_lnle ubrestrict_ublen by blast
    moreover have "ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub)) \<le> ubLen (f1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub)))"
      by (metis assms(3) in_dom le_supE ubclDom_ubundle_def ubclLen_ubundle_def ubclRestrict_ubundle_def ubrestrict_dom2 ufisweakE)
    ultimately have f1_len: "n \<le> ubLen (f1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub)))"
      using trans_lnle in_len by blast

  have "n \<le> ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ub))"
    using in_len trans_lnle ubrestrict_ublen by blast
    moreover have "ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ub)) \<le> ubLen (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ub)))"
      by (metis Int_absorb1 assms(4) in_dom le_supE ubclDom_ubundle_def ubclLen_ubundle_def ubrestrict_ubdom2 ufisweakE)
    moreover have "ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ub)) \<le> ubLen (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ub)))"
      using calculation(2) dual_order.trans less_lnsuc by blast
    ultimately have f2_len: "n \<le> ubLen (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ub)))"
      using dual_order.trans by blast

   have "n \<le> ubLen ((f1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub))) \<uplus> (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ub))))"
     by (metis f1_len f2_len min_def min_len ubclUnion_ubundle_def ubunion_len_le)
   then show ?thesis
     by (metis min_len ubclRestrict_ubundle_def ufcomph_insert)
  qed

lemma iterate_ufcomph_len_le: 
  assumes "ubDom\<cdot>ub = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"
    and  "ubDom\<cdot>x = ufCompI f1 f2"
    and  "ufIsWeak f1" 
    and  "ufIsWeak f2"
    and  "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"  
  shows  "min (ubLen ub) (ubLen x) \<le> ubLen (iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>ub)"
proof(induction i)
  case 0
  then show ?case 
    by simp
next
  case (Suc i)
  assume a: "min (ubLen ub) (ubLen x) \<le> ubLen (iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>ub)"
  moreover have "min (ubLen (iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>ub)) (ubLen x) \<le> ubLen ((ufCompH f1 f2 x)\<cdot>(iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>ub))"
    by (metis assms iterate_ufcomph_dom ubclDom_ubundle_def ufcomph_len)
  moreover have "min (ubLen ub) (ubLen x) \<le> min (ubLen (iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>ub)) (ubLen ub)"
    by (simp add: a)
  ultimately show ?case
    using dual_order.trans by fastforce 
qed

subsection{* Feedback Case *}

lemma iterate_ufcomph_len_l_h:  
  assumes "ubDom\<cdot>ub = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"
    and     "ubDom\<cdot>x = ufCompI f1 f2"
    and     "ufIsWeak f1" 
    and     "ufIsStrong f2"
    and     "ufRan\<cdot>f2 \<subset> ufDom\<cdot>f1"
    and     "ufDom\<cdot>f2 = ufRan\<cdot>f1"
    and     "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
    and     "ubLen ub < ubLen x"
    and     "ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>ub) < ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>ub)"
  shows     "ubLen ub < ubLen (iterate (Suc i)\<cdot>(ufCompH f1 f2 x)\<cdot>ub)"
proof -
  have ub_fin: "ubLen ub < \<infinity>"
    by (metis assms(8) inf_ub leD le_neq_trans)
  have ub_split: " ub = (ubRestrict (ufDom\<cdot>f1)\<cdot>ub) \<uplus> (ubRestrict (ufDom\<cdot>f2)\<cdot>ub)"
    by (simp add: assms dual_order.strict_implies_order le_supI1 ub_split_union ubclUnion_ubundle_def)
  have ub_res_f2: "ubRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ub) = ubRestrict  (ufDom\<cdot>f2)\<cdot>ub"
    by (metis (no_types, lifting) Un_upper1 assms ubRestrict_twice ubclDom_ubundle_def 
        ubclRestrict_ubundle_def ubclunion_restrict2 ubrestrict_dom2 ubrestrict_ubdom2)
 have in_dom: "ubDom\<cdot>(x \<uplus> ub) \<supseteq> ufDom\<cdot>f1 \<union> ufDom\<cdot>f2"
   by(simp add: ubclUnion_ubundle_def assms ufCompI_def)

  have ub_len: "ubLen ub = ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>ub)"
    by (metis (no_types, lifting) assms dual_order.strict_trans2 not_less_iff_gr_or_eq ub_split 
        ubclUnion_ubundle_def ubrestrict_ublen ubunion_len_l)
  have "lnsuc\<cdot>(ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>ub)) \<le> ubLen (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>ub))"
    by (metis assms inf_commute inf_sup_absorb ubclDom_ubundle_def ubclLen_ubundle_def 
        ubrestrict_ubdom2 ufisstrongE)  
  then have "ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>ub) < ubLen (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>ub))"
    by (metis assms inf_ub le2lnle leD le_neq_trans)
  moreover have "ubLen ub \<le> ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>ub)"
    by (simp add: ubrestrict_ublen)
  ultimately have f2_out_len:"ubLen ub < ubLen (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>ub))"
    by (metis dual_order.strict_trans2)
   have "ubLen ub < ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub))"
     by (metis (no_types, lifting) assms order.strict_trans2 ub_len ubclUnion_ubundle_def 
         ubrestrict_ublen ubunion_len_l ubunion_ubrestrict3)
  moreover have "ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub)) \<le> ubLen (f1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub)))"
    by (metis (no_types) Int_absorb1 assms in_dom le_supE ubclDom_ubundle_def ubclLen_ubundle_def ubrestrict_ubdom2 ufisweakE)
  ultimately have f1_out_len: "ubLen ub < ubLen (f1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub)))"
    using dual_order.strict_trans1 by blast 
  
  have "ubLen ub < ubLen ((f1 \<rightleftharpoons> ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub)) \<uplus> (f2\<rightleftharpoons> ubRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ub)))"
    by (metis f1_out_len f2_out_len ub_res_f2 ubclUnion_ubundle_def ubunion_len_l)
  then have iter1:"ubLen ub < ubLen (iterate 1\<cdot>(ufCompH f1 f2 x)\<cdot>ub)"
    by(simp add: ufcomph_insert ubclRestrict_ubundle_def)

  moreover have "min (ubLen (iterate 1\<cdot>(ufCompH f1 f2 x)\<cdot>ub)) (ubLen x) \<le> ubLen (iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>(iterate 1\<cdot>(ufCompH f1 f2 x)\<cdot>ub))"
    by (metis assms iterate_ufcomph_dom iterate_ufcomph_len_le ubclDom_ubundle_def ufisstrong_2_ufisweak)
  moreover have "ubLen ub < ubLen (iterate 1\<cdot>(ufCompH f1 f2 x)\<cdot>ub)"
    using iter1 by auto
  ultimately show ?thesis
    by (metis (no_types, hide_lams) Suc_eq_plus1 assms(8) dual_order.strict_trans1 iterate_iterate min_def)          
qed

lemma iterate_ufcomph_len_l:  
  assumes "ubDom\<cdot>ub = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"
    and     "ubDom\<cdot>x = ufCompI f1 f2"
    and     "ufIsWeak f1" 
    and     "ufIsStrong f2"
    and     "ufRan\<cdot>f2 \<subset> ufDom\<cdot>f1"
    and     "ufDom\<cdot>f2 = ufRan\<cdot>f1"
    and     "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
    and     "ufRan\<cdot>f1 \<inter> ufDom\<cdot>f1 = {}"
    and     "ubLen ub < ubLen x"                          
  shows     "ubLen ub < ubLen (iterate (2+i)\<cdot>(ufCompH f1 f2 x)\<cdot>ub)"
proof(cases "ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>ub) < ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>ub)")
  case True
 then show ?thesis
   by (metis assms add_2_eq_Suc iterate_ufcomph_len_l_h)              
next
  case False
  then have f1_le_f2: "ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>ub) \<le> ubLen  (ubRestrict (ufDom\<cdot>f2)\<cdot>ub)"
    using leI by blast
  have ub_fin: "ubLen ub < \<infinity>"
    by (metis assms(9) inf_ub leD le_neq_trans)
  have ub_split: " ub = (ubRestrict (ufDom\<cdot>f1)\<cdot>ub) \<uplus> (ubRestrict (ufDom\<cdot>f2)\<cdot>ub)"
    by (simp add: assms dual_order.strict_implies_order le_supI1 ub_split_union ubclUnion_ubundle_def)
  have ub_min: "ubLen ub = ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>ub)"
   by (metis dual_order.antisym f1_le_f2 ub_split ubclUnion_ubundle_def ubrestrict_ublen ubunion_ublen_le) 
  then have ub_f1_fin: "ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>ub) < \<infinity>"
    using ub_fin by auto
  have ub_res_f2: "ubRestrict (ufDom\<cdot>f2)\<cdot>(x\<uplus>ub) = ubRestrict  (ufDom\<cdot>f2)\<cdot>ub"
    by (metis (no_types, lifting) Un_upper1 assms ubRestrict_twice ubclDom_ubundle_def 
        ubclRestrict_ubundle_def ubclunion_restrict2 ubrestrict_dom2 ubrestrict_ubdom2)
 have in_dom: "ubDom\<cdot>(x \<uplus> ub) \<supseteq> ufDom\<cdot>f1 \<union> ufDom\<cdot>f2"
   by(simp add: ubclUnion_ubundle_def assms ufCompI_def)

   have "lnsuc\<cdot>(ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>ub)) \<le> ubLen (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>ub))"
     by (metis Int_absorb1 Un_upper1 assms ubclDom_ubundle_def ubclLen_ubundle_def 
         ubrestrict_ubdom2 ufisstrongE)  
   then have "lnsuc\<cdot>(ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>ub)) \<le> ubLen (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>ub))"
    by (metis f1_le_f2 lnsuc_lnle_emb order_subst2)
  then have f2_out_len: "ubLen ub < ubLen (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>ub))"
    using le2lnle ub_fin ub_min by auto

 have "ubLen ub \<le> ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub))"
   by (metis (no_types, hide_lams) assms dual_order.trans le_cases not_le ubclUnion_ubundle_def 
       ubrestrict_ublen ubunion_len_le)
  moreover have "ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub)) \<le> ubLen (f1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub)))"
    by (metis Int_absorb1 assms in_dom le_supE ubclDom_ubundle_def ubclLen_ubundle_def 
        ubrestrict_ubdom2 ufisweakE)
  ultimately have f1_out_len: "ubLen ub \<le> ubLen (f1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub)))"
    using dual_order.trans by blast 
  
  then show ?thesis
  proof(cases "ubLen (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>ub)) \<le> ubLen (f1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub)))")
    case True
    then have "ubLen ub < ubLen (f1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f1)\<cdot>(x\<uplus> ub)))"
      using dual_order.strict_trans1 f2_out_len by blast
    then have "ubLen ub < ubLen ((f1 \<rightleftharpoons> ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub)) \<uplus> (f2\<rightleftharpoons> ubRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ub)))"
      by (metis assms f2_out_len ub_res_f2 ubclDom_ubundle_def ubclUnion_ubundle_def 
          ubclunion_commu ubunion_len_l ufCompO_def ufcomp_I_inter_Oc_empty)
    then have "ubLen ub < ubLen (iterate 1\<cdot>(ufCompH f1 f2 x)\<cdot>ub)"
      by(simp add: ufcomph_insert ubclRestrict_ubundle_def ubclUnion_ubundle_def)

  moreover have "min (ubLen (iterate 1\<cdot>(ufCompH f1 f2 x)\<cdot>ub)) (ubLen x) \<le> ubLen (iterate (Suc i)\<cdot>(ufCompH f1 f2 x)\<cdot>(iterate 1\<cdot>(ufCompH f1 f2 x)\<cdot>ub))"
    by (metis assms iterate_ufcomph_dom iterate_ufcomph_len_le ubclDom_ubundle_def ufisstrong_2_ufisweak)
  moreover have "(iterate (2 + i)\<cdot>(ufCompH f1 f2 x)\<cdot>ub) = (iterate (Suc i)\<cdot>(ufCompH f1 f2 x)\<cdot>(iterate 1\<cdot>(ufCompH f1 f2 x)\<cdot>ub))"
    by (metis Suc_eq_plus1 add_2_eq_Suc iterate_iterate)
  ultimately show ?thesis
    by (metis (no_types, hide_lams) assms(9) min_def min_less_iff_conj)

  next
    case False
    then have "ubLen (f1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub))) < ubLen (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(ub)))"
      by (metis assms leI ubclDom_ubundle_def ubclunion_commu ufCompO_def ufcomp_I_inter_Oc_empty)
    moreover obtain ub2 where ub2_split: "ub2 = (f1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub))) \<uplus> (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ub)))"
      by metis
    moreover have ub2_iter: "ub2 = iterate 1\<cdot>(ufCompH f1 f2 x)\<cdot>ub"
      by(simp add: ub2_split ufcomph_insert ub_res_f2 ubclRestrict_ubundle_def)
    moreover have ub2_res_f2:"ubRestrict (ufDom\<cdot>f2)\<cdot>ub2 = f1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f1)\<cdot>(x \<uplus> ub))"
      by (metis (no_types, lifting) Un_upper1 assms in_dom inf_commute le_supE ub2_split 
          ubclDom_ubundle_def ubclRestrict_ubundle_def ubclunion_restrict3 ufRanRestrict)
    moreover have ub2_res_f1: "ubRestrict (ufDom\<cdot>f1)\<cdot>ub2 = f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(x \<uplus> ub))"
      by (metis (no_types, lifting) assms dual_order.strict_implies_order in_dom le_supE ub2_split 
          ubclDom_ubundle_def ubclRestrict_ubundle_def ubclUnion_ubundle_def ubrestrict_id 
          ubunion_ubrestrict4 ufRanRestrict)
    ultimately have ub2_min_res: "ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>ub2) < ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>ub2)"
      by (metis ub_res_f2)
    then have ub2_min: "ubLen ub2 = ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>ub2)"
      by (metis ub2_res_f1 ub2_res_f2 dual_order.antisym dual_order.strict_implies_order ub2_split 
          ubrestrict_ublen ubclUnion_ubundle_def ubunion_ublen_le)
    then show ?thesis 
    proof(cases "ubLen ub2 < ubLen x")
      
      case True
      then have "ubLen ub2 < ubLen (iterate (Suc i)\<cdot>(ufCompH f1 f2 x)\<cdot>ub2)"
        by (metis assms iterate_ufcomph_dom iterate_ufcomph_len_l_h ub2_iter ub2_min_res 
            ubclDom_ubundle_def)
    then have "ubLen ub < ubLen (iterate (Suc i)\<cdot>(ufCompH f1 f2 x)\<cdot>ub2)"
      by (metis (no_types, lifting) assms dual_order.trans f1_out_len not_le ub2_min ub2_res_f2 
          ub_split ubclUnion_ubundle_def ubunion_commutative ufCompO_def ufcomp_I_inter_Oc_empty)
      then show ?thesis
        by (metis (no_types, hide_lams) One_nat_def add_2_eq_Suc iterate_0 iterate_Suc2 ub2_iter)
    
    next
      case False
      then have "ubLen x \<le> ubLen ub2"
        by simp
      moreover have "ubLen ub < ubLen ub2"
        using assms(9) calculation by auto
      moreover  have "ubLen ub < ubLen (iterate 1\<cdot>(ufCompH f1 f2 x)\<cdot>ub)"
        using calculation ub2_iter by auto
      moreover have "min (ubLen (iterate 1\<cdot>(ufCompH f1 f2 x)\<cdot>ub)) (ubLen x) \<le> ubLen (iterate (Suc i)\<cdot>(ufCompH f1 f2 x)\<cdot>(iterate 1\<cdot>(ufCompH f1 f2 x)\<cdot>ub))"
        by (metis assms iterate_ufcomph_dom iterate_ufcomph_len_le ubclDom_ubundle_def ufisstrong_2_ufisweak)
      ultimately show ?thesis
        by (metis (no_types, lifting) add_2_eq_Suc assms(9) dual_order.strict_trans1 iterate_Suc2 
            min_absorb2 ub2_iter ub2_split ub_res_f2 ubclRestrict_ubundle_def ufcomph_insert) 
    qed
  qed
qed

lemma iterate_ufcomph_len_ex:  
  assumes     "ubDom\<cdot>x = ufCompI f1 f2"
      and     "ufIsWeak f1" 
      and     "ufIsStrong f2"
      and     "ufRan\<cdot>f2 \<subset> ufDom\<cdot>f1"
      and     "ufDom\<cdot>f2 = ufRan\<cdot>f1"
      and     "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
      and     "ufDom\<cdot>f1 \<noteq> {}"
      and     "ufDom\<cdot>f2 \<noteq> {}"
      and     "ufRan\<cdot>f1 \<inter> ufDom\<cdot>f1 = {}"
    shows     "Fin n \<le> ubLen x \<Longrightarrow> \<exists>i. Fin n \<le> ubLen (iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>(ubLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))"
proof(induction n)
  case 0
  then show ?case
    by (metis Fin_0 lnle_def lnzero_def minimal)
next
  case (Suc n)
  then obtain i where i_def: "Fin n \<le> ubLen (iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>(ubLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))"
    using Fin_leq_Suc_leq by blast
  then show  ?case 
  proof(cases "ubLen (iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>(ubLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))) < ubLen x")
    case True
    then have "ubLen (iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>(ubLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))) <  
               ubLen (iterate (2)\<cdot>(ufCompH f1 f2 x)\<cdot>(iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>(ubLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))"
      by (metis One_nat_def Suc_1 add_2_eq_Suc assms iter_ufCompH_dom iterate_ufcomph_len_l ubclDom_ubundle_def ubclLeast_ubundle_def)   
    moreover have "iterate (2)\<cdot>(ufCompH f1 f2 x)\<cdot>(iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>(ubLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))) 
                   = iterate (2+i)\<cdot>(ufCompH f1 f2 x)\<cdot>(ubLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
      by (simp add: iterate_iterate)
    moreover have "Fin n < ubLen (iterate (2+i)\<cdot>(ufCompH f1 f2 x)\<cdot>(ubLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))"
      using calculation(1) calculation(2) i_def by auto
    moreover have "Fin (Suc n) \<le> ubLen (iterate (2+i)\<cdot>(ufCompH f1 f2 x)\<cdot>(ubLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))"
      using calculation(3) less2lnleD by blast
    ultimately show ?thesis
      by blast
  next
    case False
    then show ?thesis
      by (metis Fin_leq_Suc_leq Suc.prems i_def le_neq_trans less2lnleD)
  qed
qed


lemma ubfix_ublen: 
 fixes f1 f2::"('a ubundle, 'a ubundle) ufun"
  assumes     "ubDom\<cdot>x = ufCompI f1 f2"
      and     "ufIsWeak f1" 
      and     "ufIsStrong f2"
      and     "ufRan\<cdot>f2 \<subset> ufDom\<cdot>f1"
      and     "ufDom\<cdot>f2 = ufRan\<cdot>f1"
      and     "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
      and     "ufDom\<cdot>f1 \<noteq> {}"
      and     "ufDom\<cdot>f2 \<noteq> {}"
      and     "ufRan\<cdot>f1 \<inter> ufDom\<cdot>f1 = {}"
    shows "ubLen x \<le> ubLen (ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
proof(cases  "ubLen x = 0")
  case True
  then show ?thesis
    by (metis bottomI le_cases lnle_def lnzero_def)
next
  case False
  then show ?thesis  
proof -
  assume a: "ubLen x \<noteq> 0"
  then have x_g_zero:" ubLen x > 0"
    by (metis bottomI leI lnle_def lnzero_def)
  obtain ub  where ub_def: "ub  = ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"
    by blast
  have iter_chain: "chain (\<lambda> i. iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x)"
    by (simp add: assms(1) ubclDom_ubundle_def)
  then have iter_pref: "iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x \<sqsubseteq> ub"
    by (metis  ub_def ubFix_def is_ub_thelub) 
  then have iter_len: "ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x) \<le> ubLen ub"
    using lnle_def monofun_def ublen_monofun by blast

  have h2:"iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x = iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>(ubLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
    by (simp add: ubclLeast_ubundle_def)
  have h3: "ubLen (ubLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)::('b::uscl_conc) ubundle) < ubLen x"
    by (metis assms(5) assms(8) x_g_zero sup_eq_bot_iff ubleast_len)
  have h4: "ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x) < ubLen x 
          \<Longrightarrow> ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x) < ubLen (iter_ubfix2 (ufCompH f1 f2) (i+2) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x)"
    by (smt add.commute add_cancel_right_left assms iter_ufCompH_dom iterate_iterate iterate_ufcomph_len_l ubclDom_ubundle_def)
  have h5: "ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x) < ubLen x 
          \<Longrightarrow> iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x \<noteq> ub"
    by (metis (no_types, lifting) add_2_eq_Suc' assms(1) ub_def h4 iterate_Suc not_less_iff_gr_or_eq 
        ubclDom_ubundle_def ubcldom_least_cs ubfix_eq ufCompH_dom)
  have h6: "ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x) < ubLen x 
          \<Longrightarrow> ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x) < ubLen ub"
    by (smt add_2_eq_Suc' assms(1) h4 iter_pref iterate_Suc leD lnle_def monofun_cfun_arg 
        monofun_def not_less_iff_gr_or_eq ub_def ubclDom_ubundle_def ubclLen_ubundle_def 
        ubcldom_least_cs ubcllen_mono ubfix_eq ufCompH_dom)

   have " ubLen x < \<infinity> \<Longrightarrow> ubLen x \<le> ubLen ub"
  proof -
    assume x_fin: "ubLen x < \<infinity>"
    then obtain n where x_len: "ubLen x = Fin n"
      using lnat_well_h2 by auto 
    then have n_le_x:"Fin n \<le> ubLen x"
      by simp
    then have "\<exists>i. Fin n \<le> ubLen (iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>(ubLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))"
      using assms iterate_ufcomph_len_ex by blast
    then obtain i where i_def: "Fin n \<le> ubLen(iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x)"
      by (metis ubclLeast_ubundle_def)
    then have "iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x \<sqsubseteq> ub"
      by (metis is_ub_thelub iter_chain ubFix_def ub_def)
    then have "Fin n \<le> ubLen ub"
      by (meson i_def lnle_def monofun_def rev_below_trans ublen_monofun)
    then show ?thesis
      by (simp add: x_len)
  qed    
  moreover have "ubLen x = \<infinity> \<Longrightarrow> ubLen ub = \<infinity>"
  proof(rule ccontr)
    assume x_len: "ubLen x = \<infinity>"
    assume ub_len: "ubLen ub \<noteq> \<infinity>"
    then obtain n where ub_len_fin: "ubLen ub = Fin n"
      using infI by auto
    then have n_le_x: "Fin n \<le> ubLen x"
      by (simp add: x_len)
    then have "\<exists>i. Fin n \<le> ubLen (iterate i\<cdot>(ufCompH f1 f2 x)\<cdot>(ubLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))"
      using assms iterate_ufcomph_len_ex by blast
    then obtain i where i_def: "Fin n \<le> ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x)"
      by (metis ubclLeast_ubundle_def)
    moreover have "ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x) < ubLen x"
    proof -
      have "\<not>(\<infinity> \<sqsubseteq> Fin n)"
        by (metis lnle_def notinfI3)
      then show ?thesis
        by (metis (no_types) inf_ub is_ub_thelub iter_chain le_neq_trans monofun_def ubFix_def ub_def ub_len_fin ublen_monofun x_len)
    qed    
    moreover have "ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x) < ubLen (iterate (2 + 0)\<cdot>(ufCompH f1 f2 x)\<cdot> (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x))"
        by (metis assms calculation(2) iter_ufCompH_dom iterate_ufcomph_len_l ubclDom_ubundle_def)
    moreover have "ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x) < ubLen (iter_ubfix2 (ufCompH f1 f2) (i+2) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x)"
        by (metis (no_types, lifting) add.commute add_cancel_right_right calculation(3) iterate_iterate)
    moreover have "(iter_ubfix2 (ufCompH f1 f2) (i+2) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x) \<sqsubseteq> ub"
      by (metis is_ub_thelub iter_chain ubFix_def ub_def)
    moreover have "ubLen (iter_ubfix2 (ufCompH f1 f2) (i+2) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) x) \<le> ubLen ub"
      using calculation(5) lnle_def monofun_def ublen_monofun by blast
    then show "False"
      using calculation(4) i_def ub_len_fin by auto
  qed
 ultimately show "ubLen x \<le> ubLen (ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
    by (metis inf_ub le_neq_trans ub_def) 
  qed
qed

lemma ufisweak_comp_ufisstrong_ufisweak_eq_weak: 
  fixes uf1 uf2::"('a ubundle, 'a ubundle) ufun"
  assumes "ufIsWeak uf1" 
      and "ufIsStrong uf2"
      and "ufRan\<cdot>uf2 \<subset> ufDom\<cdot>uf1"
      and "ufDom\<cdot>uf2 = ufRan\<cdot>uf1"
      and "ufRan\<cdot>uf1 \<inter> ufRan\<cdot>uf2 = {}"
      and "ufDom\<cdot>uf1 \<noteq> {}"
      and "ufDom\<cdot>uf2 \<noteq> {}"
      and  "ufRan\<cdot>uf1 \<inter> ufDom\<cdot>uf1 = {}"
    shows "ufIsWeak (uf1 \<otimes> uf2)"
  apply(rule ufisweakI)
  apply(simp add: assms ubclDom_ubundle_def ufcomp_dom ufcomp_insert ubclLen_ubundle_def)
  apply(rule ubfix_ublen)
  using assms by blast+




section{* Old Version *}

lemma z1: assumes "ubDom\<cdot>z \<inter> ubDom\<cdot>zz = {}" shows "ubLen (z \<uplus> zz) = ubLen z \<or> ubLen (z \<uplus> zz) = ubLen zz"
  apply (simp add: ubclUnion_ubundle_def)
  apply (case_tac "ubDom\<cdot>z = {}")
  apply simp
  apply (case_tac "ubDom\<cdot>zz = {}")
  apply (metis Int_empty_right empty_subsetI ubunion_commutative ubunion_idL)
proof -
  assume a0: "ubDom\<cdot>z \<noteq> {}"
  assume a1: "ubDom\<cdot>zz \<noteq> {}"

  (*
    obtain least channel c1 of z
    obtain least channel c2 of zz
    case distiction length c1 < length c2
  *)

  obtain c1 where c1_def: "c1 \<in> ubDom\<cdot>z \<and> ubLen z = usclLen\<cdot>(z . c1)"
    using a0 ublen_min_on_channel
    by (metis (no_types, lifting) ubLen_def)
  then have c1_min: "\<forall> c\<in>ubDom\<cdot>z. usclLen\<cdot>(z . c1) \<le> usclLen\<cdot>(z . c)"
    using usclLen_all_channel_bigger by blast

  obtain c2 where c2_def: "c2 \<in> ubDom\<cdot>zz \<and> ubLen zz = usclLen\<cdot>(zz . c2)"
    using a1 ublen_min_on_channel
    by (metis (no_types, lifting) ubLen_def)
  then have c2_min: "\<forall> c\<in>ubDom\<cdot>zz. usclLen\<cdot>(zz . c2) \<le> usclLen\<cdot>(zz . c)"
    using usclLen_all_channel_bigger by blast

  show "ubLen (ubUnion\<cdot>z\<cdot>zz) = ubLen z \<or> ubLen (ubUnion\<cdot>z\<cdot>zz) = ubLen zz"
  proof(cases "usclLen\<cdot>(z . c1) \<le> usclLen\<cdot>(zz . c2)")
    case True
    then have "\<forall> c\<in>ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz). usclLen\<cdot>((ubUnion\<cdot>z\<cdot>zz) . c1) \<le> usclLen\<cdot>((ubUnion\<cdot>z\<cdot>zz) . c)"
      apply(simp)
      apply(subst ubunion_getchL)
      using assms c1_def apply blast
      by (metis (no_types, lifting) Un_iff c1_min c2_min dual_order.trans ubunion_getchL ubunion_getchR)
    moreover have "c1 \<in>ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)"
      by (simp add: c1_def)
    ultimately have "ubLen (ubUnion\<cdot>z\<cdot>zz) = usclLen\<cdot>((ubUnion\<cdot>z\<cdot>zz) . c1)"
      proof -
        have f1: "\<forall>p l. \<not> p (l::lnat) \<or> Least p \<le> l"
          using Least_le by blast
        have f2: "\<forall>c. c \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz) \<longrightarrow> usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c1) \<le> usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c)"
          by (metis \<open>\<forall>c::channel\<in>ubDom\<cdot> (ubUnion\<cdot> (z::'a::uscl_pcpo\<^sup>\<Omega>)\<cdot> (zz::'a::uscl_pcpo\<^sup>\<Omega>)). usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . (c1::channel)) \<le> usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c)\<close>)
        have f3: "\<forall>u. ubDom\<cdot>u \<noteq> {} \<longrightarrow> (\<exists>c. c \<in> ubDom\<cdot>u \<and> usclLen\<cdot>(u . c::'a) = (LEAST l. l \<in> {usclLen\<cdot>(u . c) |c. c \<in> ubDom\<cdot>u}))"
          using ublen_min_on_channel by blast
        obtain cc :: "channel set \<Rightarrow> channel" where
          "\<forall>x0. (\<exists>v1. v1 \<in> x0) = (cc x0 \<in> x0)"
          by moura
        then have "\<forall>C. (cc C \<in> C \<or> C = {}) \<and> ((\<forall>c. c \<notin> C) \<or> C \<noteq> {})"
          by auto
        then have f4: "ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz) \<noteq> {}"
          by (metis (no_types) \<open>(c1::channel) \<in> ubDom\<cdot> (ubUnion\<cdot>(z::'a::uscl_pcpo\<^sup>\<Omega>)\<cdot> (zz::'a::uscl_pcpo\<^sup>\<Omega>))\<close>)
        then obtain cca :: "'a\<^sup>\<Omega> \<Rightarrow> channel" where
          f5: "usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c1) \<le> usclLen\<cdot> (ubUnion\<cdot>z\<cdot>zz . cca (ubUnion\<cdot>z\<cdot>zz))"
          using f3 f2 by meson
        obtain ccb :: "'a\<^sup>\<Omega> \<Rightarrow> channel" where
          f6: "ccb (ubUnion\<cdot>z\<cdot>zz) \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz) \<and> usclLen\<cdot> (ubUnion\<cdot>z\<cdot>zz . ccb (ubUnion\<cdot>z\<cdot>zz)) = (LEAST l. l \<in> {usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c) |c. c \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)})"
          using f4 f3 by meson
          have "\<forall>x0. (if ubDom\<cdot>x0 \<noteq> {} then LEAST uua. uua \<in> {usclLen\<cdot>(x0 . c::'a) |c. c \<in> ubDom\<cdot>x0} else \<infinity>) = (if ubDom\<cdot>x0 = {} then \<infinity> else LEAST uua. uua \<in> {usclLen\<cdot>(x0 . c) |c. c \<in> ubDom\<cdot>x0})"
            by auto
          then have f7: "\<forall>u. ubLen u = (if ubDom\<cdot>u = {} then \<infinity> else LEAST l. l \<in> {usclLen\<cdot>(u . c::'a) |c. c \<in> ubDom\<cdot>u})"
            by (simp add: ubLen_def)
          have "\<exists>c. usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c1) = usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c) \<and> c \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)"
            using \<open>(c1::channel) \<in> ubDom\<cdot> (ubUnion\<cdot>(z::'a::uscl_pcpo\<^sup>\<Omega>)\<cdot> (zz::'a::uscl_pcpo\<^sup>\<Omega>))\<close> by auto
          then have "usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c1) \<in> {usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c) |c. c \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)}"
            by blast
          then have "(LEAST l. l \<in> {usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c) |c. c \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)}) \<le> usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c1) \<and> usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c1) \<le> (LEAST l. l \<in> {usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c) |c. c \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)})"
            using f6 f5 f1 by (metis (no_types, lifting) \<open>\<forall>c::channel\<in>ubDom\<cdot> (ubUnion\<cdot> (z::'a::uscl_pcpo\<^sup>\<Omega>)\<cdot> (zz::'a::uscl_pcpo\<^sup>\<Omega>)). usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . (c1::channel)) \<le> usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c)\<close>)
          then have "(LEAST l. l \<in> {usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c) |c. c \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)}) = usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c1)"
            using eq_iff by blast
          then show ?thesis
            using f7 f4 by presburger
        qed
    then show ?thesis
      using assms c1_def ubunion_getchL by fastforce
  next
    case False
    then have "\<forall> c\<in>ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz). usclLen\<cdot>((ubUnion\<cdot>z\<cdot>zz) . c2) \<le> usclLen\<cdot>((ubUnion\<cdot>z\<cdot>zz) . c)"
      apply(simp)
      apply(subst ubunion_getchR)
      using assms c2_def apply blast
      by (metis (no_types, lifting) Un_iff c1_min c2_min dual_order.trans le_cases ubunion_getchL ubunion_getchR)
    moreover have "c2 \<in>ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)"
      by (simp add: c2_def)
    ultimately have "ubLen (ubUnion\<cdot>z\<cdot>zz) = usclLen\<cdot>((ubUnion\<cdot>z\<cdot>zz) . c2)"
      proof -
        have f1: "ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz) \<noteq> {}"
          by (metis \<open>(c2::channel) \<in> ubDom\<cdot> (ubUnion\<cdot>(z::'a::uscl_pcpo\<^sup>\<Omega>)\<cdot> (zz::'a::uscl_pcpo\<^sup>\<Omega>))\<close> all_not_in_conv)
        obtain cc :: "'a\<^sup>\<Omega> \<Rightarrow> channel" where
          f2: "\<And>u. (cc u \<in> ubDom\<cdot>u \<or> ubDom\<cdot>u = {}) \<and> (usclLen\<cdot>(u . cc u) = (LEAST l. l \<in> {usclLen\<cdot>(u . c) |c. c \<in> ubDom\<cdot>u}) \<or> ubDom\<cdot>u = {})"
          using ublen_min_on_channel by moura
        then have f3: "\<And>u. ubDom\<cdot>u = {} \<or> usclLen\<cdot>Rep_ubundle u\<rightharpoonup>cc u = (LEAST l. l \<in> {usclLen\<cdot>(u . c) |c. c \<in> ubDom\<cdot>u})"
          proof -
            fix u :: "'a\<^sup>\<Omega>"
            { assume "(LEAST l. l \<in> {usclLen\<cdot>(u . c) |c. c \<in> ubDom\<cdot>u}) \<noteq> usclLen\<cdot>(u . cc u)"
              then have "ubDom\<cdot>u = {} \<or> usclLen\<cdot>Rep_ubundle u\<rightharpoonup>cc u = (LEAST l. l \<in> {usclLen\<cdot>(u . c) |c. c \<in> ubDom\<cdot>u})"
                using f2 by force }
            then show "ubDom\<cdot>u = {} \<or> usclLen\<cdot>Rep_ubundle u\<rightharpoonup>cc u = (LEAST l. l \<in> {usclLen\<cdot>(u . c) |c. c \<in> ubDom\<cdot>u})"
              by (metis (no_types) ubgetch_insert)
          qed
        then have "\<And>l u. l \<notin> {usclLen\<cdot>(u . c) |c. c \<in> ubDom\<cdot>u} \<or> ubDom\<cdot>u = {} \<or> usclLen\<cdot>Rep_ubundle u\<rightharpoonup>cc u \<le> l"
          by (metis (no_types, lifting) Least_le mem_Collect_eq)
        then have f4: "\<And>l u. (\<forall>c. l \<noteq> usclLen\<cdot>(u . c) \<or> c \<notin> ubDom\<cdot>u) \<or> usclLen\<cdot>Rep_ubundle u\<rightharpoonup>cc u \<le> l"
          by auto
        have "cc (ubUnion\<cdot>z\<cdot>zz) \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)"
          using f2 f1 by blast
        then have "usclLen\<cdot> Rep_ubundle (ubUnion\<cdot>z\<cdot>zz)\<rightharpoonup>cc (ubUnion\<cdot>z\<cdot>zz) = usclLen\<cdot>Rep_ubundle (ubUnion\<cdot>z\<cdot>zz)\<rightharpoonup>c2"
          using f4 by (metis (no_types) \<open>(c2::channel) \<in> ubDom\<cdot> (ubUnion\<cdot>(z::'a::uscl_pcpo\<^sup>\<Omega>)\<cdot> (zz::'a::uscl_pcpo\<^sup>\<Omega>))\<close> \<open>\<forall>c::channel\<in>ubDom\<cdot> (ubUnion\<cdot> (z::'a::uscl_pcpo\<^sup>\<Omega>)\<cdot> (zz::'a::uscl_pcpo\<^sup>\<Omega>)). usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . (c2::channel)) \<le> usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c)\<close> dual_order.antisym ubgetch_insert)
        then have "(LEAST l. l \<in> {usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c) |c. c \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)}) = usclLen\<cdot> Rep_ubundle (ubUnion\<cdot>z\<cdot>zz)\<rightharpoonup>c2 \<and> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz) \<noteq> {}"
          using f3 f1 by fastforce
        then show ?thesis
          by (simp add: ubLen_def ubgetch_insert)
      qed
    then show ?thesis
      by (simp add: c2_def)
  qed
qed

(* TODO: update to new ufun type 
lemma ufcompH_len_step:
  assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  and "ufIsStrong f1"
  and "ufIsStrong f2"
  and "(ubLen (ub :: 'a ubundle)) < lnsuc\<cdot>(ubLen b)"
  and "ubDom\<cdot>b = ufCompI f1 f2"
  and "ubDom\<cdot>ub = ufCompO f1 f2"
  shows "(ubLen ub) <\<^sup>l ubLen ((ufCompH f1 f2) b\<cdot>ub)"
proof -
  have y0: "ubDom\<cdot>b \<inter> ubDom\<cdot>ub = {}"
    using assms ufCompI_def ufCompO_def by simp

  have y1: "ubDom\<cdot>ub \<noteq> {}"
    by (metis assms(4) inf_ub not_less ubLen_def)

  have y2: "ubLen (b \<uplus> ub) = ubLen ub"
    proof (cases "ubDom\<cdot>b = {}")
      case True
      then show ?thesis
        by (simp add: ubclUnion_ubundle_def)
    next
      case False
      obtain c_b_min where c_b_def: "c_b_min \<in> ubDom\<cdot>b \<and> ubLen b = usclLen\<cdot>(b . c_b_min)"
        by (metis (no_types, lifting) False ubLen_def ublen_min_on_channel)
      obtain c_ub_min where c_ub_def: "c_ub_min \<in> ubDom\<cdot>ub \<and> ubLen ub = usclLen\<cdot>(ub . c_ub_min)"
        by (metis (no_types, lifting) ubLen_def ublen_min_on_channel y1)

      have f1: "dom (Rep_ubundle (b \<uplus> ub)) \<inter> ubclDom\<cdot>ub = ubDom\<cdot>(ubRestrict (ubclDom\<cdot>ub)\<cdot>(b \<uplus> ub))"
        using ubdom_insert by auto
      have f2: "(ubRestrict (ubclDom\<cdot>ub)\<cdot>(b \<uplus> ub)) = ub"
        by (metis ubclRestrict_ubundle_def ubclunion_restrict2)
      then have "c_ub_min \<in> dom (Rep_ubundle (b \<uplus> ub)) \<inter> ubclDom\<cdot>ub"
        using f1 c_ub_def by presburger
      then have f3: "c_ub_min \<in> dom (Rep_ubundle (b \<uplus> ub)) \<and> c_ub_min \<in> ubclDom\<cdot>ub"
        by blast
      have "\<forall>x0 x1. (x1 (x0::lnat) \<longrightarrow> Least x1 \<le> x0) = (\<not> x1 x0 \<or> Least x1 \<le> x0)"
        by fastforce
      then have f5: "\<forall>p l. \<not> p (l::lnat) \<or> Least p \<le> l"
        by (simp add: Least_le)
      have f6: "c_ub_min \<in> ubDom\<cdot>(b \<uplus> ub)"
        by (simp add: f3 ubdom_insert)
      have "\<forall>x0 x1 x2. (x2 \<in> x1 \<longrightarrow> (ubRestrict x1\<cdot>x0) . x2 = (x0 . x2::'a)) = (x2 \<notin> x1 \<or> (ubRestrict x1\<cdot>x0) . x2 = x0 . x2)"
        by fastforce
      then have "\<forall>c C u. c \<notin> C \<or> (ubRestrict C\<cdot>u) . c = (u . c::'a)"
        using ubgetch_ubrestrict by blast
      then have "\<exists>c. usclLen\<cdot>(ub . c_ub_min) = usclLen\<cdot>(b \<uplus> ub . c) \<and> c \<in> ubDom\<cdot>(b \<uplus> ub)"
        using f6 f3 f2 by (metis (no_types))
      then have "\<exists>c. usclLen\<cdot>(ub . c_ub_min) = usclLen\<cdot>(b \<uplus> ub . c) \<and> c \<in> ubDom\<cdot>(b \<uplus> ub)"
        by fastforce
      then have "usclLen\<cdot>(ub . c_ub_min) \<in> {usclLen\<cdot>(b \<uplus> ub . c) |c. c \<in> ubDom\<cdot>(b \<uplus> ub)}"
        by simp
      then have f7: "(LEAST l. l \<in> {usclLen\<cdot>(b \<uplus> ub . c) |c. c \<in> ubDom\<cdot>(b \<uplus> ub)}) \<le> usclLen\<cdot>(ub . c_ub_min)"
        using f5 by presburger

      have f8: "{} \<noteq> dom (Rep_ubundle (b \<uplus> ub))"
        using f3 by blast

    show ?thesis
      proof -
        have f1: "\<And>u. ubLen u = (LEAST l. l \<in> {usclLen\<cdot>(u . c::'a) |c. c \<in> ubDom\<cdot>u}) \<or> dom (Rep_ubundle u) = {}"
          by (simp add: ubLen_def ubdom_insert)
        { assume "usclLen\<cdot>(ub . c_ub_min) \<le> ubLen (b \<uplus> ub)"
          then have "(LEAST l. l \<in> {usclLen\<cdot>(b \<uplus> ub . c) |c. c \<in> ubDom\<cdot>(b \<uplus> ub)}) \<le> usclLen\<cdot>(ub . c_ub_min) \<and> usclLen\<cdot>(ub . c_ub_min) \<le> ubLen (b \<uplus> ub) \<and> dom (Rep_ubundle (b \<uplus> ub)) \<noteq> {}"
            using f8 f7 by blast
          then have "ubLen (b \<uplus> ub) = usclLen\<cdot>(ub . c_ub_min)"
            using f1 by force
        }
      then show ?thesis
          by (metis (full_types) assms(4) c_ub_def lnle2le y0 z1)
      qed
    qed

  have y21: "ubLen ub \<le> ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> ub))"
    (* restricting a bundle can only increase the length
       Proof idea:
       obtain least channel c of (b \<uplus> ub)
       case distinction ubDom\<cdot>(ubRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> ub)) = {}
    *)
  proof-
    obtain c_min where c_def: "c_min \<in> ubDom\<cdot>(b \<uplus> ub) \<and> ubLen (b \<uplus> ub) = usclLen\<cdot>((b \<uplus> ub) . c_min)"
      by (metis (no_types, lifting) assms(4) inf_ub not_less ubLen_def ublen_min_on_channel y2)
    then have cmin_channels: "\<forall> c\<in>ubDom\<cdot>(b \<uplus> ub). usclLen\<cdot>((b \<uplus> ub) . c_min) \<le>  usclLen\<cdot>((b \<uplus> ub) . c)"
      proof -
        have f1: "\<forall>u. ubLen u = (if ubDom\<cdot>u = {} then \<infinity> else LEAST l. l \<in> {usclLen\<cdot>(u . c::'a) |c. c \<in> ubDom\<cdot>u})"
          by (simp add: ubLen_def)
        obtain cc :: channel where
          "(\<exists>v0. v0 \<in> ubDom\<cdot>(b \<uplus> ub) \<and> \<not> usclLen\<cdot>(b \<uplus> ub . c_min) \<le> usclLen\<cdot>(b \<uplus> ub . v0)) = (cc \<in> ubDom\<cdot>(b \<uplus> ub) \<and> \<not> usclLen\<cdot>(b \<uplus> ub . c_min) \<le> usclLen\<cdot>(b \<uplus> ub . cc))"
          by moura
        moreover
        { assume "\<exists>c. usclLen\<cdot>(b \<uplus> ub . cc) = usclLen\<cdot>(b \<uplus> ub . c) \<and> c \<in> ubDom\<cdot>(b \<uplus> ub)"
          then have "\<exists>c. usclLen\<cdot>(b \<uplus> ub . cc) = usclLen\<cdot>(b \<uplus> ub . c) \<and> c \<in> ubDom\<cdot>(b \<uplus> ub)"
            by presburger
          then have "(LEAST l. l \<in> {usclLen\<cdot>(b \<uplus> ub . c) |c. c \<in> ubDom\<cdot>(b \<uplus> ub)}) \<le> usclLen\<cdot>(b \<uplus> ub . cc)"
            by (simp add: Least_le)
          moreover
          { assume "(LEAST l. l \<in> {usclLen\<cdot>(b \<uplus> ub . c) |c. c \<in> ubDom\<cdot>(b \<uplus> ub)}) \<noteq> usclLen\<cdot>(b \<uplus> ub . c_min)"
            then have "ubLen (b \<uplus> ub) \<noteq> (LEAST l. l \<in> {usclLen\<cdot>(b \<uplus> ub . c) |c. c \<in> ubDom\<cdot>(b \<uplus> ub)})"
              using c_def by presburger
            then have "ubDom\<cdot>(b \<uplus> ub) = {}"
              using f1 by meson
            then have "cc \<notin> ubDom\<cdot>(b \<uplus> ub) \<or> usclLen\<cdot>(b \<uplus> ub . c_min) \<le> usclLen\<cdot>(b \<uplus> ub . cc)"
              by (metis (full_types) all_not_in_conv) }
          ultimately have "cc \<notin> ubDom\<cdot>(b \<uplus> ub) \<or> usclLen\<cdot>(b \<uplus> ub . c_min) \<le> usclLen\<cdot>(b \<uplus> ub . cc)"
            by fastforce }
        ultimately show ?thesis
          by auto
      qed
    show ?thesis
    proof(cases "ubDom\<cdot>(ubRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> ub)) = {}")
      case True
      then show ?thesis
        by (simp add: ubLen_def)
    next
      case False
      then show ?thesis
        by (metis (no_types, lifting) IntE c_def cmin_channels ubLen_geI ubdom_insert ubgetch_ubrestrict ubrestrict_ubdom2 y2)
    qed
  qed

  then have y3: "(ubLen ub) <\<^sup>l (ubLen (f1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> ub))))"
  proof -
    have y1: "(ubRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> ub)) \<in> dom (Rep_cufun f1)"
      by (metis (no_types, lifting) Un_Diff_cancel2 Un_assoc assms(5) assms(6) le_iff_sup sup_left_idem ubclDom_ubundle_def ubclRestrict_ubundle_def ubcldom_least_cs ubclunion_ubcldom ubresrict_dom2 ufCompI_def ufCompO_def ufunLeastIDom ufun_ufundom2dom)
    then  show ?thesis
    using assms(2) ufIsStrong_def ubclRestrict_ubundle_def
    by (smt dual_order.trans lnsuc_lnle_emb ubclLen_ubundle_def y21)
  qed

  (* Same for f2 *)
  have y22: "ubLen ub \<le> ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub))"
    proof(cases "ubDom\<cdot>(ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) = {}")
      case True
      then show ?thesis
        by (simp add: ubLen_def)
    next
      case False
      then show ?thesis
       proof -
         have f1: "\<forall>u l. (\<exists>c. c \<in> ubDom\<cdot>u \<and> \<not> l \<le> usclLen\<cdot>(u . c::'a)) \<or> l \<le> ubLen u"
           using ubLen_geI by auto
        obtain cc :: "lnat \<Rightarrow> 'a\<^sup>\<Omega> \<Rightarrow> channel" where
          "\<forall>x0 x1. (\<exists>v2. v2 \<in> ubDom\<cdot>x1 \<and> \<not> x0 \<le> usclLen\<cdot>(x1 . v2)) = (cc x0 x1 \<in> ubDom\<cdot>x1 \<and> \<not> x0 \<le> usclLen\<cdot>(x1 . cc x0 x1))"
          by moura
        then have f2: "\<forall>u l. cc l u \<in> ubDom\<cdot>u \<and> \<not> l \<le> usclLen\<cdot>(u . cc l u) \<or> l \<le> ubLen u"
          using f1 by metis
        then have f3: "ubDom\<cdot>(b \<uplus> ub) \<noteq> {}"
          by (metis (no_types) all_not_in_conv assms(4) leD y2)
        have "\<forall>u. ubLen u = (if ubDom\<cdot>u = {} then \<infinity> else LEAST l. l \<in> {usclLen\<cdot>(u . c::'a) |c. c \<in> ubDom\<cdot>u})"
          by (simp add: ubLen_def)
        then have f4: "\<forall>u. if ubDom\<cdot>u = {} then ubLen u = \<infinity> else ubLen u = (LEAST l. l \<in> {usclLen\<cdot>(u . c::'a) |c. c \<in> ubDom\<cdot>u})"
          by force
        { assume "usclLen\<cdot> ((ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) . cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub))) = usclLen\<cdot> (b \<uplus> ub . cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)))"
          moreover
          { assume "\<exists>c. usclLen\<cdot> ((ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) . cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub))) = usclLen\<cdot>(b \<uplus> ub . c) \<and> c \<in> ubDom\<cdot>(b \<uplus> ub)"
            then have "usclLen\<cdot> ((ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) . cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub))) \<in> {usclLen\<cdot>(b \<uplus> ub . c) |c. c \<in> ubDom\<cdot>(b \<uplus> ub)}"
              by force
            then have "(LEAST l. l \<in> {usclLen\<cdot>(b \<uplus> ub . c) |c. c \<in> ubDom\<cdot>(b \<uplus> ub)}) \<le> usclLen\<cdot> ((ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) . cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)))"
              by (meson wellorder_Least_lemma(2))
            then have ?thesis
              using f4 f3 f2 y2 by auto
          }
          ultimately have "ubLen ub \<le> ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) \<or> cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) \<notin> ubDom\<cdot>(b \<uplus> ub) \<or> cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) \<notin> ufDom\<cdot>f2"
            by blast
        }
        then have "ubLen ub \<le> ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) \<or> cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) \<notin> ubDom\<cdot>(b \<uplus> ub) \<or> cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) \<notin> ufDom\<cdot>f2"
          by (metis (no_types) ubgetch_ubrestrict)
        then show ?thesis
          using f2 by (metis (no_types) IntE ubrestrict_ubdom2)
       qed 
    qed

  then have y4: "(ubLen ub) <\<^sup>l (ubLen (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub))))"
  proof -
    have y1: "(ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) \<in> dom (Rep_cufun f2)"
      using assms(5) assms(6) ufCompI_def
      by (metis (no_types, lifting) Un_Diff_cancel Un_assoc sup.absorb_iff1 sup.right_idem ubclDom_ubundle_def ubclRestrict_ubundle_def ubclUnion_ubundle_def ubcldom_least_cs ubclunion_ubcldom ubresrict_dom2 ubunion_commutative ufCompO_def ufunLeastIDom ufun_ufundom2dom y0)
    then show ?thesis
      using assms(3) ufIsStrong_def ubclRestrict_ubundle_def
      by (smt dual_order.trans lnsuc_lnle_emb ubclLen_ubundle_def y22)
  qed

  show ?thesis
    apply(simp add: ufCompH_def)
    by (smt Un_Diff_cancel2 assms(1) assms(5) assms(6) le_supI1 sup_ge1 sup_ge2 ubclDom_ubundle_def ubclRestrict_ubundle_def ubclunion_ubcldom ufCompI_def ufCompO_def ufRanRestrict y3 y4 z1)
qed

lemma ufComp_strongCausal: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}" and "ufIsStrong f1" and "ufIsStrong f2"
  shows "ufIsStrong (ufComp f1 (f2::'m ubundle ufun))"
  apply (simp add: ufIsStrong_def ufComp_def ubclLen_ubundle_def)
  apply rule+
proof -
  fix b ::"'m ubundle"
  assume a0: "b \<in> dom (Rep_cufun (Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))"
  then have "b \<in> dom (\<lambda>u. (ubclDom\<cdot>u = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 u) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
    by (simp add: assms(1))
  then have a1: "ubDom\<cdot>b = ufCompI f1 f2"
    by (simp add: domIff2 ubclDom_ubundle_def)

  have comp_well: "ufWell (\<Lambda> x. (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
    using assms(1) ufcomp_well by blast

  have ubLen_cont: "ubLen (\<Squnion>i::nat. iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)
                        = (\<Squnion>i::nat. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
    (* Not possible with infinite channels *)
    sorry

  have comp_chain: "chain (\<lambda>i. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
    by (metis (no_types) a1 ch2ch_monofun iter_ufCompH_chain ubclDom_ubundle_def ublen_monofun)


  have ufcompH_iterate_len: "\<And>i. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) < lnsuc\<cdot>(ubLen b) \<Longrightarrow>
    ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) >\<^sup>l (ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
  proof -
    fix i
    assume a2: "ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) < lnsuc\<cdot>(ubLen b)"
    show "ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) >\<^sup>l (ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
      apply(unfold iterate_Suc)
      apply(subst ufcompH_len_step)
      apply(simp_all add: assms a1 a2)
      by (metis a1 iter_ufCompH_dom ubclDom_ubundle_def ufCompO_def)
  qed

  have f10: "(ubLen b) <\<^sup>l (\<Squnion>i::nat. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
  proof (cases "ubLen b = \<infinity>")
    case True
    have "\<And>i. ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) >\<^sup>l (ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
      by (metis (no_types, lifting) True antisym_conv2 comp_chain fold_inf inf_ub lnle_def po_class.chain_def ufcompH_iterate_len)
    then have "(\<Squnion>i::nat. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) = \<infinity>"
      proof -
        have f1: "\<forall>l. \<not> l <\<^sup>l l \<or> \<not> l < \<infinity>"
          by (metis (lifting) ln_less not_le)
        have f2: "\<forall>n l f. ((l::lnat) \<sqsubseteq> Lub f \<or> \<not> l \<le> f n) \<or> \<not> chain f"
          by (metis (lifting) below_lub lnle_conv)
        have f3: "\<forall>l. l \<sqsubseteq> lnsuc\<cdot>l"
          by (metis less_lnsuc lnle_conv)
        have "lnsuc\<cdot> (\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) = (\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) \<longrightarrow> (\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) = \<infinity>"
          using f1 by (metis (lifting) dual_order.order_iff_strict inf_ub)
        then show ?thesis
          using f3 f2 by (metis (no_types, lifting) \<open>\<And>i::nat. ubLen (iter_ubfix2 (ufCompH (f1::('m::uscl_pcpo\<^sup>\<Omega>) ufun) (f2::('m::uscl_pcpo\<^sup>\<Omega>) ufun)) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) (b::'m::uscl_pcpo\<^sup>\<Omega>)) <\<^sup>l ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)\<close> below_antisym comp_chain l42 unique_inf_lub)
      qed
    then show ?thesis
      by (metis True fold_inf lnat_po_eq_conv)
  next
    case False
    obtain n where f101: "Fin n = ubLen b" by (metis False infI)

    have "(Fin n) <\<^sup>l (\<Squnion>i::nat. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
      proof -
        obtain nn :: "(nat \<Rightarrow> lnat) \<Rightarrow> nat" where
          f1: "\<forall>f. f (nn f) = Lub f \<or> \<not> finite_chain f \<or> \<not> chain f"
          by (metis (no_types) l42)
        have f2: "\<forall>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<sqsubseteq> (\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
          using comp_chain is_ub_thelub by blast
        have f3: "\<forall>l la. \<not> la < l \<or> la < \<infinity>"
          by (metis inf_ub less_le_trans)
        { assume "\<exists>n. \<not> ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) < ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc n) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)"
          then have "\<exists>na. \<not> ubLen (iter_ubfix2 (ufCompH f1 f2) na (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) < Fin (Suc n)"
            using f3 by (metis (full_types) Fin_Suc f101 le2lnle ufcompH_iterate_len)
          then have "(\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) < Fin (Suc n) \<and> ubLen (iter_ubfix2 (ufCompH f1 f2) (nn (\<lambda>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) = (\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) \<longrightarrow> (\<exists>n. \<not> ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<le> ubLen (iter_ubfix2 (ufCompH f1 f2) (nn (\<lambda>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
            using le_less_trans by auto }
        then have "ubLen (iter_ubfix2 (ufCompH f1 f2) (nn (\<lambda>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<noteq> (\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) \<or> \<not> (\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) < Fin (Suc n)"
          using f2 by (metis leD lnle_conv)
        then show ?thesis
          using f1 comp_chain unique_inf_lub
          by (metis (no_types, lifting) Fin_Suc inf_ub leI)
      qed

    then show ?thesis
      by (metis Fin_Suc Fin_leq_Suc_leq f101)
  qed

  show "(ubLen b) <\<^sup>l ubLen (Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)) \<rightleftharpoons> b)"
    apply(simp add: comp_well)
    apply(simp add: ubclDom_ubundle_def a1)
    apply(simp add: ubFix_def)
    by (simp add: f10 ubLen_cont)
qed

lemma ufParComp_strongCausal: assumes "ufIsStrong f1" and "ufIsStrong f2" and "ufCompL f1 f2 = {}" and "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  shows "ufIsStrong (ufParComp f1 (f2::'m ubundle ufun))"
  by (metis assms parallelOperatorEq ufComp_strongCausal)


lemma ufSerComp_strongCausal: assumes "ufIsStrong f1" and "ufIsStrong f2" and "sercomp_well f1 f2" and "ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  shows "ufIsStrong (ufSerComp f1 (f2::'m ubundle ufun))"
  proof -
    obtain uu :: "('m\<^sup>\<Omega>) ufun \<Rightarrow> 'm\<^sup>\<Omega>" where
    f1: "\<forall>u. (\<not> ufIsStrong u \<or> (\<forall>ua. ua \<notin> dom (Rep_cufun u) \<or> ubclLen ua <\<^sup>l ubclLen (u \<rightleftharpoons> ua))) \<and> (ufIsStrong u \<or> uu u \<in> dom (Rep_cufun u) \<and> \<not> ubclLen (uu u) <\<^sup>l ubclLen (u \<rightleftharpoons> uu u))"
      by (metis (full_types) ufIsStrong_def)
    have f2: "ufDom\<cdot>(ufSerComp f1 f2) = ufDom\<cdot>f1"
      by (meson assms(3) ufSerComp_dom)
    have f3: "\<forall>c. ufWell c = ((\<exists>C. \<forall>u. ((u::'m\<^sup>\<Omega>) \<in> dom (Rep_cfun c)) = (ubclDom\<cdot>u = C)) \<and> (\<exists>C. \<forall>u. (u::'m\<^sup>\<Omega>) \<notin> ran (Rep_cfun c) \<or> ubclDom\<cdot>u = C))"
      by (simp add: ufWell_def)
    have "ubclLen (uu (ufSerComp f1 f2)) <\<^sup>l ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<and> ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<le> ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<longrightarrow> uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun (ufSerComp f1 f2)) \<or> ubclLen (uu (ufSerComp f1 f2)) <\<^sup>l ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2))"
      using trans_lnle by blast
  then show ?thesis
    by (metis (no_types, lifting) f3 f2 f1 assms(1) assms(2) assms(3) rep_ufun_well ubcldom_least_cs ufIsWeak_def ufSerComp_apply ufisstrong_2_ufisweak ufran_2_ubcldom2 ufunLeastIDom)
  qed


definition emptyfun :: "('m\<^sup>\<Omega>) ufun" where
"emptyfun \<equiv> Abs_cufun (\<lambda>x. (ubDom\<cdot>x = {})\<leadsto>(Abs_ubundle Map.empty))"

lemma emptyfun_mono: "monofun (\<lambda>x. (ubDom\<cdot>x = {})\<leadsto>(Abs_ubundle Map.empty))"
  by (simp add: monofunI some_below ubdom_below)

lemma emptyfun_cont: "cont (\<lambda>x. (ubDom\<cdot>x = {})\<leadsto>(Abs_ubundle Map.empty))"
  apply(rule contI2)
  apply(simp add: emptyfun_mono)
  by (simp add: ubcldom_lub_eq2I some_lub_chain_eq)

lemma emptyfun_dom: "ufDom\<cdot>emptyfun = {}"
proof -
  have f1: "(ubclDom::'a\<^sup>\<Omega> \<rightarrow> channel set) = ubDom"
    using ubclDom_ubundle_def by blast
  have f2: "{c. (None::'a option) \<noteq> None} = (Collect bot::channel set)"
    by blast
  have f3: "\<And>u. ubDom\<cdot>(u::'a\<^sup>\<Omega>) = {c. Rep_ubundle u c \<noteq> None}"
    by (simp add: dom_def ubdom_insert)
  then have f4: "\<And>C. {c. Rep_ubundle (ubclLeast C) c \<noteq> (None::'a option)} = C"
    using f1 by (metis ubcldom_least_cs)
  have f5: "\<And>u ua ub. Rep_cufun u (ua::'a\<^sup>\<Omega>) \<noteq> Some ub \<or> ufDom\<cdot>u = {c. Rep_ubundle ua c \<noteq> None}"
    using f3 f1 by simp
  have "Rep_ubundle (ubclLeast (Collect bot)::'a\<^sup>\<Omega>) = Map.empty"
    using f4 f2 by blast
  then have f6: "(\<lambda>u. (ubclDom\<cdot>(u::'a\<^sup>\<Omega>) = Collect bot)\<leadsto>ubclLeast (Collect bot)) = (\<lambda>u. (ubDom\<cdot>u = {})\<leadsto>Abs_ubundle Map.empty::'a\<^sup>\<Omega>)"
    using f1 by (metis (no_types) bot_set_def ubabs_ubrep)

  show ?thesis
    apply (simp add: ufDom_def ubclDom_ubundle_def)
    proof -
      obtain CC :: "('a\<^sup>\<Omega> \<rightarrow> ('a\<^sup>\<Omega>) option) \<Rightarrow> channel set" where
        f7: "\<And>u. ufDom\<cdot>u = CC (Rep_ufun u)"
        using f4 f3 f1 by (metis (no_types) rep_ufun_well ufWell_def ufunLeastIDom)
      then have "\<And>u ua. {c. Rep_ubundle (u::'a\<^sup>\<Omega>) c \<noteq> None} \<noteq> Collect bot \<or> Some (ubclLeast (Collect bot)) \<noteq> Some (ua::'a\<^sup>\<Omega>) \<or> CC (Rep_ufun (Abs_cufun (\<lambda>u. (ubDom\<cdot>u = {})\<leadsto>Abs_ubundle Map.empty))) = {c. Rep_ubundle u c \<noteq> None}"
        using f6 f5 f3 f1 by (metis (no_types) ufleast_rep_abs)

      then show "(\<Lambda> (f::('a\<^sup>\<Omega>) ufun). ubDom\<cdot>(SOME b::'a\<^sup>\<Omega>. b \<in> dom (Rep_cufun f)))\<cdot>emptyfun = {}"
        using f7 f4 f1 bot_set_def emptyfun_def ufDom_def by metis
    qed
qed

lemma emptyfun_ran: "ufRan\<cdot>emptyfun = {}"
proof -
  have f1: "(ubclDom::'a\<^sup>\<Omega> \<rightarrow> channel set) = ubDom"
    using ubclDom_ubundle_def by blast
  have f2: "{c. (None::'a option) \<noteq> None} = (Collect bot::channel set)"
    by blast
  have f3: "\<And>u. ubDom\<cdot>(u::'a\<^sup>\<Omega>) = {c. Rep_ubundle u c \<noteq> None}"
    by (simp add: dom_def ubdom_insert)
  then have f4: "\<And>C. {c. Rep_ubundle (ubclLeast C) c \<noteq> (None::'a option)} = C"
    using f1 by (metis ubcldom_least_cs)
  have f5: "\<And>u ua ub. Rep_cufun u (ua::'a\<^sup>\<Omega>) \<noteq> Some ub \<or> ufDom\<cdot>u = {c. Rep_ubundle ua c \<noteq> None}"
    using f3 f1 by simp
  have "Rep_ubundle (ubclLeast (Collect bot)::'a\<^sup>\<Omega>) = Map.empty"
    using f4 f2 by blast
  then have f6: "(\<lambda>u. (ubclDom\<cdot>(u::'a\<^sup>\<Omega>) = Collect bot)\<leadsto>ubclLeast (Collect bot)) = (\<lambda>u. (ubDom\<cdot>u = {})\<leadsto>Abs_ubundle Map.empty::'a\<^sup>\<Omega>)"
    using f1 by (metis (no_types) bot_set_def ubabs_ubrep)

  show ?thesis
    apply (simp add: ufRan_def ubclDom_ubundle_def)
    proof -
      have "Some (ubclLeast (Collect bot)) = Some (Abs_ubundle Map.empty::'a\<^sup>\<Omega>)"
        by (metis (full_types) bot_set_def f1 f6 ubdom_empty)

      then show "(\<Lambda> u. ubDom\<cdot> (SOME ua. (ua::'a\<^sup>\<Omega>) \<in> ran (Rep_cufun u)))\<cdot> emptyfun = {}"
        by (metis (no_types) emptyfun_def emptyfun_dom f1 option.sel ubdom_empty ufRan_def ufleast_rep_abs ufran_2_ubcldom2)
    qed
qed


lemma emptyfun_well: "ufWell (\<Lambda> (x::'m\<^sup>\<Omega>). (ubDom\<cdot>x = {})\<leadsto>Abs_ubundle Map.empty)"
    apply (simp add: ufWell_def)
    apply rule
    apply (rule_tac x="{}" in exI)
    apply rule
    apply (simp add: domIff emptyfun_cont ubclDom_ubundle_def)
    apply (rule_tac x="{}" in exI)
    apply rule
    apply (simp add: emptyfun_cont ubclDom_ubundle_def)
    proof-
      fix ba :: "'a\<^sup>\<Omega>"
      obtain uu :: "('m\<^sup>\<Omega> \<Rightarrow> ('a\<^sup>\<Omega>) option) \<Rightarrow> 'a\<^sup>\<Omega> \<Rightarrow> 'm\<^sup>\<Omega>" where
        g1: "\<And>u f. u \<notin> ran f \<or> f (uu f u) = Some u"
        by (meson ran2exists)
      { assume a2: "dom (Rep_ubundle ba) \<noteq> {}"
        then have g2: "(ubDom\<cdot> (uu (\<lambda>u. (ubDom\<cdot>u = {})\<leadsto>Abs_ubundle Map.empty) ba) = {})\<leadsto>Abs_ubundle Map.empty \<noteq> Some ba"
          by (metis (no_types) option.distinct(1) option.sel ubdom_empty ubdom_insert)
        then have g3: "ba \<in> ran (\<lambda>u. (ubDom\<cdot>(u::'m\<^sup>\<Omega>) = {})\<leadsto>Abs_ubundle Map.empty) \<longrightarrow> ubDom\<cdot>ba = {}"
          using g1 by blast
      }
      then show "ba \<in> ran (\<lambda>u. (ubDom\<cdot>(u::'m\<^sup>\<Omega>) = {})\<leadsto>Abs_ubundle Map.empty) \<longrightarrow> ubDom\<cdot>ba = {}"
        using ubdom_insert by blast
    qed


lemma feedbackeq: "ufFeedbackComp f = ufComp f emptyfun"
proof -
  have dom2: "ufDom\<cdot>(ufComp f emptyfun) = ufDom\<cdot>(ufFeedbackComp f)"
(*     by (smt comp_well_def emptyfun_dom emptyfun_ran inf_bot_right sup_bot_left ufCompI_def ufFeedbackComp_dom ufclDom_ufun_def ufclRan_ufun_def ufcomp_I_commu ufunclCompWell_ufun_def ufunclComp_ufun_def ufuncl_comp_dom) *)
  proof -
    have f1: "(\<lambda>u. ubclDom\<cdot> (SOME ua. (ua::'a\<^sup>\<Omega>) \<in> dom (Rep_cufun u))) = Rep_cfun (\<Lambda> u. ubclDom\<cdot>(SOME ua. ua \<in> dom (Rep_cufun u)))"
      by simp
    then have f2: "\<forall>u. ubclDom\<cdot> (SOME ua. (ua::'a\<^sup>\<Omega>) \<in> dom (Rep_cufun ((\<mu>) u))) = ufCompI emptyfun u"
      by (metis (no_types) emptyfun_dom emptyfun_ran sup_bot_left ufCompI_def ufDom_def ufFeedbackComp_dom ufunclFeedbackComp_ufun_def)
    have f3: "\<forall>u. ufunclCompWell (u::('a\<^sup>\<Omega>) ufun) emptyfun"
      by (simp add: comp_well_def emptyfun_ran ufunclCompWell_ufun_def)
    then have "ubclDom\<cdot>(SOME u. u \<in> dom (Rep_cufun ((\<mu>) f))) = ufCompI emptyfun f \<and> ufunclCompWell f emptyfun"
      by (simp add: f2)
  then show ?thesis
    using f1 by (metis (no_types) ufCompI_def ufDom_def ufclDom_ufun_def ufclRan_ufun_def ufcomp_I_commu ufunclComp_ufun_def ufunclFeedbackComp_ufun_def ufuncl_comp_dom)
  qed

  have ran2: "ufRan\<cdot>(ufComp f emptyfun) = ufRan\<cdot>(ufFeedbackComp f)"
  proof -
    have f1: "(\<lambda>u. ubclDom\<cdot> (SOME ua. (ua::'a\<^sup>\<Omega>) \<in> dom (Rep_cufun u))) = Rep_cfun (\<Lambda> u. ubclDom\<cdot>(SOME ua. ua \<in> dom (Rep_cufun u)))"
      by simp
    then have f2: "\<forall>u. ubclDom\<cdot> (SOME ua. (ua::'a\<^sup>\<Omega>) \<in> dom (Rep_cufun ((\<mu>) u))) = ufCompI emptyfun u"
      by (metis (no_types) emptyfun_dom emptyfun_ran sup_bot_left ufCompI_def ufDom_def ufFeedbackComp_dom ufunclFeedbackComp_ufun_def)
    have f3: "\<forall>u. ufunclCompWell (u::('a\<^sup>\<Omega>) ufun) emptyfun"
      by (simp add: comp_well_def emptyfun_ran ufunclCompWell_ufun_def)
    then have "ubclDom\<cdot>(SOME u. u \<in> dom (Rep_cufun ((\<mu>) f))) = ufCompI emptyfun f \<and> ufunclCompWell f emptyfun"
      by (simp add: f2)
  then show ?thesis
    by (metis (no_types, lifting) ufclRan_ufun_def ufunclComp_ufun_def emptyfun_ran sup_bot.left_neutral sup_commute ufFeedbackComp_ran ufuncl_comp_ran)
  qed

  have f1: "\<And>sb::'a\<^sup>\<Omega>. ubclDom\<cdot>sb = ufDom\<cdot>(ufFeedbackComp f) \<Longrightarrow> ((ufComp f emptyfun)\<rightleftharpoons>sb) = ((ufFeedbackComp f)\<rightleftharpoons>sb)"
  proof - 
    fix sb :: "'a\<^sup>\<Omega>"
    assume a1: "ubclDom\<cdot>sb = ufDom\<cdot>(ufFeedbackComp f)"
    then have z1: "ubclDom\<cdot>sb = ufDom\<cdot>f - ufRan\<cdot>f"
      by (simp add: ufFeedbackComp_dom)
    have z2: "ufRan\<cdot>f \<inter> ufRan\<cdot>emptyfun = {}"
      by (simp add: emptyfun_ran)
    have z3: "\<And>i. (iter_ubfix2 (ufCompH f emptyfun) i (ufRan\<cdot>f) sb) = (iter_ubfix2 (ufFeedH f) i (ufRan\<cdot>f) sb)"
    proof(induct_tac i)  
      show "iter_ubfix2 (ufCompH f emptyfun) (0::nat) (ufRan\<cdot>f) sb = iter_ubfix2 (ufFeedH f) (0::nat) (ufRan\<cdot>f) sb"
        by simp
      show "\<And>n::nat.
         iter_ubfix2 (ufCompH f emptyfun) n (ufRan\<cdot>f) sb = iter_ubfix2 (ufFeedH f) n (ufRan\<cdot>f) sb \<Longrightarrow>
         iter_ubfix2 (ufCompH f emptyfun) (Suc n) (ufRan\<cdot>f) sb = iter_ubfix2 (ufFeedH f) (Suc n) (ufRan\<cdot>f) sb"
        proof -
          fix n :: nat
          assume a1: "iter_ubfix2 (ufCompH f emptyfun) n (ufRan\<cdot>f) sb = iter_ubfix2 (ufFeedH f) n (ufRan\<cdot>f) sb"
          have "\<And>u ua. ubRestrict (ubclDom\<cdot>u)\<cdot>(Abs_ubundle (Rep_ubundle (ua::'a\<^sup>\<Omega>) ++ Rep_ubundle u)) = u"
            by (metis ubclDom_ubundle_def ubunion_insert ubunion_restrict)
          then show "iter_ubfix2 (ufCompH f emptyfun) (Suc n) (ufRan\<cdot>f) sb = iter_ubfix2 (ufFeedH f) (Suc n) (ufRan\<cdot>f) sb"
            proof -
              have f1: "\<forall>C. ubDom\<cdot>(ubclLeast C::'a\<^sup>\<Omega>) = C"
                by (metis ubclLeast_ubundle_def ubleast_ubdom)
              have f2: "\<forall>u ua. {} \<noteq> ubDom\<cdot>(u::'a\<^sup>\<Omega>) \<inter> ubDom\<cdot>ua \<or> u \<uplus> ua = ua \<uplus> u"
                by (metis ubclUnion_ubundle_def ubunion_commutative)
              have f3: "iter_ubfix2 (ufCompH f emptyfun) (Suc n) (ufRan\<cdot>f) sb = ufCompH f emptyfun sb\<cdot>(iter_ubfix2 (ufFeedH f) n (ufRan\<cdot>f) sb)"
                by (metis a1 iterate_Suc)
              have "\<forall>u. dom (Rep_ubundle (u::'a\<^sup>\<Omega>)) = ubclDom\<cdot>u"
                using f1 by (metis (no_types) ubcldom_least ubdom_below ubdom_insert)
              then show ?thesis
                using f3 f2 by (metis (no_types) empty_subsetI emptyfun_dom emptyfun_ran inf_bot_left iterate_Suc ubclUnion_ubundle_def ubdom_insert ubunion_idL ufFeedH_insert ufRanRestrict ufcomph_insert)
            qed
        qed
    qed

  show "((ufComp f emptyfun)\<rightleftharpoons>sb) = ((ufFeedbackComp f)\<rightleftharpoons>sb)"
    apply (simp add: ufComp_def ufFeedbackComp_def)
    apply (subst rep_abs_cufun)
    apply (simp_all add: emptyfun_ran)
    apply (simp add: z1 z2 ufCompI_def emptyfun_dom emptyfun_ran)
    apply (subst rep_abs_cufun)
    apply (simp add: ufFeedbackComp_cont)
    apply (simp add: ufFeedbackComp_well)
    apply (simp add: z1)
    apply (simp add: ubFix_def)
    using z3 by simp
  qed

show ?thesis
  by (simp add: f1 dom2 ufun_eqI)
qed


lemma ufFeedbackComp_strongCausal: assumes "ufIsStrong (f::'m ubundle ufun)" 
  shows "ufIsStrong (ufFeedbackComp f)"
proof -
  have f1: "ufIsStrong emptyfun"
    by (metis (no_types, lifting) emptyfun_ran inf_ub rep_ufun_well ubLen_def ubclDom_ubundle_def ubclLen_ubundle_def ubcldom_least_cs ufIsStrong_def ufWell_def ufran_2_ubcldom2 ufunLeastIDom)
  have f2: "ufIsStrong (ufComp f emptyfun)"
    by (simp add: assms emptyfun_ran f1 ufComp_strongCausal)
  show ?thesis
    apply (subst feedbackeq)
    by (simp add: assms f2)
qed

lemma ufParComp_weakstrong_weakCausal: assumes "ufIsWeak f1" and "ufIsStrong f2" and "ufCompL f1 f2 = {}" and "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  shows "ufIsWeak (ufParComp f1 (f2::'m ubundle ufun))"
  sorry

lemma ufParComp_strongweak_weakCausal: assumes "ufIsStrong f1" and "ufIsWeak f2" and "ufCompL f1 f2 = {}" and "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  shows "ufIsWeak (ufParComp f1 (f2::'m ubundle ufun))"
  by (metis assms(1) assms(2) assms(3) assms(4) inf_commute ufParComp_commutativity ufParComp_weakstrong_weakCausal ufcomp_L_commu)

lemma ufSerComp_strongweak_strongCausal: assumes "ufIsStrong f1" and "ufIsWeak f2" and "sercomp_well f1 f2" and "ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  shows "ufIsStrong (ufSerComp f1 (f2::'m ubundle ufun))"
proof -
have "\<forall>l la lb. (\<not> (l::lnat) \<le> la \<or> \<not> lb \<le> l) \<or> lb \<le> la"
  by auto
  then have f1: "\<forall>l la lb. \<not> (l::lnat) \<le> la \<or> \<not> lb \<le> l \<or> lb \<le> la"
    by meson
  have "\<forall>u. ufIsStrong u = (\<forall>ua. (ua::'m\<^sup>\<Omega>) \<notin> dom (Rep_cufun u) \<or> ubclLen ua <\<^sup>l ubclLen (u \<rightleftharpoons> ua))"
    by (simp add: ufIsStrong_def)
  then obtain uu :: "('m\<^sup>\<Omega>) ufun \<Rightarrow> 'm\<^sup>\<Omega>" where
    f2: "\<forall>u. (\<not> ufIsStrong u \<or> (\<forall>ua. ua \<notin> dom (Rep_cufun u) \<or> ubclLen ua <\<^sup>l ubclLen (u \<rightleftharpoons> ua))) \<and> (ufIsStrong u \<or> uu u \<in> dom (Rep_cufun u) \<and> \<not> ubclLen (uu u) <\<^sup>l ubclLen (u \<rightleftharpoons> uu u))"
    by (metis (no_types))
  have f3: "\<forall>u ua ub. (u::'m\<^sup>\<Omega>) \<notin> dom (Rep_cufun ua) \<or> ub \<notin> dom (Rep_cufun ua) \<or> ubclDom\<cdot>u = ubclDom\<cdot>ub"
    by (meson ufun_dom2ufundom)
  obtain uua :: "('m\<^sup>\<Omega>) ufun \<Rightarrow> 'm\<^sup>\<Omega>" where
    f4: "\<forall>u. uua u \<in> dom (Rep_cufun u)"
    by (meson ufdom_not_empty)
  have f5: "\<forall>c. ufWell c = ((\<exists>C. \<forall>u. ((u::'m\<^sup>\<Omega>) \<in> dom (Rep_cfun c)) = (ubclDom\<cdot>u = C)) \<and> (\<exists>C. \<forall>u. (u::'m\<^sup>\<Omega>) \<notin> ran (Rep_cfun c) \<or> ubclDom\<cdot>u = C))"
    by (simp add: ufWell_def)
  obtain CC :: "('m\<^sup>\<Omega> \<rightarrow> ('m\<^sup>\<Omega>) option) \<Rightarrow> channel set" where
    f6: "\<forall>x0. (\<exists>v1. \<forall>v2. v2 \<notin> ran (Rep_cfun x0) \<or> ubclDom\<cdot>v2 = v1) = (\<forall>v2. v2 \<notin> ran (Rep_cfun x0) \<or> ubclDom\<cdot>v2 = CC x0)"
    by moura
  obtain uub :: "channel set \<Rightarrow> ('m\<^sup>\<Omega> \<rightarrow> ('m\<^sup>\<Omega>) option) \<Rightarrow> 'm\<^sup>\<Omega>" where
    f8: "\<forall>x0 x1. (\<exists>v2. v2 \<in> ran (Rep_cfun x1) \<and> ubclDom\<cdot>v2 \<noteq> x0) = (uub x0 x1 \<in> ran (Rep_cfun x1) \<and> ubclDom\<cdot>(uub x0 x1) \<noteq> x0)"
    by moura
  obtain uuc :: "channel set \<Rightarrow> ('m\<^sup>\<Omega> \<rightarrow> ('m\<^sup>\<Omega>) option) \<Rightarrow> 'm\<^sup>\<Omega>" where
    "\<forall>x0 x1. (\<exists>v2. (v2 \<in> dom (Rep_cfun x1)) \<noteq> (ubclDom\<cdot>v2 = x0)) = ((uuc x0 x1 \<in> dom (Rep_cfun x1)) \<noteq> (ubclDom\<cdot>(uuc x0 x1) = x0))"
    by moura
  then have "\<forall>c. ((\<forall>C. \<exists>u. (u \<in> dom (Rep_cfun c)) \<noteq> (ubclDom\<cdot>u = C)) \<or> (\<forall>C. \<exists>u. u \<in> ran (Rep_cfun c) \<and> ubclDom\<cdot>u \<noteq> C)) = ((\<forall>C. (uuc C c \<in> dom (Rep_cfun c)) \<noteq> (ubclDom\<cdot>(uuc C c) = C)) \<or> (\<forall>C. uub C c \<in> ran (Rep_cfun c) \<and> ubclDom\<cdot>(uub C c) \<noteq> C))"
    using f8 by auto
  have "\<forall>x0 x1. ((uuc x0 x1 \<in> dom (Rep_cfun x1)) \<noteq> (ubclDom\<cdot>(uuc x0 x1) = x0)) = ((uuc x0 x1 \<notin> dom (Rep_cfun x1)) = (ubclDom\<cdot>(uuc x0 x1) = x0))"
    by meson
  have "ubclDom\<cdot>(ubclLeast (ufDom\<cdot>f1)::'m\<^sup>\<Omega>) = ubclDom\<cdot>(uua f1)"
    using f4 f3 by (metis ufunLeastIDom)
  have "\<forall>u. ufIsWeak u = (\<forall>ua. (ua::'m\<^sup>\<Omega>) \<notin> dom (Rep_cufun u) \<or> ubclLen ua \<le> ubclLen (u \<rightleftharpoons> ua))"
    by (simp add: ufIsWeak_def)
  then have f12: "\<forall>u. u \<notin> dom (Rep_cufun f2) \<or> ubclLen u \<le> ubclLen (f2 \<rightleftharpoons> u)"
    using assms(2) by blast
  have f13: "ubclDom\<cdot>(ubclLeast (ufDom\<cdot>f2)::'m\<^sup>\<Omega>) = ubclDom\<cdot>(uua f2)"
    using f4 f3 by (metis ufunLeastIDom)
  have "\<forall>x0 x1 x2. (ufRan\<cdot>(x2::('m\<^sup>\<Omega>) ufun) = ufDom\<cdot>x1 \<and> ufDom\<cdot>x2 \<inter> ufRan\<cdot>x2 = {} \<and> ufDom\<cdot>x1 \<inter> ufRan\<cdot>x1 = {} \<and> ubclDom\<cdot>(x0::'m\<^sup>\<Omega>) = ufDom\<cdot>(ufSerComp x2 x1)) = (ufRan\<cdot>x2 = ufDom\<cdot>x1 \<and> ufDom\<cdot>x2 \<inter> ufRan\<cdot>x2 = {} \<and> ufDom\<cdot>x1 \<inter> ufRan\<cdot>x1 = {} \<and> ubclDom\<cdot>x0 = ufDom\<cdot>(ufSerComp x2 x1))"
    by auto
  then have f14: "ubclDom\<cdot>(uu (ufSerComp f1 f2)) \<noteq> ufDom\<cdot>(ufSerComp f1 f2) \<or> ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2) = f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))"
    by (meson assms(3) ufSerComp_apply)
  have "ufDom\<cdot>(ufSerComp f1 f2) = ufDom\<cdot>f1"
    by (meson assms(3) ufSerComp_dom)
  moreover
  { assume "\<not> ubclLen (uu (ufSerComp f1 f2)) <\<^sup>l ubclLen (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)))"
    then have "\<not> ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<le> ubclLen (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))) \<or> \<not> ubclLen (uu (ufSerComp f1 f2)) <\<^sup>l ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))"
      using f1 by meson
    then have "ubclDom\<cdot>(uu (ufSerComp f1 f2)) = ufDom\<cdot>f1 \<longrightarrow> uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun (ufSerComp f1 f2)) \<or> ubclLen (uu (ufSerComp f1 f2)) <\<^sup>l ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2))"
      by (metis assms(1) assms(3) f12 f2 ubcldom_least_cs ufran_2_ubcldom2 ufunLeastIDom ufun_ufundom2dom) }
  ultimately have "uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun (ufSerComp f1 f2)) \<or> ubclLen (uu (ufSerComp f1 f2)) <\<^sup>l ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2))"
    using f14 by (metis (no_types) assms(3) domIff ufSerComp_repAbs)
  then show ?thesis
    using f2 by blast
qed

lemma ufSerComp_weakstrong_strongCausal: assumes "ufIsWeak f1" and "ufIsStrong f2" and "sercomp_well f1 f2" and "ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  shows "ufIsStrong (ufSerComp f1 (f2::'m ubundle ufun))"
proof -
obtain uu :: "('m\<^sup>\<Omega>) ufun \<Rightarrow> 'm\<^sup>\<Omega>" where
  f1: "\<forall>u. (\<not> ufIsStrong u \<or> (\<forall>ua. ua \<notin> dom (Rep_cufun u) \<or> ubclLen ua <\<^sup>l ubclLen (u \<rightleftharpoons> ua))) \<and> (ufIsStrong u \<or> uu u \<in> dom (Rep_cufun u) \<and> \<not> ubclLen (uu u) <\<^sup>l ubclLen (u \<rightleftharpoons> uu u))"
  by (metis (no_types) ufIsStrong_def)
  have f2: "\<forall>l la lb. \<not> (l::lnat) \<le> la \<or> \<not> lb \<le> l \<or> lb \<le> la"
    by force
  have f3: "ubclDom\<cdot>(uu (ufSerComp f1 f2)) \<noteq> ufDom\<cdot>(ufSerComp f1 f2) \<or> ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2) = f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))"
    using assms(3) ufSerComp_apply by blast
  have f4: "ufDom\<cdot>(ufSerComp f1 f2) = ufDom\<cdot>f1"
using assms(3) ufSerComp_dom by auto
  have f5: "\<forall>u. u \<notin> dom (Rep_cufun f2) \<or> ubclLen u \<le> ubclLen (f2 \<rightleftharpoons> u)"
    using assms(2) ufIsWeak_def ufisstrong_2_ufisweak by auto
  { assume "\<not> ubclLen (uu (ufSerComp f1 f2)) <\<^sup>l ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2))"
    { assume "\<not> ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) <\<^sup>l ubclLen (uu (ufSerComp f1 f2))"
      moreover
      { assume "\<not> ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) <\<^sup>l ubclLen (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)))"
        then have "f1 \<rightleftharpoons> uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun f2)"
          using f1 assms(2) by auto
        then have "ubclDom\<cdot>(f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<noteq> ubclDom\<cdot>(ubclLeast (ufDom\<cdot>f2)::'m\<^sup>\<Omega>)"
          by (metis (no_types) ufunLeastIDom ufun_ufundom2dom) }
ultimately have "\<not> ubclLen (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))) \<le> ubclLen (uu (ufSerComp f1 f2)) \<or> ubclDom\<cdot>(f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<noteq> ubclDom\<cdot>(ubclLeast (ufDom\<cdot>f2)::'m\<^sup>\<Omega>)"
  using f2 by blast }
  moreover
  { assume "ubclLen (uu (ufSerComp f1 f2)) <\<^sup>l ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<noteq> ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) <\<^sup>l ubclLen (uu (ufSerComp f1 f2))"
    moreover
    { assume "ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<noteq> ubclLen (uu (ufSerComp f1 f2))"
      moreover
      { assume "ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<noteq> ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))"
        then have "ubclLen (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))) \<noteq> ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<or> ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2) \<noteq> f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))"
          by auto
        then have "\<not> ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<le> ubclLen (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))) \<or> uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun f1) \<or> \<not> ubclLen (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))) \<le> ubclLen (uu (ufSerComp f1 f2)) \<or> ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2) \<noteq> f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))"
          using f2 by (meson assms(1) lnat_po_eq_conv ufIsWeak_def) }
      ultimately have "ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<noteq> ubclLen (uu (ufSerComp f1 f2)) \<or> \<not> ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<le> ubclLen (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))) \<or> uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun f1) \<or> \<not> ubclLen (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))) \<le> ubclLen (uu (ufSerComp f1 f2)) \<or> ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2) \<noteq> f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))"
        by force }
    moreover
    { assume "ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<noteq> ubclLen (uu (ufSerComp f1 f2))"
      then have "\<not> ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<le> ubclLen (uu (ufSerComp f1 f2)) \<or> \<not> ubclLen (uu (ufSerComp f1 f2)) \<le> ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))"
        by force
      then have "\<not> ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<le> ubclLen (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))) \<or> uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun f1) \<or> \<not> ubclLen (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))) \<le> ubclLen (uu (ufSerComp f1 f2))"
        using f2 assms(1) ufIsWeak_def by blast }
    ultimately have "ubclDom\<cdot>(uu (ufSerComp f1 f2)) = ufDom\<cdot>f1 \<and> ubclDom\<cdot>(f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) = ubclDom\<cdot>(ubclLeast (ufDom\<cdot>f2)::'m\<^sup>\<Omega>) \<and> ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2) = f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<and> ubclLen (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))) \<le> ubclLen (uu (ufSerComp f1 f2)) \<longrightarrow> uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun (ufSerComp f1 f2)) \<or> ubclLen (uu (ufSerComp f1 f2)) <\<^sup>l ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2))"
      using f5 by (metis (no_types) ubcldom_least_cs ufunLeastIDom ufun_ufundom2dom) }
  moreover
  { assume "ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2) \<noteq> f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2))"
    then have "ubclDom\<cdot>(uu (ufSerComp f1 f2)) \<noteq> ufDom\<cdot>f1"
      using f4 f3 by presburger }
  ultimately have "ubclDom\<cdot>(uu (ufSerComp f1 f2)) = ufDom\<cdot>f1 \<longrightarrow> uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun (ufSerComp f1 f2)) \<or> ubclLen (uu (ufSerComp f1 f2)) <\<^sup>l ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2))"
    by (metis (no_types) assms(3) lnle2le not_le_imp_less ubcldom_least_cs ufran_2_ubcldom2)
then have "uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun (ufSerComp f1 f2)) \<or> ubclLen (uu (ufSerComp f1 f2)) <\<^sup>l ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2))"
  by (meson assms(3) domIff ufSerComp_repAbs) }
  then show ?thesis
    using f1 by (metis (no_types))
qed


lemma ufParComp_weakCausal: assumes "ufIsWeak f1" and "ufIsWeak f2" and "ufCompL f1 f2 = {}" and "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  shows "ufIsWeak (ufParComp f1 (f2::'m ubundle ufun))"
proof -
  have dom: "ufDom\<cdot>(ufParComp f1 f2) = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2"
    by (simp add: assms(3) assms(4) ufParComp_dom)
  have ran: "ufRan\<cdot>(ufParComp f1 f2) = ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"
    by (simp add: assms(3) assms(4) ufParComp_ran)

show "ufIsWeak (ufParComp f1 (f2::'m ubundle ufun))"
  apply (simp add:  ufIsWeak_def)
  apply rule+
  proof -
    fix b
    assume a1: "b \<in> dom (Rep_cufun (ufParComp f1 f2))"
    have g1: "ubclDom\<cdot>b = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2"
      using a1 dom ufdom_2ufundom by auto
    have g2: "ubDom\<cdot>(f1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f1)\<cdot>b)) \<inter> ubDom\<cdot>(f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>b)) = {}"
      by (metis Int_absorb1 Un_upper1 assms(4) g1 inf_sup_ord(4) ubclDom_ubundle_def ubrestrict_ubdom2 ufran_2_ubcldom2)

    have g31: "ubLen b \<le> ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>b)"
    proof (cases  "ubDom\<cdot>(ubRestrict (ufDom\<cdot>f1)\<cdot>b) = {}")
      case True
      then show ?thesis 
        by (simp add: ubLen_def)
    next
      case False
      show ?thesis
      proof (cases "ubDom\<cdot>(b)={}")
        case True
        then show ?thesis by (simp add: ubLen_def)
      next
        case False
        obtain c_min where c_def: "c_min \<in> ubDom\<cdot>(b) \<and> ubLen (b) = usclLen\<cdot>((b) . c_min)"
        proof -
          assume a1: "\<And>c_min. c_min \<in> ubDom\<cdot>b \<and> ubLen b = usclLen\<cdot>(b . c_min) \<Longrightarrow> thesis"
          have z1: "\<exists>l. l \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b}"
            using False by blast
          then have z2: "(LEAST l. l \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b}) \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b}"
            by (meson LeastI)
          then have z3: "(\<exists>c. (LEAST l. l \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b}) = usclLen\<cdot>(b . c) \<and> c \<in> ubDom\<cdot>b) \<and> {} \<noteq> ubDom\<cdot>b"
            by blast
          then have z4: "\<exists>c. ubLen b = usclLen\<cdot>(b . c) \<and> c \<in> ubDom\<cdot>b"
            by (simp add: ubLen_def False)
          then show ?thesis
            using a1 by blast
        qed

        then have cmin_channels: "\<forall> c\<in>ubDom\<cdot>(b). usclLen\<cdot>((b) . c_min) \<le>  usclLen\<cdot>((b) . c)"
        proof -
          obtain cc :: "channel set \<Rightarrow> channel" where
            "\<forall>C. (cc C \<in> C \<or> C = {}) \<and> ((\<forall>c. c \<notin> C) \<or> C \<noteq> {})"
            by moura
          then have f1: "\<forall>C c. (cc C \<in> C \<or> C = {}) \<and> (c \<notin> C \<or> C \<noteq> {})"
            by (metis (no_types))
          have f2: "\<forall>u. ubLen u = (if ubDom\<cdot>u = {} then \<infinity> else LEAST l. l \<in> {usclLen\<cdot>(u . c::'m) |c. c \<in> ubDom\<cdot>u})"
            by (simp add: ubLen_def)
          obtain cca :: channel where
            "(\<exists>v0. v0 \<in> ubDom\<cdot>b \<and> \<not> usclLen\<cdot>(b . c_min) \<le> usclLen\<cdot>(b . v0)) = (cca \<in> ubDom\<cdot>b \<and> \<not> usclLen\<cdot>(b . c_min) \<le> usclLen\<cdot>(b . cca))"
            by blast
          moreover
          { assume "\<exists>c. usclLen\<cdot>(b . cca) = usclLen\<cdot>(b . c) \<and> c \<in> ubDom\<cdot>b"
            then have "(LEAST l. l \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b}) \<le> usclLen\<cdot>(b . cca)"
              by (simp add: Least_le)
            moreover
            { assume "(LEAST l. l \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b}) \<noteq> usclLen\<cdot>(b . c_min)"
              then have "ubLen b \<noteq> (LEAST l. l \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b})"
                using c_def by presburger
              then have "cca \<notin> ubDom\<cdot>b \<or> usclLen\<cdot>(b . c_min) \<le> usclLen\<cdot>(b . cca)"
                using f2 f1 by meson
            }
            ultimately have "cca \<notin> ubDom\<cdot>b \<or> usclLen\<cdot>(b . c_min) \<le> usclLen\<cdot>(b . cca)"
              by force
          }
        ultimately show ?thesis
          by blast
        qed
  
      then show ?thesis
        by (simp add: c_def ubLen_geI)
      qed
    qed

    then have g3: "ubLen b \<le> ubLen (f1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f1)\<cdot>b))"
    proof -
      have y1: "(ubRestrict (ufDom\<cdot>f1)\<cdot>(b)) \<in> dom (Rep_cufun f1)"
        by (metis (no_types) domIff g1 inf_commute inf_sup_absorb option.collapse rep_ufun_well ubclDom_ubundle_def ubrestrict_ubdom2 ubundle_ex ufWell_def ufdom_2ufundom)
      have x2: "ubclLen b \<le> ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>(b))"
        by (simp add: ubclLen_ubundle_def order_trans g31)
      then have x3: "ubclLen b \<le> ubclLen (ubRestrict (ufDom\<cdot>f1)\<cdot>(b))"
        using  order_trans by (simp add: ubclLen_ubundle_def)
      then have x4: "\<exists>l\<le>ubclLen (f1 \<rightleftharpoons> ubRestrict (ufDom\<cdot>f1)\<cdot>(b)). ubclLen b \<le> l"
        by (metis assms(1) ufIsWeak_def y1)
      then have x5: "ubclLen b \<le> ubclLen (f1 \<rightleftharpoons> ubRestrict (ufDom\<cdot>f1)\<cdot>(b))"
        by (meson trans_lnle)

    then show ?thesis
      using  order_trans by (simp add: ubclLen_ubundle_def)
    qed

    have g41: "ubLen b \<le> ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>b)"
    proof (cases  "ubDom\<cdot>(ubRestrict (ufDom\<cdot>f2)\<cdot>b) = {}")
      case True
      then show ?thesis 
        by (simp add: ubLen_def)
    next
      case False
      show ?thesis
      proof (cases "ubDom\<cdot>(b)={}")
        case True
        then show ?thesis by (simp add: ubLen_def)
      next
        case False
        obtain c_min where c_def: "c_min \<in> ubDom\<cdot>(b) \<and> ubLen (b) = usclLen\<cdot>((b) . c_min)"
        proof -
          assume a1: "\<And>c_min. c_min \<in> ubDom\<cdot>b \<and> ubLen b = usclLen\<cdot>(b . c_min) \<Longrightarrow> thesis"
          have z1: "\<exists>l. l \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b}"
            using False by blast
          then have z2: "(LEAST l. l \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b}) \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b}"
            by (meson LeastI)
          then have z3: "(\<exists>c. (LEAST l. l \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b}) = usclLen\<cdot>(b . c) \<and> c \<in> ubDom\<cdot>b) \<and> {} \<noteq> ubDom\<cdot>b"
            by blast
          then have z4: "\<exists>c. ubLen b = usclLen\<cdot>(b . c) \<and> c \<in> ubDom\<cdot>b"
            by (simp add: ubLen_def False)
          then show ?thesis
            using a1 by blast
        qed

        then have cmin_channels: "\<forall> c\<in>ubDom\<cdot>(b). usclLen\<cdot>((b) . c_min) \<le>  usclLen\<cdot>((b) . c)"
        proof -
          obtain cc :: "channel set \<Rightarrow> channel" where
            "\<forall>C. (cc C \<in> C \<or> C = {}) \<and> ((\<forall>c. c \<notin> C) \<or> C \<noteq> {})"
            by moura
          then have f1: "\<forall>C c. (cc C \<in> C \<or> C = {}) \<and> (c \<notin> C \<or> C \<noteq> {})"
            by (metis (no_types))
          have f2: "\<forall>u. ubLen u = (if ubDom\<cdot>u = {} then \<infinity> else LEAST l. l \<in> {usclLen\<cdot>(u . c::'m) |c. c \<in> ubDom\<cdot>u})"
            by (simp add: ubLen_def)
          obtain cca :: channel where
            "(\<exists>v0. v0 \<in> ubDom\<cdot>b \<and> \<not> usclLen\<cdot>(b . c_min) \<le> usclLen\<cdot>(b . v0)) = (cca \<in> ubDom\<cdot>b \<and> \<not> usclLen\<cdot>(b . c_min) \<le> usclLen\<cdot>(b . cca))"
            by blast
          moreover
          { assume "\<exists>c. usclLen\<cdot>(b . cca) = usclLen\<cdot>(b . c) \<and> c \<in> ubDom\<cdot>b"
            then have "(LEAST l. l \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b}) \<le> usclLen\<cdot>(b . cca)"
              by (simp add: Least_le)
            moreover
            { assume "(LEAST l. l \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b}) \<noteq> usclLen\<cdot>(b . c_min)"
              then have "ubLen b \<noteq> (LEAST l. l \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b})"
                using c_def by presburger
              then have "cca \<notin> ubDom\<cdot>b \<or> usclLen\<cdot>(b . c_min) \<le> usclLen\<cdot>(b . cca)"
                using f1 f2 by meson
            }
            ultimately have "cca \<notin> ubDom\<cdot>b \<or> usclLen\<cdot>(b . c_min) \<le> usclLen\<cdot>(b . cca)"
              by force
          }
        ultimately show ?thesis
          by blast
        qed
  
      then show ?thesis
        by (simp add: c_def ubLen_geI)
      qed
    qed

    then have g4: "ubLen b \<le> ubLen (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>b))"
    proof -
      have y1: "(ubRestrict (ufDom\<cdot>f2)\<cdot>(b)) \<in> dom (Rep_cufun f2)"
      proof -
        obtain uu :: "channel set \<Rightarrow> 'm\<^sup>\<Omega>" where
          "\<forall>C. ubclDom\<cdot>(uu C) = C"
          using ubundle_ex by moura
        then show ?thesis
          by (metis (no_types) domIff g1 inf_commute inf_sup_absorb inf_sup_aci(5) option.collapse rep_ufun_well ubclDom_ubundle_def ubrestrict_ubdom2 ufWell_def ufdom_2ufundom)
      qed
      have x2: "ubclLen b \<le> ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>(b))"
        by (simp add: ubclLen_ubundle_def order_trans g41)
      then have x3: "ubclLen b \<le> ubclLen (ubRestrict (ufDom\<cdot>f2)\<cdot>(b))"
        using  order_trans by (simp add: ubclLen_ubundle_def)
      then have x4: "\<exists>l\<le>ubclLen (f2 \<rightleftharpoons> ubRestrict (ufDom\<cdot>f2)\<cdot>(b)). ubclLen b \<le> l"
        by (metis assms(2) ufIsWeak_def y1)
      then have x5: "ubclLen b \<le> ubclLen (f2 \<rightleftharpoons> ubRestrict (ufDom\<cdot>f2)\<cdot>(b))"
        by (meson trans_lnle)

    then show ?thesis
      using  order_trans by (simp add: ubclLen_ubundle_def)
    qed

    
  show "ubclLen b \<le> ubclLen (ufParComp f1 f2 \<rightleftharpoons> b)"
    apply (simp add: ufParComp_def ubclLen_ubundle_def)
    apply (subst rep_abs_cufun)
    apply (simp add: ufParComp_cont)
    apply (simp add: assms(3) assms(4) ufParComp_well)
    apply (simp add: g1)
    by (metis ubclRestrict_ubundle_def z1 g2 g3 g4)
  qed
qed


lemma ufSerComp_weakCausal: assumes "ufIsWeak f1" and "ufIsWeak f2" and "sercomp_well f1 f2" and "ufDom\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  shows "ufIsWeak (ufSerComp f1 (f2::'m ubundle ufun))"
  proof -
    obtain uu :: "('m\<^sup>\<Omega>) ufun \<Rightarrow> 'm\<^sup>\<Omega>" where
      f1: "\<forall>u. (\<not> ufIsWeak u \<or> (\<forall>ua. ua \<notin> dom (Rep_cufun u) \<or> ubclLen ua \<le> ubclLen (u \<rightleftharpoons> ua))) \<and> (ufIsWeak u \<or> uu u \<in> dom (Rep_cufun u) \<and> \<not> ubclLen (uu u) \<le> ubclLen (u \<rightleftharpoons> uu u))"
      by (metis (no_types) ufIsWeak_def)
    obtain uua :: "('m\<^sup>\<Omega>) ufun \<Rightarrow> 'm\<^sup>\<Omega>" where
      f2: "\<forall>u. (\<not> ufIsStrong u \<or> (\<forall>ua. ua \<notin> dom (Rep_cufun u) \<or> ubclLen ua <\<^sup>l ubclLen (u \<rightleftharpoons> ua))) \<and> (ufIsStrong u \<or> uua u \<in> dom (Rep_cufun u) \<and> \<not> ubclLen (uua u) <\<^sup>l ubclLen (u \<rightleftharpoons> uua u))"
      by (metis (no_types) ufIsStrong_def)
  
    have "Rep_cufun (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u))) = Rep_cufun (ufSerComp f1 f2)"
      by (simp add: ufSerComp_def)
    then have f12: "(ubclDom\<cdot>(uu (ufSerComp f1 f2)) = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) = Rep_cufun (ufSerComp f1 f2) (uu (ufSerComp f1 f2))"
      using assms by (simp add: ufSerComp_repAbs assms)
    { assume "ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<le> ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2))"
      then have "ubclLen (uu (ufSerComp f1 f2)) \<le> ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<longrightarrow> uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun (ufSerComp f1 f2)) \<or> ubclLen (uu (ufSerComp f1 f2)) \<le> ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2))"
        using trans_lnle by blast
      then have "ubclDom\<cdot>(uu (ufSerComp f1 f2)) = ufDom\<cdot>(ufSerComp f1 f2) \<longrightarrow> uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun (ufSerComp f1 f2)) \<or> ubclLen (uu (ufSerComp f1 f2)) \<le> ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2))"
        by (metis domIff ufdom_2_dom_ctufun f1 assms(1) f12)
    }
    moreover
    { assume "\<not> ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<le> ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2))"
      moreover
      { assume "\<not> ubclLen (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)) \<le> ubclLen (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> uu (ufSerComp f1 f2)))"
        then have "Rep_cufun (ufSerComp f1 f2) (uu (ufSerComp f1 f2)) = None"
          by (metis ufun_ufundom2dom f12 f1  assms(2) assms(3) ubcldom_least_cs ufran_2_ubcldom2 ufunLeastIDom)
        then have "uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun (ufSerComp f1 f2)) \<or> ubclLen (uu (ufSerComp f1 f2)) \<le> ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2))"
          by (meson domIff)
      }
      ultimately have "ubclDom\<cdot>(uu (ufSerComp f1 f2)) = ufDom\<cdot>(ufSerComp f1 f2) \<longrightarrow> uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun (ufSerComp f1 f2)) \<or> ubclLen (uu (ufSerComp f1 f2)) \<le> ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2))"
        by (metis (no_types) assms(3) ufSerComp_apply)
    }
    moreover
    { assume "ubclDom\<cdot>(uu (ufSerComp f1 f2)) \<noteq> ufDom\<cdot>(ufSerComp f1 f2)"
      moreover
      { assume "ubclDom\<cdot> (uua (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u)))) \<noteq> ubclDom\<cdot>(uu (ufSerComp f1 f2))"
        then have "uu (ufSerComp f1 f2) \<in> dom (Rep_cufun (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u)))) \<longrightarrow> uua (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u))) \<notin> dom (Rep_cufun (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u)))) \<or> ubclLen (uua (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u)))) <\<^sup>l ubclLen (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u)) \<rightleftharpoons> uua (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u))))"
          by (meson ufun_dom2ufundom)
        then have "(uua (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u))) \<notin> dom (Rep_cufun (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u)))) \<or> ubclLen (uua (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u)))) <\<^sup>l ubclLen (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u)) \<rightleftharpoons> uua (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u))))) \<or> uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun (ufSerComp f1 f2)) \<or> ubclLen (uu (ufSerComp f1 f2)) \<le> ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2))"
          by (simp add: ufSerComp_def)
      }
      moreover
      { assume "uua (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u))) \<notin> dom (Rep_cufun (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u)))) \<or> ubclLen (uua (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u)))) <\<^sup>l ubclLen (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u)) \<rightleftharpoons> uua (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u))))"
        then have "ufIsStrong (Abs_cufun (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> (f1 \<rightleftharpoons> u)))"
          using f2 by blast
        then have ?thesis
          by (simp add: ufSerComp_def ufisstrong_2_ufisweak)
      }
      ultimately have "ufIsWeak (ufSerComp f1 f2) \<or> uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun (ufSerComp f1 f2)) \<or> ubclLen (uu (ufSerComp f1 f2)) \<le> ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2))"
        by (metis (no_types) ubcldom_least_cs ufunLeastIDom ufun_dom2ufundom)
    }
    ultimately have "ufIsWeak (ufSerComp f1 f2) \<or> uu (ufSerComp f1 f2) \<notin> dom (Rep_cufun (ufSerComp f1 f2)) \<or> ubclLen (uu (ufSerComp f1 f2)) \<le> ubclLen (ufSerComp f1 f2 \<rightleftharpoons> uu (ufSerComp f1 f2))"
      by linarith
  then show ?thesis
    using f1 by (metis (no_types))
qed
*)

end