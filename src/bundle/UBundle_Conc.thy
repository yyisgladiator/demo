(*  Title:        UBundle
    Author:       Sebastian, Jens, Marc

    Description:  Defines stream bundles
*)

theory UBundle_Conc  
  imports UBundle UBundle_Pcpo
begin

  
default_sort uscl_conc

  
(****************************************************)
section\<open>Definitions\<close>
(****************************************************)  

  
(* ubConc *)
definition ubConc :: "'M\<^sup>\<Omega> \<Rightarrow> 'M\<^sup>\<Omega> \<rightarrow> 'M\<^sup>\<Omega>"  where
"ubConc b1  \<equiv> \<Lambda> b2. (Abs_ubundle (\<lambda>c. Some (usclConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))) \<bar> (ubDom\<cdot>b1 \<union> ubDom\<cdot>b2)"  

(* ubConcEq *)
definition ubConcEq:: "'M\<^sup>\<Omega> \<Rightarrow> 'M\<^sup>\<Omega> \<rightarrow> 'M\<^sup>\<Omega>"  where
"ubConcEq b1 \<equiv> \<Lambda> b2. (ubConc b1\<cdot>b2) \<bar> ubDom\<cdot>b2"


(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)


subsection \<open>ubConc\<close>


lemma ubconc_well[simp]: "ubWell (\<lambda>c. Some (usclConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))"
  apply(rule ubwellI)
  apply(simp add: ubdom_insert)
  apply(subst usclOkay_conc)
  by(simp_all add: ubgetch_insert)

lemma ubconc_mono[simp]: "monofun (\<lambda> b2. (Abs_ubundle (\<lambda>c. Some (usclConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))) \<bar> (ubDom\<cdot>b1 \<union> ubDom\<cdot>b2))"
proof - 
  have f1 : "monofun (\<lambda> b2. (Abs_ubundle (\<lambda>c. Some (usclConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))))"
    apply(rule monofunI)
    by (smt UNIV_I below_option_def below_ubundle_def fun_belowI monofun_cfun_arg option.distinct(1) option.sel ubdom_channel_usokay ubgetchE ubrep_ubabs ubup_ubdom ubup_ubgetch2 ubwellI usclOkay_conc)
  show ?thesis
    by (smt f1 monofun_cfun_arg monofun_def ubdom_below)
qed

lemma ubconc_cont[simp]: "cont (\<lambda> b2. (Abs_ubundle (\<lambda>c. Some (usclConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))) \<bar> (ubDom\<cdot>b1 \<union> ubDom\<cdot>b2))"
proof -
  have f0 : "monofun (\<lambda> b2. (Abs_ubundle (\<lambda>c. Some (usclConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))))"
    apply(rule monofunI)
    by (smt UNIV_I below_option_def below_ubundle_def fun_belowI monofun_cfun_arg option.distinct(1) option.sel ubdom_channel_usokay ubgetchE ubrep_ubabs ubup_ubdom ubup_ubgetch2 ubwellI usclOkay_conc)
  have f1: "cont (\<lambda> b2. (Abs_ubundle (\<lambda>c. Some (usclConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))))"
    apply(rule contI2)
    using f0 apply simp
    apply rule+
  proof - 
    fix Y:: "nat \<Rightarrow> 'a\<^sup>\<Omega>"
    assume f00: "chain Y"
    have f2: "\<And>i. ubDom\<cdot>(\<Squnion>i::nat. Y i) = ubDom\<cdot>(Y i)"
      by (simp add: \<open>chain (Y::nat \<Rightarrow> 'a\<^sup>\<Omega>)\<close>)
    then have f3: "ubDom\<cdot>(Abs_ubundle (\<lambda>c::channel. Some (usclConc (ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>(\<Squnion>i::nat. Y i)  .  c)))) = UNIV"
      by (simp add: ubdom_ubrep_eq)
    have f4: "\<And>i. ubDom\<cdot>(Abs_ubundle (\<lambda>c::channel. Some (usclConc (ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>(Y i)  .  c)))) = UNIV"
      by (simp add: ubdom_ubrep_eq)
    have f50: "chain (\<lambda>i. Abs_ubundle (\<lambda>c::channel. Some (usclConc (ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>(Y i)  .  c))))"
      apply(simp add: chain_def)
      apply rule+
    proof - 
      fix i
      have f501: "(Y i) \<sqsubseteq> (Y (Suc i))"
        by (simp add: f00 po_class.chainE)
      show "Abs_ubundle (\<lambda>c::channel. Some (usclConc (ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>(Y i)  .  c))) \<sqsubseteq>
              Abs_ubundle (\<lambda>c::channel. Some (usclConc (ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>(Y (Suc i))  .  c)))"
       using f0 f501 monofun_def by fastforce
   qed
    have f5: "ubDom\<cdot>(\<Squnion>i::nat. Abs_ubundle (\<lambda>c::channel. Some (usclConc (ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>(Y i)  .  c)))) = UNIV"
      using f4 f50 ubdom_chain_eq2 by blast 
    have f6: "\<And>c. (usclConc (ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>(Lub Y)  .  c)) \<sqsubseteq> (\<Squnion>i::nat. Abs_ubundle (\<lambda>c::channel. Some (usclConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>(Y i) . c)))) . c"
    proof -
      fix c
      show "(usclConc (ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>(Lub Y)  .  c)) \<sqsubseteq> (\<Squnion>i::nat. Abs_ubundle (\<lambda>c::channel. Some (usclConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>(Y i) . c)))) . c"
      proof - 
        have f7: "(usclConc (ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>(Lub Y)  .  c)) \<sqsubseteq> (\<Squnion>i::nat. (usclConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>(Y i) . c)))"
          by (metis (mono_tags) \<open>chain (Y::nat \<Rightarrow> 'a\<^sup>\<Omega>)\<close> below_refl ch2ch_cont cont_Rep_cfun2 contlub_cfun_arg)
        have f8: "(\<Squnion>i::nat. Abs_ubundle (\<lambda>c::channel. Some (usclConc (ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>(Y i)  .  c))))  .  c = (\<Squnion>i::nat. Abs_ubundle (\<lambda>c::channel. Some (usclConc (ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>(Y i)  .  c))) . c)"
          by (simp add: contlub_cfun_arg f50)
        show ?thesis
          apply(simp add: f8)
          by (smt UNIV_I \<open>chain (Y::nat \<Rightarrow> 'a\<^sup>\<Omega>)\<close> ch2ch_Rep_cfunR contlub_cfun_arg eq_imp_below lub_eq option.sel ubdom_channel_usokay ubgetch_insert ubrep_ubabs ubup_ubdom ubwellI usclOkay_conc)
      qed
    qed
    show "Abs_ubundle (\<lambda>c::channel. Some (usclConc (ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>(\<Squnion>i::nat. Y i)  .  c))) \<sqsubseteq>
       (\<Squnion>i::nat. Abs_ubundle (\<lambda>c::channel. Some (usclConc (ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>(Y i)  .  c))))"
      apply(subst ub_below)
      using f3 f5 apply blast
       apply(simp add: f3 ubgetch_ubrep_eq)
      using f6 by simp_all
  qed
  show ?thesis
    apply(rule contI2)
    using ubconc_mono apply blast
    apply rule+
    apply(rule ubrestrict_below)
    using f1 by simp_all
qed

lemma ubconc_dom[simp]: "ubDom\<cdot>(ubConc b1\<cdot>b2) = ubDom\<cdot>b1 \<union> ubDom\<cdot>b2"
proof -
  have f1: "ubDom\<cdot>(Abs_ubundle (\<lambda>c. Some (usclConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))) = UNIV"
    by (simp add: ubdom_ubrep_eq)
  show ?thesis
    apply(simp add: ubConc_def)
    using f1 by blast
qed

lemma ubConc_usclConc_eq [simp]: assumes "c \<in> (ubDom\<cdot>sb1)"
                              and "c \<in> (ubDom\<cdot>sb2)"
                            shows "(ubConc sb1 \<cdot> sb2) . c = usclConc (sb1. c) \<cdot> (sb2. c)"
  proof -
    have h1: "ubWell (\<lambda>c::channel. Some (usclConc (Rep_ubundle (ubUp\<cdot>sb1)\<rightharpoonup>c) \<cdot> (Rep_ubundle (ubUp\<cdot>sb2)\<rightharpoonup>c)))"
      apply(simp add: ubWell_def )
      by (simp add: usclOkay_conc)
    then show ?thesis
      apply(simp add: ubConc_def assms)
      apply(simp add:  ubgetch_insert h1)
      by (metis assms(1) assms(2) ubgetch_insert ubup_ubgetch)
  qed

lemma ubconc_getch: "c\<in>(ubDom\<cdot>ub1 \<union> ubDom\<cdot>ub2) \<Longrightarrow> (ubConc ub1\<cdot>ub2) . c = usclConc (ubUp\<cdot>ub1 . c)\<cdot>(ubUp\<cdot>ub2 . c)"
  apply(simp add: ubConc_def)
  by (simp add: ubWell_def ubgetch_insert usclOkay_conc)

lemma ubconc_insert: "ubConc b1\<cdot>b2 = (Abs_ubundle (\<lambda>c. Some (usclConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))) \<bar> (ubDom\<cdot>b1 \<union> ubDom\<cdot>b2)"
  by(simp add: ubConc_def)

lemma ubconc_ubleast:
  shows "ubConc (a :: 'a ubundle)\<cdot>(ubLeast (ubDom\<cdot>a)) = a"
  proof -
    have a_dom: "ubDom\<cdot>a = ubDom\<cdot>(ubConc a\<cdot>(ubLeast (ubDom\<cdot>a)))"
      by simp
    have "\<And>c. c \<in> ubDom\<cdot>(ubConc (a :: 'a ubundle)\<cdot>(ubLeast (ubDom\<cdot>a))) 
                \<Longrightarrow> ubConc a\<cdot>(ubLeast (ubDom\<cdot>a))  .  c = a  .  c"
      using usclConc_rightbottom by auto
    then show ?thesis
      using a_dom ubgetchI by blast
  qed

lemma ubconc_uscllen_justub1: "\<And> c . c \<in> ubclDom\<cdot>b1 \<Longrightarrow> c \<notin> ubclDom\<cdot>b2 \<Longrightarrow> usclLen\<cdot>((ubConc b1\<cdot>b2) . c) = usclLen\<cdot>(b1 . c)"
  by (simp add: usclConc_rightbottom ubconc_getch ubclDom_ubundle_def)
lemma ubconc_uscllen_justub2: "\<And> c . c \<in> ubclDom\<cdot>b2 \<Longrightarrow> c \<notin> ubclDom\<cdot>b1 \<Longrightarrow> usclLen\<cdot>((ubConc b1\<cdot>b2) . c) = usclLen\<cdot>(b2 . c)"
  by (simp add: usclConc_leftbottom ubconc_getch ubclDom_ubundle_def)
lemma ubconc_uscllen_both: "\<And> c . c \<in> ubclDom\<cdot>b1 \<Longrightarrow> c \<in> ubclDom\<cdot>b2 \<Longrightarrow> usclLen\<cdot>((ubConc b1\<cdot>b2) . c) = usclLen\<cdot>(b1 . c) + usclLen\<cdot>(b2 . c)"
  by (simp add: usclLen_usclConc ubclDom_ubundle_def)

lemma ubconc_emptyright: assumes "ubclDom\<cdot>b2 = {}" shows "ubConc b1\<cdot>b2 = b1"
proof -
  have "\<And> c. (ubUp\<cdot>b2  .  c) = \<bottom>"
    by (metis assms empty_iff ubclDom_ubundle_def ubup_ubgetch2)
  then have allCinb1: "\<And> c. (usclConc (ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>b2  .  c)) = (ubUp\<cdot>b1  .  c)"
    by (simp add: usclConc_rightbottom)
  have concdom_b1dom: "(ubDom\<cdot>b1 \<union> ubDom\<cdot>b2) = ubDom\<cdot>b1"
    by (metis Un_empty_right assms ubclDom_ubundle_def)
  show ?thesis
  proof (cases "ubDom\<cdot>b1 = {}")
    case True
    then show ?thesis
      by (metis assms empty_iff sup_bot.right_neutral ubclDom_ubundle_def ubconc_dom ubgetchI)
  next
    case False
    then show ?thesis
      by (metis ubconc_dom ubconc_getch ubgetchI ubup_ubgetch concdom_b1dom allCinb1)
  qed
qed

lemma ubconc_emptyleft: assumes "ubclDom\<cdot>b1 = {}" shows "ubConc b1\<cdot>b2 = b2"
proof -
  have "\<And> c. (ubUp\<cdot>b1  .  c) = \<bottom>"
    by (metis assms empty_iff ubclDom_ubundle_def ubup_ubgetch2)
  then have allCinb2: "\<And> c. (usclConc (ubUp\<cdot>b1  .  c)\<cdot>(ubUp\<cdot>b2  .  c)) = (ubUp\<cdot>b2  .  c)"
    by (simp add: usclConc_leftbottom)
  have concdom_b2dom: "(ubDom\<cdot>b1 \<union> ubDom\<cdot>b2) = ubDom\<cdot>b2"
    by (metis assms sup_bot.left_neutral ubclDom_ubundle_def)
  show ?thesis
  proof (cases "ubDom\<cdot>b2 = {}")
    case True
    then show ?thesis
      by (metis assms ubconc_emptyright ubclDom_ubundle_def ubclRestrict_ubundle_def ubclrestrict_dom_id ubrestrict_ubleast)
  next
    case False
    then show ?thesis
  by (metis allCinb2 concdom_b2dom ubconc_dom ubconc_getch ubgetchI ubup_ubgetch)
  qed
qed


lemma ubconc_ubcllen_equalDom: assumes "ubclDom\<cdot>ub1 = ubclDom\<cdot>ub2"
  shows "(ubclLen ub1) + (ubclLen ub2) \<le> ubclLen (ubConc ub1\<cdot>ub2)"
proof (simp add: ubclLen_ubundle_def, cases "ubclDom\<cdot>ub1 = {}")
  case True
  then have ub2leer: "ubclDom\<cdot>ub2 = {}"
    using assms by simp
  then have "ubDom\<cdot>(ubConc ub1\<cdot>ub2) = {}"
    by (metis True sup.idem ubclDom_ubundle_def ubconc_dom)
  then have "ubLen (ubConc ub1\<cdot>ub2) = \<infinity>"
    by (simp add: ubLen_def)
  then show "ubLen ub1 + ubLen ub2 \<le> ubLen (ubConc ub1\<cdot>ub2)"
    by simp
next
  case False
  then have nicht_ub1leer: "ubDom\<cdot>ub1 \<noteq> {}"
    by (simp add: ubclDom_ubundle_def)
  then have nicht_ub2leer: "ubDom\<cdot>ub2 \<noteq> {}"
    by (metis assms ubclDom_ubundle_def)
  then have "ubDom\<cdot>(ubConc ub1\<cdot>ub2) \<noteq> {}"
    by simp
  obtain c where c_def: "c \<in> ubDom\<cdot>(ubConc ub1\<cdot>ub2) \<and> usclLen\<cdot>((ubConc ub1\<cdot>ub2) . c) = ubLen (ubConc ub1\<cdot>ub2)"
    by (metis (no_types, lifting) Un_iff nicht_ub2leer empty_iff ubLen_def ubconc_dom ublen_min_on_channel)
  have ub1min_smallereq_concminch_in_b1: "ubLen ub1 \<le> usclLen\<cdot>(ub1 . c)"
    by (metis Un_iff assms c_def ubLen_smallereq_all ubclDom_ubundle_def ubconc_dom)
  have ub2min_smallereq_concminch_in_b2: "ubLen ub2 \<le> usclLen\<cdot>(ub2 . c)"
    by (metis Un_iff assms c_def ubLen_smallereq_all ubclDom_ubundle_def ubconc_dom)
  have addition_smaller: "ubLen ub1 + ubLen ub2 \<le> usclLen\<cdot>(ub1 . c) + usclLen\<cdot>(ub2 . c)"
    using ub1min_smallereq_concminch_in_b1 ub2min_smallereq_concminch_in_b2 by (simp add: lessequal_addition)
  have concminch_in_b1plussb2_is_ubLenconc: "usclLen\<cdot>(ub1 . c) + usclLen\<cdot>(ub2 . c) = ubLen (ubConc ub1\<cdot>ub2)"
    by (metis Un_absorb assms c_def ubclDom_ubundle_def ubconc_dom ubconc_uscllen_both)

  show "ubLen ub1 + ubLen ub2 \<le> ubLen (ubConc ub1\<cdot>ub2)"
    using addition_smaller concminch_in_b1plussb2_is_ubLenconc by auto
qed


lemma ubconc_ubcllen_diffDom: assumes "ubclDom\<cdot>ub1 \<inter> ubclDom\<cdot>ub2 = {}"
  shows "lnmin\<cdot>(ubclLen ub1)\<cdot>(ubclLen ub2) = ubclLen (ubConc ub1\<cdot>ub2)"
proof (simp add: ubclDom_ubundle_def ubclLen_ubundle_def)
  have "ubDom\<cdot>(ubConc ub1\<cdot>ub2) = {} \<Longrightarrow> ubLen (ubConc ub1\<cdot>ub2) = lnmin\<cdot>(ubLen ub1)\<cdot>(ubLen ub2)"
    by (simp add: ubLen_def)
  moreover
  have "ubDom\<cdot>(ubConc ub1\<cdot>ub2) \<noteq> {} \<Longrightarrow> ubDom\<cdot>ub1 = {} \<Longrightarrow> ubLen (ubConc ub1\<cdot>ub2) = lnmin\<cdot>(ubLen ub1)\<cdot>(ubLen ub2)"
    by (simp add: ubconc_emptyleft ubLen_def ubclDom_ubundle_def)
  moreover
  have "ubDom\<cdot>(ubConc ub1\<cdot>ub2) \<noteq> {} \<Longrightarrow> ubDom\<cdot>ub2 = {} \<Longrightarrow> ubLen (ubConc ub1\<cdot>ub2) = lnmin\<cdot>(ubLen ub1)\<cdot>(ubLen ub2)"
    by (simp add: ubconc_emptyright ubLen_def ubclDom_ubundle_def)
  moreover

  have "ubDom\<cdot>ub1 \<noteq> {} \<Longrightarrow> ubDom\<cdot>ub2 \<noteq> {} \<Longrightarrow> ubLen (ubConc ub1\<cdot>ub2) = lnmin\<cdot>(ubLen ub1)\<cdot>(ubLen ub2)"
  proof -
    assume b1notempty: "ubDom\<cdot>ub1 \<noteq> {}"
    assume b2notempty: "ubDom\<cdot>ub2 \<noteq> {}"
    obtain c0minLen where c0minLen_def: "c0minLen \<in> ubDom\<cdot>(ubConc ub1\<cdot>ub2) \<and> ubLen (ubConc ub1\<cdot>ub2) = usclLen\<cdot>((ubConc ub1\<cdot>ub2) . c0minLen)"
      by (metis (no_types, lifting) Un_iff b2notempty empty_iff ubLen_def ubconc_dom ublen_min_on_channel)
    then have c0minLen_min: "\<forall> c \<in> ubDom\<cdot>(ubConc ub1\<cdot>ub2) . usclLen\<cdot>((ubConc ub1\<cdot>ub2) . c0minLen) \<le> usclLen\<cdot>((ubConc ub1\<cdot>ub2) . c)"
      using usclLen_all_channel_bigger by blast
    have ch_xor: "\<forall> c \<in> ubDom\<cdot>(ubConc ub1\<cdot>ub2) . \<not> (c \<in> ubDom\<cdot>ub1 \<and> c \<in> ubDom\<cdot>ub2)"
      by (metis assms disjoint_iff_not_equal ubclDom_ubundle_def)

    have isinb1: "c0minLen \<in> ubDom\<cdot>ub1 \<Longrightarrow> ubLen (ubConc ub1\<cdot>ub2) = lnmin\<cdot>(ubLen ub1)\<cdot>(ubLen ub2)"
    proof -
      assume c0inub1: "c0minLen \<in> ubDom\<cdot>ub1"
      then have not_c0inub2: "c0minLen \<notin> ubDom\<cdot>ub2"
        using c0minLen_def ch_xor by blast
      have "\<And> c . c \<in> ubDom\<cdot>ub1 \<Longrightarrow> usclLen\<cdot>(ub1 . c) \<ge> usclLen\<cdot>(ub1 . c0minLen)"
        by (metis Un_iff c0inub1 c0minLen_min ch_xor ubconc_dom ubconc_uscllen_justub1 ubclDom_ubundle_def)
      then have ub1Lenisub1Len: "usclLen\<cdot>(ub1 . c0minLen) = ubLen ub1"
        by (metis (no_types, lifting) b1notempty c0inub1 dual_order.antisym ubLen_def ubLen_smallereq_all ublen_min_on_channel)
      then have concLenisub1Len: "ubLen (ubConc ub1\<cdot>ub2) = ubLen ub1"
        by (simp add: c0inub1 c0minLen_def not_c0inub2 ubconc_uscllen_justub1 ubclDom_ubundle_def)
      have concLensmallerub2Len: "ubLen (ubConc ub1\<cdot>ub2) \<le> ubLen ub2"
        by (metis IntI Un_iff assms empty_iff ubLen_geI ubLen_smallereq_all ubclDom_ubundle_def ubconc_dom ubconc_uscllen_justub2)

      show "ubLen (ubConc ub1\<cdot>ub2) = lnmin\<cdot>(ubLen ub1)\<cdot>(ubLen ub2)"
        using concLenisub1Len concLensmallerub2Len lnmin_eqasmthmin by auto
    qed

    have isinb2: "c0minLen \<notin> ubDom\<cdot>ub1 \<Longrightarrow> ubLen (ubConc ub1\<cdot>ub2) = lnmin\<cdot>(ubLen ub1)\<cdot>(ubLen ub2)"
    proof -
      assume not_c0inub1: "c0minLen \<notin> ubDom\<cdot>ub1"
      then have c0inub2: "c0minLen \<in> ubDom\<cdot>ub2"
        using c0minLen_def by (simp add: ch_xor)
      have "\<And> c . c \<in> ubDom\<cdot>ub2 \<Longrightarrow> usclLen\<cdot>(ub2 . c) \<ge> usclLen\<cdot>(ub2 . c0minLen)"
        by (metis Un_iff c0inub2 c0minLen_min ch_xor ubconc_dom ubconc_uscllen_justub2 ubclDom_ubundle_def)
      then have concLenisub2Len: "ubLen (ubConc ub1\<cdot>ub2) = ubLen ub2"
        by (simp add: c0inub2 c0minLen_def dual_order.antisym not_c0inub1 ubLen_geI ubLen_smallereq_all ubconc_uscllen_justub2 ubclDom_ubundle_def)
      have concLensmallerub1Len: "ubLen (ubConc ub1\<cdot>ub2) \<le> ubLen ub1"
        by (metis Un_iff c0minLen_def c0minLen_min ch_xor ubLen_geI ubconc_dom ubconc_uscllen_justub1 ubclDom_ubundle_def)
      show "ubLen (ubConc ub1\<cdot>ub2) = lnmin\<cdot>(ubLen ub1)\<cdot>(ubLen ub2)"
        using concLenisub2Len concLensmallerub1Len lnmin_eqasmthmin lnmin_asso by fastforce
    qed

    show "ubLen (ubConc ub1\<cdot>ub2) = lnmin\<cdot>(ubLen ub1)\<cdot>(ubLen ub2)"
      by (cases "c0minLen \<in> ubDom\<cdot>ub1", simp_all add: isinb1 isinb2)
  qed
  then show "lnmin\<cdot>(ubLen ub1)\<cdot>(ubLen ub2) = ubLen (ubConc ub1\<cdot>ub2)"
    using calculation by argo
qed


lemma ubconc_ublen_onech: assumes ubdom_one: "ubclDom\<cdot>b2 = {c}" and ubdom_eq: "ubclDom\<cdot>b1 = ubclDom\<cdot>b2"
  shows "ubLen (ubConc b1\<cdot>b2) = (ubLen b1) + (ubLen b2)"
proof (cases "ubDom\<cdot>b1 = {}")
  case True
  then show ?thesis
    by (metis (no_types, lifting) bot_eq_sup_iff plus_lnatInf_l ubLen_def ubconc_dom ubdom_eq ubclDom_ubundle_def)
next
  case False

  obtain c1 where c1_def: "c1 \<in> ubDom\<cdot>b1 \<and> ubLen b1 = usclLen\<cdot>(b1 . c1)"
    by (metis (no_types, lifting) False ubLen_def ublen_min_on_channel)
  then have c1_min: "\<forall> c\<in>ubDom\<cdot>b1. usclLen\<cdot>(b1 . c1) \<le> usclLen\<cdot>(b1 . c)"
    using usclLen_all_channel_bigger by blast

  obtain c2 where c2_def: "c2 \<in> ubDom\<cdot>b2 \<and> ubLen b2 = usclLen\<cdot>(b2 . c2)"
    by (metis (no_types, lifting) False ubLen_def ubdom_eq ublen_min_on_channel ubclDom_ubundle_def)
  then have c2_min: "\<forall> c\<in>ubDom\<cdot>b2. usclLen\<cdot>(b2 . c2) \<le> usclLen\<cdot>(b2 . c)"
    using usclLen_all_channel_bigger by blast

  have c1isublenb1: "ubLen b1 = (usclLen\<cdot>(b1 . c1))"
    by (simp add: c1_def)
  have c2isublenb2: "ubLen b2 = (usclLen\<cdot>(b2 . c2))"
    by (simp add: c2_def)

  have conclen: "ubLen (ubConc b1\<cdot>b2) = usclLen\<cdot>((ubConc b1\<cdot>b2) . c1)"
    by (metis c1_def singletonD sup.idem ubconc_dom ubdom_eq ubdom_one uslen_ubLen_ch3 ubclDom_ubundle_def)

  have c1_def: "c1 = c"
    by (metis c1_def singletonD ubclDom_ubundle_def ubdom_eq ubdom_one)
  have c2_def: "c2 = c"
    by (metis c2_def singletonD ubclDom_ubundle_def ubdom_one)

  show ?thesis
    by (simp add: c1_def c1isublenb1 c2_def c2isublenb2 conclen ubconc_uscllen_both ubdom_eq ubdom_one)
qed


lemma ubconc_assoc: "ubConc (ubConc a\<cdot>b)\<cdot>ub = ubConc a\<cdot>(ubConc b\<cdot>ub)"
  apply(rule ub_eq)
   apply auto
  apply (auto simp add: ubconc_getch )
  apply (metis (no_types, lifting) Un_iff ubconc_dom ubconc_getch ubup_ubgetch ubup_ubgetch2 usclConc_assoc usclConc_rightbottom)
  apply (simp add: usclConc_assoc)
  by (metis (no_types, lifting) Un_iff ubconc_dom ubconc_getch ubup_ubgetch ubup_ubgetch2 usclConc_assoc usclConc_rightbottom)


subsection \<open>ubConcEq\<close>


lemma ubconceq_cont [simp]: "cont (\<lambda> b2.  (ubConc b1\<cdot>b2) \<bar> ubDom\<cdot>b2)"
  apply(rule contI)
  by (smt ch2ch_Rep_cfunR contlub_cfun_arg cpo_lubI image_cong ubdom_chain_eq2)

lemma ubconceq_insert: "ubConcEq b1\<cdot>b2 = (ubConc b1\<cdot>b2) \<bar> ubDom\<cdot>b2"
  by(simp add: ubConcEq_def)

lemma ubconceq_dom [simp]: "ubDom\<cdot>(ubConcEq b1\<cdot>b2) = ubDom\<cdot>b2"
  by (simp add: inf.absorb2 ubconceq_insert)

lemma ubconceq_ubleast:
  shows "ubConcEq (a :: 'a ubundle)\<cdot>(ubLeast (ubDom\<cdot>a)) = a"
  by (simp add: usclConc_rightbottom ubconc_ubleast ubconceq_insert)

lemma ubconceq_ubcllen_equalDom: assumes "ubclDom\<cdot>ub1 = ubclDom\<cdot>ub2"
  shows "(ubclLen ub1) + (ubclLen ub2) \<le> ubclLen (ubConcEq ub1\<cdot>ub2)"
  using assms by (simp add: ubclDom_ubundle_def ubconc_ubcllen_equalDom ubconceq_insert)

lemma ubconceq_ubcllen_diffDom: assumes "ubclDom\<cdot>ub1 \<inter> ubclDom\<cdot>ub2 = {}"
  shows "ubclLen ub2 = ubclLen (ubConcEq ub1\<cdot>ub2)"
  apply (simp add: ubclLen_ubundle_def ubconceq_insert)
  apply (simp add: ubLen_def)
  apply (cases "ubDom\<cdot>ub2 = {}")
  apply simp
  apply (cases "(ubDom\<cdot>ub1 \<union> ubDom\<cdot>ub2) \<inter> ubDom\<cdot>ub2 = {}")
  apply blast
  apply rule
  apply simp
  by (metis (no_types, hide_lams) assms disjoint_iff_not_equal ubclDom_ubundle_def ubconc_uscllen_justub2 ubgetch_ubrestrict)

lemma ubconceq_ublen_onech: assumes ubdom_one: "ubclDom\<cdot>b2 = {c}" and ubdom_eq: "ubclDom\<cdot>b1 = ubclDom\<cdot>b2" 
  shows "ubLen (ubConcEq b1\<cdot>b2) = (ubLen b1) + (ubLen b2)"
proof -
  have "ubDom\<cdot>b1 = ubclDom\<cdot>b2"
    by (metis ubclDom_ubundle_def ubdom_eq)
  then have "ubConc b1\<cdot>b2 = ubConcEq b1\<cdot>b2"
    by (simp add: ubclDom_ubundle_def ubconceq_insert)
  then show ?thesis
    by (simp add: ubconc_ublen_onech ubdom_eq ubdom_one ubconceq_insert)
qed

lemma ubconceq_restrict: "ubDom\<cdot>ub2 \<subseteq> cs \<Longrightarrow> ubConcEq (ubRestrict cs\<cdot>ub)\<cdot>ub2 = ubConcEq ub\<cdot>ub2"
  apply(rule ub_eq)
  apply (simp add: ubconceq_insert)
   apply blast
  apply (simp add: ubconceq_insert)
  by (smt IntE IntI Un_iff subset_Un_eq ubconc_getch ubgetch_ubrestrict ubrestrict_ubdom2 ubup_ubgetch ubup_ubgetch2)

lemma conceq_longer_conc: "ubLen (ubConcEq b1\<cdot>b2) \<ge> ubLen (ubConc b1\<cdot>b2)"
  by (simp add: ubLen_geI ubLen_smallereq_all ubconceq_insert)

lemma conceq_conc_1: assumes "ubclDom\<cdot>b1 \<subseteq> ubclDom\<cdot>b2" shows "ubConcEq b1\<cdot>b2 = ubConc b1\<cdot>b2"
  by (metis assms ubclDom_ubundle_def ubclRestrict_ubundle_def ubclrestrict_dom_id ubconc_dom ubconceq_insert ubunionDom ubunion_idL)


lemma ubconceq_assoc: "ubclDom\<cdot>b = ubclDom\<cdot>ub \<Longrightarrow> ubConcEq (ubConcEq a\<cdot>b)\<cdot>ub = ubConcEq a\<cdot>(ubConcEq b\<cdot>ub)"
  apply(simp add: ubConcEq_def ubconc_assoc)
  by (metis conceq_conc_1 inf_sup_absorb sup.idem ubclDom_ubundle_def ubconc_assoc ubconceq_insert ubconceq_restrict ubrestrict_ubdom ubrestrict_ubdom2)


lemma ubConcEq_ubLeast[simp]: "ubConcEq (ubLeast cs)\<cdot>s = s"
  apply(rule ub_eq)
   apply auto
  apply (simp add:ubConcEq_def)
  by (simp add: ubconc_getch usclConc_leftbottom)

lemma ubleast_len: assumes cs_nempty: "cs \<noteq> {}"
  shows "ubLen (ubLeast cs :: 'a ubundle) = 0"
proof -
  obtain c where c_def: "c \<in> cs"
    using cs_nempty by blast
  have "usclLen\<cdot>((ubLeast cs :: 'a ubundle)  .  c) = 0"
    by (simp add: c_def usclLen_bottom)
  then show "ubLen (ubLeast cs :: 'a ubundle) = (0::lnat)"
    by (metis bot_is_0 c_def dual_order.antisym lnle_def minimal ubLen_smallereq_all ubleast_ubdom)
qed

end    