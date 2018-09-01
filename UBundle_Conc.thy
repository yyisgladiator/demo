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

subsection \<open>ubConcEq\<close>


lemma ubconceq_cont [simp]: "cont (\<lambda> b2.  (ubConc b1\<cdot>b2) \<bar> ubDom\<cdot>b2)"
  apply(rule contI)
  by (smt ch2ch_Rep_cfunR contlub_cfun_arg cpo_lubI image_cong ubdom_chain_eq2)

lemma ubconceq_insert [simp]: "ubConcEq b1\<cdot>b2 = (ubConc b1\<cdot>b2) \<bar> ubDom\<cdot>b2"
  by(simp add: ubConcEq_def)

lemma ubconceq_dom [simp]: "ubDom\<cdot>(ubConcEq b1\<cdot>b2) = ubDom\<cdot>b2"
  by auto


(* lnatGreater / lnatLess abbrev aus Composition_Causalities in lnat übernehmen*)

(*idee: min streams in beiden müssen im selben channel liegen *)
(*allgemeiner fall ähnlich zu Composition_Causalities.z1? *)
(*ubdom_one assms nötig? *)
lemma ubconc_ublen2: assumes ubdom_one: "ubDom\<cdot>b2 = {c}" and ubdom_eq: "ubDom\<cdot>b1 = ubDom\<cdot>b2" 
  shows "ubLen (ubConc b1\<cdot>b2) = (ubLen b1) + (ubLen b2)"
proof (cases "ubDom\<cdot>b1 = {}")
  case True
  then show ?thesis
    using ubdom_eq ubdom_one by auto
next
  case False

  obtain c1 where c1_def: "c1 \<in> ubDom\<cdot>b1 \<and> ubLen b1 = usclLen\<cdot>(b1 . c1)"
    by (metis (no_types, lifting) False ubLen_def ublen_min_on_channel)
  then have c1_min: "\<forall> c\<in>ubDom\<cdot>b1. usclLen\<cdot>(b1 . c1) \<le> usclLen\<cdot>(b1 . c)"    (*verallgemeinern? min 4mal im projekt*)
  proof -
    have f1: "ubLen b1 = (LEAST l. l \<in> {usclLen\<cdot>(b1 . c) |c. c \<in> ubDom\<cdot>b1})"
      by (simp add: False ubLen_def)
    obtain cc :: channel where
      "(\<exists>v0. v0 \<in> ubDom\<cdot>b1 \<and> \<not> usclLen\<cdot>(b1 . c1) \<le> usclLen\<cdot>(b1 . v0)) = (cc \<in> ubDom\<cdot>b1 \<and> \<not> usclLen\<cdot>(b1 . c1) \<le> usclLen\<cdot>(b1 . cc))"
      by moura
    moreover
    { assume "\<exists>c. usclLen\<cdot>(b1 . cc) = usclLen\<cdot>(b1 . c) \<and> c \<in> ubDom\<cdot>b1"
      then have "(LEAST l. l \<in> {usclLen\<cdot>(b1 . c) |c. c \<in> ubDom\<cdot>b1}) \<le> usclLen\<cdot>(b1 . cc)"
        by (simp add: Least_le)
      then have "cc \<notin> ubDom\<cdot>b1 \<or> usclLen\<cdot>(b1 . c1) \<le> usclLen\<cdot>(b1 . cc)"
        using f1 c1_def by auto }
    ultimately show ?thesis
      by blast
  qed

  obtain c2 where c2_def: "c2 \<in> ubDom\<cdot>b2 \<and> ubLen b2 = usclLen\<cdot>(b2 . c2)"
    by (metis (no_types, lifting) False ubLen_def ubdom_eq ublen_min_on_channel)
  then have c2_min: "\<forall> c\<in>ubDom\<cdot>b2. usclLen\<cdot>(b2 . c2) \<le> usclLen\<cdot>(b2 . c)"
(*sledgeproovable*)
    sorry


  have "ubLen b1 = (usclLen\<cdot>(b1 . c1))"
    by (simp add: c1_def)

  have "ubLen b2 = (usclLen\<cdot>(b2 . c2))"
    by (simp add: c2_def)

  obtain len1:: lnat where len1_def: "len1 = ubLen b1"
    by simp
  obtain len2:: lnat where len1_def: "len2 = ubLen b2"
    by simp

  have c1inset: "c1 \<in>ubDom\<cdot>(ubConcEq b1\<cdot>b2)"
    using c1_def ubconceq_dom ubdom_eq by blast
  have c2inset: "c2 \<in>ubDom\<cdot>(ubConcEq b1\<cdot>b2)"
    using c2_def ubconceq_dom ubdom_eq by blast

(*   have conclen_ohneassms_ubdom_one: "ubLen (ubConcEq b1\<cdot>b2) = usclLen\<cdot>((ubConcEq b1\<cdot>b2) . c1) \<or> ubLen (ubConcEq b1\<cdot>b2) = usclLen\<cdot>((ubConcEq b1\<cdot>b2) . c2)"
    sorry *)

  have conclen1: "ubLen (ubConcEq b1\<cdot>b2) = usclLen\<cdot>((ubConcEq b1\<cdot>b2) . c1)"
    by (metis c1_def singletonD ubconceq_dom ubdom_eq ubdom_one uslen_ubLen_ch3)
  have conclen2: "ubLen (ubConcEq b1\<cdot>b2) = usclLen\<cdot>((ubConcEq b1\<cdot>b2) . c2)"
    using c1_def c2_def conclen1 ubdom_eq ubdom_one by auto


  have test: "usclLen\<cdot>((ubConc b1\<cdot>b2) . c1) = usclLen\<cdot>(usclConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c))"
    using c1_def ubdom_eq ubdom_one by auto


  have "c1 = c"
    using c1_def ubdom_eq ubdom_one by auto
  have "c2 = c"
    using c2_def ubdom_eq ubdom_one by blast


(*   have "\<forall> c\<in>ubDom\<cdot>(ubConcEq b1\<cdot>b2). usclLen\<cdot>((ubUnion\<cdot>z\<cdot>zz) . c1) \<le> usclLen\<cdot>((ubUnion\<cdot>z\<cdot>zz) . c)"
    sorry *)


  show ?thesis


    sorry
qed

lemma ubconceq_ublen2: assumes ubdom_one: "ubDom\<cdot>b2 = {c}" and ubdom_eq: "ubDom\<cdot>b1 = ubDom\<cdot>b2" 
  shows "ubLen (ubConcEq b1\<cdot>b2) = (ubLen b1) + (ubLen b2)"
  by (simp add: ubconc_ublen2 ubdom_eq ubdom_one)


lemma ubleast_len: assumes "cs \<noteq> {}" shows "ubLen (ubLeast cs) = 0"
proof (simp add: ubLen_def assms)

  have null: "usclLen\<cdot>\<bottom> = 0"
    sorry

  have ubleast_all_null: "\<And> c . c\<in>cs \<Longrightarrow> usclLen\<cdot>((ubLeast cs) . c) = 0"
  proof -
    fix c
    assume a1: "c\<in>cs"
    show "usclLen\<cdot>((ubLeast cs) . c) = 0"
    by (simp add: a1 null)
  qed

  obtain ch:: channel where ch_def: "ch\<in>cs"
    using assms by auto
  then have ch_def_is_null: "usclLen\<cdot>((ubLeast cs) . ch) = 0"
    using ubleast_all_null by auto

(*   have exist_ch: "\<exists>c. 0 = usclLen\<cdot>(ubLeast cs . c::'b) \<and> c \<in> cs"
    by (metis ch_def_is_null ch_def) *)
(* dieses lemma sorgt _hier_ im show darunter für "Pending sort hypotheses: uscl_conc" *)
(*innerhalb des ISAR Proofs der jetzt im show steht, geht aber nichts kaputt... ? *)

  show "(LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(ubLeast cs  .  c) \<and> c \<in> cs) = (0::lnat)"
(*     by (smt LeastI ch_def ch_def_is_null lnzero_def ubleast_all_null) *)
    proof -
      have f1: "\<forall>p. Least p = (0::lnat) \<or> \<not> p 0"
        by (metis (no_types) Least_equality lnle_def lnzero_def minimal)
      have "\<exists>c. 0 = usclLen\<cdot>(ubLeast cs . c::'b) \<and> c \<in> cs"
        by (metis ch_def_is_null ch_def)
      then show ?thesis
        using f1 by blast
    qed
qed

(* idee: kA, aber im Moment ist es auf jeden Fall zu tief aufgedröselt*)
lemma ubconc_with_ubleast_same_ublen: "ubConc a\<cdot>(ubLeast (ubDom\<cdot>a)) = a"
  proof -

    have a_dom: "ubDom\<cdot>a = ubDom\<cdot>(ubConc a\<cdot>(ubLeast (ubDom\<cdot>a)))"
      by simp
    have ubleast_dom: "ubDom\<cdot>(ubLeast (ubDom\<cdot>a)) = ubDom\<cdot>a"
      by simp


    have "ubLen a = ubLen (ubConc a\<cdot>(ubLeast (ubDom\<cdot>a)))"
    proof (cases "ubDom\<cdot>a = {}")
      case True
      then show ?thesis 
        by (simp add: ubLen_def)
    next
      case False
      then show ?thesis 
        apply (subst ubconc_ublen2)
          defer
        apply simp
        apply (metis add.right_neutral plus_lnatInf_r ubleast_len ubLen_def)
(*?*)
        sorry
    qed

  show ?thesis
    apply (simp add: ubConc_def)
    apply (simp add: ubgetch_insert)
    apply (simp add: ubRestrict_def)
    apply (subst ubrep_ubabs)
     apply (metis (no_types, lifting) UNIV_I option.sel ubWell_def ubdom_channel_usokay ubgetch_insert ubleast_ubdom ubleast_ubgetch ubup_ubdom usclOkay_conc)
    apply (simp add: ubUp_def)
    
    sorry
qed

lemma ubconceq_with_ubleast_same_ublen: "ubConcEq a\<cdot>(ubLeast (ubDom\<cdot>a)) = a"
  by (simp add: ubconc_with_ubleast_same_ublen)


end