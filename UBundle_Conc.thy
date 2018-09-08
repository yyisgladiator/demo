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

lemma maybe_newassms1: "usclLen\<cdot>\<bottom> = 0"
  sorry
lemma maybe_newassms2: "\<And> x . usclConc x\<cdot>\<bottom> = x"
  sorry
lemma maybe_newassms3: "\<And> x . usclConc \<bottom>\<cdot>x = x"
  sorry
lemma maybe_newassms4: "usclLen\<cdot>(usclConc s1\<cdot>s2) = usclLen\<cdot>s1 + usclLen\<cdot>s2"
  sorry
lemma usclLen_all_channel_bigger: assumes "cLen \<in> ubDom\<cdot>b \<and> ubLen b = usclLen\<cdot>(b  .  cLen)" shows "\<And>c::channel. c \<in> ubDom\<cdot>b \<Longrightarrow> usclLen\<cdot>(b  .  cLen) \<le> usclLen\<cdot>(b  .  c)"
(*in comp_caus bewiesen*)
(*wohin? nach ubundle.thy?*)
  sorry


lemma ubLen_smallereq_all: "\<And> c . c \<in> ubDom\<cdot>ub \<Longrightarrow> ubLen ub \<le> usclLen\<cdot>(ub . c)"
proof -
  fix c
  assume cindom: "c \<in> ubDom\<cdot>ub"
  show "ubLen ub \<le> usclLen\<cdot>(ub . c)"
    by (metis (no_types, lifting) cindom empty_iff ubLen_def ublen_min_on_channel usclLen_all_channel_bigger)
qed

lemma ubconc_uscllen_one1: "\<And> c . c \<in> ubDom\<cdot>b1 \<Longrightarrow> c \<notin> ubDom\<cdot>b2 \<Longrightarrow> usclLen\<cdot>((ubConc b1\<cdot>b2) . c) = usclLen\<cdot>(b1 . c)"
  by (simp add: maybe_newassms2 ubconc_getch)
lemma ubconc_uscllen_one2: "\<And> c . c \<in> ubDom\<cdot>b2 \<Longrightarrow> c \<notin> ubDom\<cdot>b1 \<Longrightarrow> usclLen\<cdot>((ubConc b1\<cdot>b2) . c) = usclLen\<cdot>(b2 . c)"
  by (simp add: maybe_newassms3 ubconc_getch)
lemma ubconc_uscllen_both: "\<And> c . c \<in> ubDom\<cdot>b1 \<Longrightarrow> c \<in> ubDom\<cdot>b2 \<Longrightarrow> usclLen\<cdot>((ubConc b1\<cdot>b2) . c) = usclLen\<cdot>(b1 . c) + usclLen\<cdot>(b2 . c)"
  by (simp add: maybe_newassms4)


lemma ubconc_ublen2: assumes "ubclDom\<cdot>b1 \<subseteq> ubclDom\<cdot>b2 \<or> ubclDom\<cdot>b2 \<subseteq> ubclDom\<cdot>b1" shows "ubLen (ubConc b1\<cdot>b2) \<le> (ubLen b1) + (ubLen b2)"
proof -
  have "ubDom\<cdot>b1 = {} \<Longrightarrow> ubLen (ubConc b1\<cdot>b2) \<le> ubLen b1 + ubLen b2"
    by (simp add: plus_lnatInf_r ubLen_def)
  moreover
  have "ubDom\<cdot>b2 = {} \<Longrightarrow> ubLen (ubConc b1\<cdot>b2) \<le> ubLen b1 + ubLen b2"
    by (simp add: plus_lnatInf_r ubLen_def)
  moreover

  have "ubDom\<cdot>b1 \<noteq> {} \<Longrightarrow> ubDom\<cdot>b2 \<noteq> {} \<Longrightarrow> ubLen (ubConc b1\<cdot>b2) \<le> ubLen b1 + ubLen b2"
  proof -
    assume b1notempty: "ubDom\<cdot>b1 \<noteq> {}"
    assume b2notempty: "ubDom\<cdot>b2 \<noteq> {}"

    obtain c0minLen where c0minLen_def: "c0minLen \<in> ubDom\<cdot>(ubConc b1\<cdot>b2) \<and> ubLen (ubConc b1\<cdot>b2) = usclLen\<cdot>((ubConc b1\<cdot>b2) . c0minLen)"
      by (metis (no_types, lifting) Un_iff b2notempty empty_iff ubLen_def ubconc_dom ublen_min_on_channel)
    then have c0minLen_min: "\<forall> c \<in> ubDom\<cdot>(ubConc b1\<cdot>b2) . usclLen\<cdot>((ubConc b1\<cdot>b2) . c0minLen) \<le> usclLen\<cdot>((ubConc b1\<cdot>b2) . c)"
      using usclLen_all_channel_bigger by blast

    have "ubclDom\<cdot>b1 \<subseteq> ubclDom\<cdot>b2 \<Longrightarrow> ubLen (ubConc b1\<cdot>b2) \<le> ubLen b1 + ubLen b2"
(*c0minLen \<notin> ubclDom\<cdot>b1 \<Longrightarrow> ubLen (ubConc b1\<cdot>b2) = ubLen b2"*)
      sorry

    moreover

    have "ubclDom\<cdot>b2 \<subseteq> ubclDom\<cdot>b1 \<Longrightarrow> ubLen (ubConc b1\<cdot>b2) \<le> ubLen b1 + ubLen b2"
(*c0minLen \<notin> ubclDom\<cdot>b2 \<Longrightarrow> ubLen (ubConc b1\<cdot>b2) = ubLen b1"*)
      sorry

    then show ?thesis
      using assms calculation by blast
  qed

  then show ?thesis
    using calculation by blast
qed

lemma ubconc_dom2: "(ubDom\<cdot>b1 \<subseteq> ubDom\<cdot>(ubConc b1\<cdot>b2)) \<and> (ubDom\<cdot>b2 \<subseteq> ubDom\<cdot>(ubConc b1\<cdot>b2))"
  by simp
lemma ubconc_dom3: "\<And> b2 . ubDom\<cdot>b1 \<subseteq> ubDom\<cdot>(ubConc b1\<cdot>b2)"
  by simp
lemma ubconc_dom4: "\<And> b1 . ubDom\<cdot>b2 \<subseteq> ubDom\<cdot>(ubConc b1\<cdot>b2)"
  by simp

lemma ubconceq_ublen2: assumes "ubclDom\<cdot>b1 \<subseteq> ubclDom\<cdot>b2 \<or> ubclDom\<cdot>b2 \<subseteq> ubclDom\<cdot>b1" shows "ubLen (ubConcEq b1\<cdot>b2) \<le> (ubLen b1) + (ubLen b2)"
proof (simp add: ubConcEq_def)
  have "ubDom\<cdot>b2 = {} \<Longrightarrow> ubLen ((ubConc b1\<cdot>b2) \<bar> ubDom\<cdot>b2) \<le> ubLen b1 + ubLen b2"
    by (simp add: ubLen_def)
  moreover
  have "ubDom\<cdot>b1 = {} \<Longrightarrow> ubLen ((ubConc b1\<cdot>b2) \<bar> ubDom\<cdot>b2) \<le> ubLen b1 + ubLen b2"
    by (simp add: plus_lnatInf_r ubLen_def)
  moreover

  have "ubDom\<cdot>b1 \<noteq> {} \<Longrightarrow> ubDom\<cdot>b2 \<noteq> {} \<Longrightarrow> ubLen ((ubConc b1\<cdot>b2) \<bar> ubDom\<cdot>b2) \<le> ubLen b1 + ubLen b2"
  proof -
    assume b1notempty: "ubDom\<cdot>b1 \<noteq> {}"
    assume b2notempty: "ubDom\<cdot>b2 \<noteq> {}"

    obtain c0minLen where c0minLen_def: "c0minLen \<in> ubDom\<cdot>(ubConc b1\<cdot>b2) \<and> ubLen (ubConc b1\<cdot>b2) = usclLen\<cdot>((ubConc b1\<cdot>b2) . c0minLen)"
      by (metis (no_types, lifting) Un_iff b2notempty empty_iff ubLen_def ubconc_dom ublen_min_on_channel)

    have "c0minLen \<in> ubDom\<cdot>b2 \<Longrightarrow> ubLen ((ubConc b1\<cdot>b2) \<bar> ubDom\<cdot>b2) \<le> ubLen b1 + ubLen b2"
    proof -
      assume c0inb2: "c0minLen \<in> ubDom\<cdot>b2"
      then have "(ubConc b1\<cdot>b2 \<bar> ubDom\<cdot>b2) . c0minLen = ubConc b1\<cdot>b2 . c0minLen"
        using ubgetch_ubrestrict by blast
      then show ?thesis
        using c0inb2 by (metis (no_types) assms c0minLen_def dual_order.trans ubLen_smallereq_all ubconc_ublen2 ubconceq_dom ubconceq_insert)
    qed

    moreover

    have "\<not> (c0minLen \<in> ubDom\<cdot>b2) \<Longrightarrow> ubLen ((ubConc b1\<cdot>b2) \<bar> ubDom\<cdot>b2) \<le> ubLen b1 + ubLen b2"
    proof -
      assume c0notb2: "\<not> (c0minLen \<in> ubDom\<cdot>b2)"
      then have c0inb1: "c0minLen \<in> ubDom\<cdot>b1"
        using c0minLen_def by auto

      have "ubclDom\<cdot>b2 \<subseteq> ubclDom\<cdot>b1"
        by (metis assms c0minLen_def c0notb2 ubclDom_ubundle_def ubconc_dom ubunionDom ubunion_idL)
      have "(ubDom\<cdot>b1 \<union> ubDom\<cdot>b2) \<inter> ubDom\<cdot>b2 \<noteq> {}"
        by (simp add: Int_absorb1 b2notempty)

      have "ubclDom\<cdot>b2 \<subseteq> ubclDom\<cdot>b1 \<Longrightarrow> ubLen ((ubConc b1\<cdot>b2) \<bar> ubDom\<cdot>b2) \<le> ubLen b1 + ubLen b2"
                  apply (simp add: ubLen_def assms b1notempty b2notempty)

        sorry
      then show ?thesis
        by (metis (no_types, lifting) assms c0inb1 c0notb2 subsetCE ubclDom_ubundle_def)
    qed

    then show ?thesis
      using calculation by blast 
  qed

  then show "ubLen ((ubConc b1\<cdot>b2) \<bar> ubDom\<cdot>b2) \<le> ubLen b1 + ubLen b2"
    using calculation by blast
qed


lemma ubleast_len: "cs \<noteq> {} \<Longrightarrow> usclLen\<cdot>(\<bottom> :: 'a) = 0 \<Longrightarrow> ubLen (ubLeast cs :: 'a ubundle) = 0"
proof -
  fix cs :: "channel set"
  assume cs_nempty: "cs \<noteq> {}"
  assume len_zero: "usclLen\<cdot>(\<bottom> :: 'a) = 0"
  obtain c where c_def: "c \<in> cs"
    using cs_nempty by blast
  have "usclLen\<cdot>((ubLeast cs :: 'a ubundle)  .  c) = 0"
    by (simp add: c_def len_zero)
  then show "ubLen (ubLeast cs :: 'a ubundle) = (0::lnat)"
    by (metis bot_is_0 c_def dual_order.antisym lnle_def minimal ubLen_smallereq_all ubleast_ubdom)
qed

lemma ubconc_with_ubleast_same_ublen: "ubConc a\<cdot>(ubLeast (ubDom\<cdot>a)) = a"
  proof -
    have a_dom: "ubDom\<cdot>a = ubDom\<cdot>(ubConc a\<cdot>(ubLeast (ubDom\<cdot>a)))"
      by simp
    have ubleast_dom: "ubDom\<cdot>(ubLeast (ubDom\<cdot>a)) = ubDom\<cdot>a"
      by simp

    have for_each: "\<And>c::channel. c \<in> ubDom\<cdot>(ubConc a\<cdot>(ubLeast (ubDom\<cdot>a))) \<Longrightarrow> ubConc a\<cdot>(ubLeast (ubDom\<cdot>a))  .  c = a  .  c"
    proof -
      fix c
      assume a1:  "c \<in> ubDom\<cdot>(ubConc a\<cdot>(ubLeast (ubDom\<cdot>a)))"
      then have a2: "c \<in> ubDom\<cdot>a"
        by auto
      show "ubConc a\<cdot>(ubLeast (ubDom\<cdot>a))  .  c = a  .  c"
      proof (cases "ubDom\<cdot>a = {}")
        case True
        then show ?thesis 
          using a1 a_dom by blast
      next
        case False
        then show ?thesis
          by (simp add: a2 maybe_newassms2)
      qed
    qed

(*     have "ubLen a = ubLen (ubConc a\<cdot>(ubLeast (ubDom\<cdot>a)))"
      by (metis a_dom for_each ubgetchI) *)

    show ?thesis
      using a_dom for_each ubgetchI by blast
qed

lemma ubconceq_with_ubleast_same_ublen: "ubConcEq a\<cdot>(ubLeast (ubDom\<cdot>a)) = a"
  by (simp add: ubconc_with_ubleast_same_ublen)


end    