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


subsection \<open>ubConcEq\<close>


lemma ubconceq_cont [simp]: "cont (\<lambda> b2.  (ubConc b1\<cdot>b2) \<bar> ubDom\<cdot>b2)"
  apply(rule contI)
  by (smt ch2ch_Rep_cfunR contlub_cfun_arg cpo_lubI image_cong ubdom_chain_eq2)

lemma ubconceq_insert [simp]: "ubConcEq b1\<cdot>b2 = (ubConc b1\<cdot>b2) \<bar> ubDom\<cdot>b2"
  by(simp add: ubConcEq_def)

lemma ubconceq_dom [simp]: "ubDom\<cdot>(ubConcEq b1\<cdot>b2) = ubDom\<cdot>b2"
  by auto



end    