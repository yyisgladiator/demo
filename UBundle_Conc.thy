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
"ubConc b1  \<equiv> \<Lambda> b2. (Abs_ubundle (\<lambda>c. Some (usConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))) \<bar> (ubDom\<cdot>b1 \<union> ubDom\<cdot>b2)"  

(* ubConcEq *)
definition ubConcEq:: "'M\<^sup>\<Omega> \<Rightarrow> 'M\<^sup>\<Omega> \<rightarrow> 'M\<^sup>\<Omega>"  where
"ubConcEq b1 \<equiv> \<Lambda> b2. (ubConc b1\<cdot>b2) \<bar> ubDom\<cdot>b2"


(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)


subsection \<open>ubConc\<close>


lemma ubconc_well[simp]: "ubWell (\<lambda>c. Some (usConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))"
  apply(rule ubwellI)
  apply(simp add: ubdom_insert)
  apply(subst usOkay_conc)
  by(simp_all add: ubgetch_insert)

lemma ubconc_mono[simp]: "monofun (\<lambda> b2. (Abs_ubundle (\<lambda>c. Some (usConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))) \<bar> (ubDom\<cdot>b1 \<union> ubDom\<cdot>b2))"
proof - 
  have f1 : "monofun (\<lambda> b2. (Abs_ubundle (\<lambda>c. Some (usConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))))"
    apply(rule monofunI)
    by (smt UNIV_I below_option_def below_ubundle_def fun_belowI monofun_cfun_arg option.distinct(1) option.sel ubdom_channel_usokay ubgetchE ubrep_ubabs ubup_ubdom ubup_ubgetch2 ubwellI usOkay_conc)
  show ?thesis
    by (smt f1 monofun_cfun_arg monofun_def ubdom_below)
qed

lemma ubconc_cont[simp]: "cont (\<lambda> b2. (Abs_ubundle (\<lambda>c. Some (usConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))) \<bar> (ubDom\<cdot>b1 \<union> ubDom\<cdot>b2))"
proof -
  have f0 : "monofun (\<lambda> b2. (Abs_ubundle (\<lambda>c. Some (usConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))))"
    apply(rule monofunI)
    by (smt UNIV_I below_option_def below_ubundle_def fun_belowI monofun_cfun_arg option.distinct(1) option.sel ubdom_channel_usokay ubgetchE ubrep_ubabs ubup_ubdom ubup_ubgetch2 ubwellI usOkay_conc)
  have f1: "cont (\<lambda> b2. (Abs_ubundle (\<lambda>c. Some (usConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))))"
    apply(rule contI2)
    using f0 apply simp
    apply rule+
    
    sorry
  show ?thesis
    apply(rule contI2)
    using ubconc_mono apply blast
    apply rule+
    apply(rule ubrestrict_below)
    using f1 by simp_all
qed

lemma ubconc_dom[simp]: "ubDom\<cdot>(ubConc b1\<cdot>b2) = ubDom\<cdot>b1 \<union> ubDom\<cdot>b2"
proof -
  have f1: "ubDom\<cdot>(Abs_ubundle (\<lambda>c. Some (usConc (ubUp\<cdot>b1 . c)\<cdot>(ubUp\<cdot>b2 . c)))) = UNIV"
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