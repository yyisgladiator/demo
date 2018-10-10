(*  Title:        MediumSPF.thy
    Author:       Annika Savelsberg
    E-Mail:       annika.savelsberg@rwth-aachen.de

    Description:  Theory for MediumSPF Definitions and Lemmata.
*)

chapter {* Theory for MediumSPF Definitions and Lemmata *}

theory MediumSPF
imports Medium

begin

default_sort countable

(* ----------------------------------------------------------------------- *)
  section {* MediumSPF Definition for Verification *}
(* ----------------------------------------------------------------------- *)

text {* @{term MedSPF}: Lossy medium function for the Alternating Bit Protocol. *}
lift_definition MedSPF :: "bool stream \<Rightarrow> ('a medMessage tsyn,'a medMessage tsyn) SPF" is
  "\<lambda> ora. tsynbMed ora"
  by simp

text{* @{term oraFun}: Function to create ora streams with True at position n.*}
definition oraFun :: "nat \<Rightarrow> bool stream set" where
  "oraFun n = {ora. (#({True} \<ominus> ora) = \<infinity> \<and> snth n ora \<and> (\<forall>k<n. \<not>snth k ora))}"

(* ----------------------------------------------------------------------- *)
subsection {* basic properties of MedSPF *}
(* ----------------------------------------------------------------------- *)

text{* @{term MedSPF} insertion lemma. *}
lemma medspf_insert: "(MedSPF ora) \<rightleftharpoons> sb = (Abs_ufun (tsynbMed ora)) \<rightleftharpoons> sb"
  by (simp add: MedSPF_def)

text{* The domain of @{term MedSPF}. *}
lemma medspf_ufdom[simp]: "ufDom\<cdot>(MedSPF ora) = medInDom"
  apply (simp add: ufDom_def)
  apply (simp add: ubclDom_ubundle_def MedSPF_def tsynbMed_def)
  apply (subst rep_abs_cufun2)
  apply (metis (no_types) tsynbMed_def tsynbmed_ufwell)
  apply (simp add: domIff)
  by (meson medin_dom someI_ex)

text{* The range of @{term MedSPF}. *}
lemma medspf_ufran[simp]: "ufRan\<cdot>(MedSPF ora) = medOutDom"
  apply (simp add: ufran_least)
  apply (simp add: ubclLeast_ubundle_def ubclDom_ubundle_def)
  by (simp add: MedSPF_def tsynbmed_insert tsynbmed_ubundle_ubdom)

text{* The domain of the output bundle of @{term MedSPF}. *}
lemma medspf_ubdom:
  assumes "ubDom\<cdot>sb = ufDom\<cdot>(MedSPF ora)"
  shows "ubDom\<cdot>((MedSPF ora) \<rightleftharpoons> sb) = medOutDom"
  by (metis assms medspf_ufdom medspf_ufran ubclDom_ubundle_def ufran_2_ubcldom2)

text{* @{term MedSPF} is strict. *}
lemma medspf_strict: "(MedSPF ora) \<rightleftharpoons> ubLeast(medInDom) = ubLeast(medOutDom)"
  proof -
    have partial_eq:" [\<C> ''out'' \<mapsto> \<bottom>] =  (\<lambda>a. (a \<in> {\<C> ''out''}) \<leadsto> \<bottom>)" 
      by (simp add: fun_upd_def)
    hence "Abs_ubundle [\<C> ''out'' \<mapsto> \<bottom>] = ubLeast {\<C> ''out''}" 
      by (simp add: partial_eq ubLeast_def)
    hence "Rep_cfun (tsynbMed ora) \<rightharpoonup> ubLeast {\<C> ''in''} = ubLeast {\<C> ''out''}" 
      by (simp add: medInDom_def medInGetStream.rep_eq medOutSetStream.rep_eq 
        medOutSetStream_h.abs_eq tsynbmed_insert)
    thus ?thesis 
      by (simp add: MedSPF_def medInDom_def medOutDom_def)
  qed

(* ----------------------------------------------------------------------- *)
subsection {* properties of oraFun *}
(* ----------------------------------------------------------------------- *)

text{* The n-th element of an @{term oraFun} stream is True. *}
lemma orafun_snth: "ora \<in> oraFun n \<Longrightarrow> snth n ora"
  by (simp add: oraFun_def)

text{* No element of @{term oraFun} is empty. *}
lemma orafun_nbot: "ora \<in> oraFun n \<Longrightarrow> ora \<noteq> \<epsilon>"
  using oraFun_def by force

text{* The set @{term oraFun} is not empty. *}
lemma orafun_nempty: "oraFun n \<noteq> {}"
  proof -
  obtain ora where ora_def: "ora = ((n \<star> \<up>False) \<bullet> ((\<up>True)\<infinity>))"
    by simp
  have ora_fair: "#({True} \<ominus> ora) = \<infinity>"
    using insert_not_empty ora_def by simp
  have sdrop_empty: "sdrop n\<cdot>(n\<star>\<up>False) = \<bottom>"
    by (simp add: sdropostake sntimes_stake)
  then have sdrop_inf: "sdrop n\<cdot>ora = \<up>True\<infinity>"
    by (simp add: ora_def sdropl6)
  then have snth_true: "snth n ora"
    by (simp add: snth_def)
  have sdrop_k: "\<And>k. k<n \<Longrightarrow> sdrop k\<cdot>(n\<star>\<up>False) = (n-k)\<star>\<up>False"
    by (metis (no_types, lifting) add_diff_inverse_nat less_Suc_eq not_less_eq sdropl6 sdrops_sinf 
      sntimes_len sntimes_stake stake_add)
  then have snth_false: "\<forall>k<n. \<not> snth k ora"
    by (metis less2nat linorder_not_le ora_def shd_sntime slen_snth_prefix snth_def sntimes_len 
    zero_less_diff)
  have "ora \<in> oraFun n"
    by (simp add: oraFun_def ora_fair snth_false snth_true)
  then show ?thesis
    by blast
  qed

text{* If the first element of an @{term oraFun} stream is True, then the rest is in @{term oraFun}. *}
lemma orafun0_orafunn: 
  assumes "ora \<in> oraFun 0" obtains n where "\<exists>ora1. ora = \<up>True \<bullet> ora1 \<and> ora1 \<in> oraFun n"
  using assms
  proof -
    obtain ora1 where ora1_def: "ora = \<up>True \<bullet> ora1"
      by (metis (full_types) assms orafun_nbot orafun_snth snth_shd surj_scons)
    have ora1_fair: "#({True} \<ominus> ora1) = \<infinity>"
      using assms ora1_def oraFun_def by force
    obtain ora2 where ora2_def: "ora2 = sdropwhile Not\<cdot>ora1"
      by simp
    obtain ora3 where ora3_def: "ora3 = stakewhile Not\<cdot>ora1"
      by simp
    have ora1_conc: "ora1 = ora3 \<bullet> ora2"
      by (simp add: ora2_def ora3_def stakewhileDropwhile)
    obtain n where n_def: "#ora3 = Fin n"
      by (metis Inf'_neq_0 approxl2 empty_iff ex_snth_in_sfilter_nempty insert_iff leD ora1_conc 
          ora1_fair ora3_def sconc_prefix slen_empty_eq stakewhile_slen)
    have snth_ora1_t: "snth n ora1"
      by (metis (full_types) Fin_neq_inf n_def ora1_fair ora3_def sfilterl4 stakewhile_notin)
    have snth_ora1_f: "\<forall>k<n. \<not> snth k ora1"
      using n_def ora3_def by simp    
    then have ora1_orafun: "ora1 \<in> oraFun n"
      by (simp add: snth_ora1_t ora1_fair oraFun_def)
    show ?thesis
      using ora1_def ora1_orafun that by blast
  qed

(* ----------------------------------------------------------------------- *)
subsection {* MedSPF step lemmata *}
(* ----------------------------------------------------------------------- *)

text{* If null comes in, it will be sent and Medium stays in its state. *}
lemma medspf_spfconc_null: assumes "ora \<in> oraFun n"  
  shows "spfConcIn (medIn -)\<cdot>(MedSPF ora) = spfConcOut (medOut -)\<cdot>(MedSPF ora)"
  apply (rule spf_eq, simp_all)
  apply (subst medspf_ubdom, simp)
  apply (rule ub_eq, simp_all)
  apply (simp add: medspf_ubdom)+
  using assms
  by (simp add: medspf_insert usclConc_stream_def medOutDom_def tsynbmed_getch_out 
    medingetstream_ubconc orafun_nbot tsynmed_sconc_null tsynmap_sconc medout_null 
    tsynmap_singleton_null)

text{* If a message comes in and the counter is not zero, null will be sent and Medium stays in its 
  state. *}
lemma medspf_spfconc_msg_nzero: assumes "ora1 \<in> oraFun (Suc n)" obtains ora2 where "ora2 \<in> oraFun n"
  and "spfConcIn (medIn (Msg m))\<cdot>(MedSPF ora1) = spfConcOut (medOut -)\<cdot>(MedSPF ora2)"
  using assms
  proof -
    have ora1_shd_f: "\<not>(snth 0 ora1)"
      by (metis (no_types, lifting) CollectD assms oraFun_def zero_less_Suc)
    obtain ora2 where ora2def: "ora1 = \<up>False \<bullet> ora2"
      by (metis (full_types) ora1_shd_f assms orafun_nbot snth_shd surj_scons)
    have ora2_fair: "#({True} \<ominus> ora2) = \<infinity>"
      using assms ora2def oraFun_def by simp
    have ora2_snth: "snth n ora2"
      using assms ora2def orafun_snth snth_scons by blast
    have ora2_f: "(\<forall>k<n. \<not> snth k ora2)"
      by (metis (no_types, lifting) CollectD Suc_less_eq assms ora2def oraFun_def snth_scons)
    have ora2_orafun: "ora2 \<in> oraFun n"
      by (simp add: ora2_f ora2_fair ora2_snth oraFun_def)
    have "spfConcIn (medIn (Msg m))\<cdot>(MedSPF ora1) = spfConcOut (medOut -)\<cdot>(MedSPF ora2)"
      apply (rule spf_eq, simp_all)
      apply (subst medspf_ubdom, simp)
      apply (rule ub_eq, simp)
      apply (simp add: medspf_ubdom)+
      using assms
      by (simp add: medspf_insert usclConc_stream_def medOutDom_def tsynbmed_getch_out ora2def 
        medingetstream_ubconc tsynmed_sconc_msg_f tsynmap_sconc_null medout_null)
   then show ?thesis
     using ora2_orafun that by simp
  qed           

text{* If a message comes in and the counter is zero, the message will be sent and Medium changes its 
  state. *}
lemma medspf_spfconc_msg_zero: assumes "ora1 \<in> oraFun 0" obtains ora2 where "\<exists>n. ora2 \<in> oraFun n"
  and "spfConcIn (medIn (Msg m))\<cdot>(MedSPF ora1) = spfConcOut (medOut (Msg m))\<cdot>(MedSPF ora2)"
  using assms
  proof -
    have ora1_shd_t: "shd ora1 = True"
      using assms orafun_snth snth_shd by blast
    obtain ora where ora_def: "ora1 = \<up>True \<bullet> ora"
      by (metis (full_types) assms ora1_shd_t orafun_nbot surj_scons)
    obtain n where ora1_def: "ora1 = \<up>True \<bullet> ora \<and> ora \<in> oraFun n"
      by (metis assms inject_scons ora_def orafun0_orafunn)
    have ora_fair: "#({True} \<ominus> ora) = \<infinity>"
      using assms oraFun_def ora_def by auto
    have "spfConcIn (medIn (Msg m))\<cdot>(MedSPF ora1) = spfConcOut (medOut (Msg m))\<cdot>(MedSPF ora)"
      apply (rule spf_eq, simp_all)
      apply (subst medspf_ubdom, simp)
      apply (rule ub_eq, simp_all)
      apply (simp add: medspf_ubdom)+
      using assms
      by (simp add: medspf_insert usclConc_stream_def ora_def medOutDom_def tsynbmed_getch_out 
        medout_msg medingetstream_ubconc tsynmed_sconc_msg_t tsynmap_sconc_msg)
    then show ?thesis
      using ora1_def that by blast
  qed

end