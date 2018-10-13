(*  Title:        MediumSPF.thy
    Author:       Annika Savelsberg
    E-Mail:       annika.savelsberg@rwth-aachen.de

    Description:  Theory for MediumSPF Definitions and Lemmata.
*)

chapter {* Theory for MediumSPF Definitions and Lemmata *}

theory MediumSPF
imports fun.SPF PreludeMed Medium

begin

default_sort countable

(* ----------------------------------------------------------------------- *)
  section {* MediumSPF Definition for Verification *}
(* ----------------------------------------------------------------------- *)


text {* @{term tsynbMed}: Lossy medium function on time-synchonous stream bundles. *}
definition tsynbMed :: "bool stream \<Rightarrow> 'a mediumMessage tsyn stream ubundle 
  \<rightarrow> 'a mediumMessage tsyn stream ubundle" where
  "tsynbMed ora \<equiv> \<Lambda> sb. (mediumOut_stream_o\<cdot>(tsynMed\<cdot>(medium_get_stream_i\<cdot>sb)\<cdot>ora))"


text {* @{term MedSPF}: Lossy medium function for the Alternating Bit Protocol. *}
definition MedSPF :: "bool stream \<Rightarrow> ('a mediumMessage tsyn,'a mediumMessage tsyn) SPF" where
"MedSPF ora = ufLift mediumDom (tsynbMed ora)"


text{* @{term oraFun}: Function to create ora streams with True at position n.*}
definition oraFun :: "nat \<Rightarrow> bool stream set" where
  "oraFun n = {ora. (#({True} \<ominus> ora) = \<infinity> \<and> snth n ora \<and> (\<forall>k<n. \<not>snth k ora))}"

(* ----------------------------------------------------------------------- *)
subsection {* basic properties of MedSPF *}
(* ----------------------------------------------------------------------- *)

text{* The domain of @{term MedSPF}. *}
lemma medspf_ufdom[simp]: "ufDom\<cdot>(MedSPF ora) = mediumDom"
  by (simp add: MedSPF_def)

text{* The range of @{term MedSPF}. *}
lemma medspf_ufran[simp]: "ufRan\<cdot>(MedSPF ora) = mediumRan"
  apply (simp add: MedSPF_def tsynbMed_def)
  by (simp add: ubclDom_ubundle_def)

text{* The domain of the output bundle of @{term MedSPF}. *}
lemma medspf_ubdom [simp]:
  assumes "ubDom\<cdot>sb = ufDom\<cdot>(MedSPF ora)"
  shows "ubDom\<cdot>((MedSPF ora) \<rightleftharpoons> sb) = mediumRan"
  by (metis assms medspf_ufdom medspf_ufran ubclDom_ubundle_def ufran_2_ubcldom2)

text{* @{term MedSPF} is strict. *}
lemma medspf_strict: "(MedSPF ora) \<rightleftharpoons> ubLeast(mediumDom) = ubLeast(mediumRan)"
  apply (simp add: MedSPF_def ubclDom_ubundle_def)
  apply (rule medium_get_stream_Out_eq, simp_all)
  by (simp add: tsynbMed_def)+

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
  shows "spfConcIn (mediumIn_i -)\<cdot>(MedSPF ora) = spfConcOut (mediumOut_o -)\<cdot>(MedSPF ora)"
  apply (rule spf_eq, simp_all)
  apply (rule medium_get_stream_Out_eq, simp_all)
  apply (simp add: MedSPF_def tsynbMed_def ubclDom_ubundle_def)
  using assms orafun_nbot tsynmed_sconc_null by blast


text{* If a message comes in and the counter is not zero, null will be sent and Medium stays in its 
  state. *}
lemma medspf_spfconc_msg_nzero: assumes "ora1 \<in> oraFun (Suc n)" obtains ora2 where "ora2 \<in> oraFun n"
  and "spfConcIn (mediumIn_i (Msg m))\<cdot>(MedSPF ora1) = spfConcOut (mediumOut_o -)\<cdot>(MedSPF ora2)"
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
    have "spfConcIn (mediumIn_i (Msg m))\<cdot>(MedSPF ora1) = spfConcOut (mediumOut_o -)\<cdot>(MedSPF ora2)"
      apply (rule spf_eq, simp_all)
      apply (rule medium_get_stream_Out_eq, simp_all)
      apply (simp add: MedSPF_def tsynbMed_def ubclDom_ubundle_def)
      by (simp add: ora2def tsynmed_sconc_msg_f)
    thus ?thesis
      using ora2_orafun that by blast 
  qed           

text{* If a message comes in and the counter is zero, the message will be sent and Medium changes its 
  state. *}
lemma medspf_spfconc_msg_zero: assumes "ora1 \<in> oraFun 0" obtains ora2 where "\<exists>n. ora2 \<in> oraFun n"
  and "spfConcIn (mediumIn_i (Msg m))\<cdot>(MedSPF ora1) = spfConcOut (mediumOut_o (Msg m))\<cdot>(MedSPF ora2)"
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
    have "spfConcIn (mediumIn_i (Msg m))\<cdot>(MedSPF ora1) = spfConcOut (mediumOut_o (Msg m))\<cdot>(MedSPF ora)"
      apply (rule spf_eq, simp_all)
      apply (rule medium_get_stream_Out_eq, simp_all)
      apply (simp add: MedSPF_def tsynbMed_def ubclDom_ubundle_def)
      using ora1_def tsynmed_sconc_msg_t by blast
    then show ?thesis
      using ora1_def that by blast
  qed

end