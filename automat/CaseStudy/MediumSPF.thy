(*  Title:        MediumSPF.thy
    Author:       Annika Savelsberg
    E-Mail:       annika.savelsberg@rwth-aachen.de

    Description:  Theory for MediumSPF Definitions and Lemmata.
*)

chapter {* Theory for MediumSPF Definitions and Lemmata *}

theory MediumSPF
imports Medium

begin

(* ----------------------------------------------------------------------- *)
  section {* MediumSPF Definition for Verification *}
(* ----------------------------------------------------------------------- *)

text {* @{term MedSPF}: Lossy medium function for the Alternating Bit Protocol. *}
definition MedSPF :: "bool stream \<Rightarrow> 'a medMessage tsyn SPF" where
  "MedSPF ora \<equiv> Abs_ufun (tsynbMed ora)"

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
lemma medspf_ufdom: "ufDom\<cdot>(MedSPF ora) = medInDom"
  apply (simp add: ufDom_def)
  apply (simp add: ubclDom_ubundle_def MedSPF_def tsynbMed_def)
  apply (subst rep_abs_cufun2)
  apply (metis (no_types) tsynbMed_def tsynbmed_ufwell)
  apply (simp add: domIff)
  by (meson medin_dom someI_ex)

text{* The range of @{term MedSPF}. *}
lemma medspf_ufran: "ufRan\<cdot>(MedSPF ora) = medOutDom"
  apply (simp add: ufran_least)
  apply (simp add: ubclLeast_ubundle_def medspf_ufdom ubclDom_ubundle_def)
  by (simp add: MedSPF_def tsynbmed_insert tsynbmed_ubundle_ubdom)

text{* The domain of the output bundle of @{term MedSPF}. *}
lemma medspf_ubdom:
  assumes "ubDom\<cdot>sb = ufDom\<cdot>(MedSPF ora)"
  shows "ubDom\<cdot>((MedSPF ora) \<rightleftharpoons> sb) = medOutDom"
  by (metis assms medspf_ufdom medspf_ufran ubclDom_ubundle_def ufran_2_ubcldom2)

text{* @{term MedSPF} is strict. *}
lemma medspf_strict: "(MedSPF ora) \<rightleftharpoons> ubLeast(medInDom) = ubLeast(medOutDom)"
  proof -
    have eq_empty: "natbool2abp\<cdot>(tsynMed\<cdot>(abp2natbool\<cdot>(ubLeast {\<C> ''ds''} . 
        \<C> ''ds''))\<cdot>ora) =  \<bottom>" 
      by (simp add: abp2natbool_def natbool2abp_def)
    have partial_eq:" [\<C> ''dr'' \<mapsto> \<bottom>] =  (\<lambda>a. (a \<in> {\<C> ''dr''}) \<leadsto> \<bottom>)" 
      by (simp add: fun_upd_def)
    hence "Abs_ubundle [\<C> ''dr'' \<mapsto> \<bottom>] = ubLeast {\<C> ''dr''}" 
      by (simp add: partial_eq ubLeast_def)
    hence "Rep_cfun (tsynbMed ora) \<rightharpoonup> ubLeast {\<C> ''ds''} = ubLeast {\<C> ''dr''}" 
      using tsynbMed_def eq_empty by simp 
    thus ?thesis by (simp add: medspf_insert)
  qed

(* ----------------------------------------------------------------------- *)
subsection {* properties of oraFun *}
(* ----------------------------------------------------------------------- *)

lemma orafun_snth: "ora \<in> oraFun n \<Longrightarrow> snth n ora"
  by (simp add: oraFun_def)

lemma orafun_nbot: "ora \<in> oraFun n \<Longrightarrow> ora \<noteq> \<epsilon>"
  using oraFun_def by force

lemma orafun_nempty: "oraFun n \<noteq> {}"
  proof -
  obtain ora where ora_def: "ora = ((n \<star> \<up>False) \<bullet> ((\<up>True)\<infinity>))"
    by simp
  have ora_fair: "#({True} \<ominus> ora) = \<infinity>"
    using insert_not_empty ora_def by simp
  have sdrop_empty: "sdrop n\<cdot>(n\<star>\<up>False) = \<bottom>"
    by (simp add: sdropostake sntimes_stake)
  then have sdrop_empty: "sdrop n\<cdot>ora = \<up>True\<infinity>"
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

(* ----------------------------------------------------------------------- *)
subsection {* MedSPF step lemmata *}
(* ----------------------------------------------------------------------- *)

(*
lemma createdsbundle_ubdom: "ubDom\<cdot>(createDsBundle a)= {\<C> ''ds''}"
  by (simp add: ubDom_def createDsBundle.rep_eq)

lemma createdsbundle_ubgetch: "createDsBundle m . \<C> ''ds'' = \<up> (\<M> (Pair_nat_bool m))"
  by (simp add: ubgetch_insert createDsBundle.rep_eq)

lemma createdrbundle_ubdom: "ubDom\<cdot>(createDrBundle a)= {\<C> ''dr''}"
  by (simp add: ubDom_def createDrBundle.rep_eq)

lemma createdrbundle_ubgetch: "createDrBundle m . \<C> ''dr'' = \<up> (\<M> (Pair_nat_bool m))"
  by (simp add: ubgetch_insert createDrBundle.rep_eq)
*)

(*lemma copied can be deleted *)
lemma spfConcIn_step[simp]:
  assumes  "ubDom\<cdot>sb = ufDom\<cdot>spf"
  shows "(spfConcIn sb1\<cdot>spf) \<rightleftharpoons> sb = spf \<rightleftharpoons> (ubConcEq sb1\<cdot>sb)" 
  by (simp_all add: assms spfConcIn_def ubclDom_ubundle_def Int_absorb1)

lemma medspf_spfconc_null: assumes "ora \<in> oraFun n"  
  shows "spfConcIn (tsynbNull(\<C> ''ds''))\<cdot>(MedSPF ora) = spfConcOut (tsynbNull(\<C> ''dr''))\<cdot>(MedSPF ora)"
  apply (rule spf_eq)
  apply (simp add: medspf_ufdom)+
  apply (subst medspf_ubdom)
  apply (simp add: medspf_ufdom)
  apply (rule ub_eq)
  apply (simp add: medspf_ubdom medspf_ufdom)+
  using assms
  by (simp add: medspf_insert tsynbmed_getch_dr usclConc_stream_def abp2natbool_def natbool2abp_def
    tsynmap_sconc_null orafun_nbot tsynmed_sconc_null)

lemma medspf_spfconc_msg_nzero: assumes "ora1 \<in> oraFun (Suc n)" obtains ora2 where "ora2 \<in> oraFun n"
  and "spfConcIn (createDsBundle m)\<cdot>(MedSPF ora1) = spfConcOut (tsynbNull(\<C> ''dr''))\<cdot>(MedSPF ora2)"
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
    have "spfConcIn (createDsBundle m)\<cdot>(MedSPF ora1) = spfConcOut (tsynbNull(\<C> ''dr''))\<cdot>(MedSPF ora2)"
      apply (rule spf_eq)
      apply (simp add: medspf_ufdom)+
      apply (subst medspf_ubdom)
      apply (simp add: medspf_ufdom)
      apply (rule ub_eq)
      apply (simp add: medspf_ubdom medspf_ufdom)+
      using assms
      by (simp add: medspf_insert tsynbmed_getch_dr usclConc_stream_def abp2natbool_def 
        natbool2abp_def ora2def createdsbundle_ubdom createdsbundle_ubgetch tsynmap_sconc_msg 
        tsynmed_sconc_msg_f tsynmap_sconc_null)
   then show ?thesis
     using ora2_orafun that by simp
  qed           

lemma medspf_spfconc_msg_zero: assumes "ora1 \<in> oraFun 0" obtains ora2 where "ora2 \<in> oraFun n"
  and "spfConcIn (createDsBundle m)\<cdot>(MedSPF ora1) = spfConcOut (createDrBundle m)\<cdot>(MedSPF ora2)"
  using assms
  proof -
    obtain ora2 where ora2_def: "ora2 \<in> oraFun n"
      by (meson orafun_nempty subsetI subset_empty)
    have ora1_shd_t: "shd ora1 = True"
      using assms orafun_snth snth_shd by blast
    obtain ora where ora_def: "ora1 = \<up>True \<bullet> ora"
      by (metis (full_types) assms ora1_shd_t orafun_nbot surj_scons)
    have "spfConcIn (createDsBundle m)\<cdot>(MedSPF ora1) = spfConcOut (createDrBundle m)\<cdot>(MedSPF ora2)"
      apply (rule spf_eq)
      apply (simp add: medspf_ufdom)+
      apply (subst medspf_ubdom)
      apply (simp add: medspf_ufdom)
      apply (rule ub_eq)
      apply (simp add: medspf_ubdom medspf_ufdom)+
      using assms
      apply (simp add: medspf_insert createdsbundle_ubdom createdsbundle_ubgetch tsynbmed_getch_dr
        usclConc_stream_def ora_def tsynmap_sconc_msg abp2natbool_def natbool2abp_def 
        tsynmed_sconc_msg_t pair_invpair_inv)
oops

end