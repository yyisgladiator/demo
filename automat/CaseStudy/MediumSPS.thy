(*  Title:        MediumSPS.thy
    Author:       Annika Savelsberg
    E-Mail:       annika.savelsberg@rwth-aachen.de

    Description:  Theory for MediumSPS Definitions and Lemmata.
*)

chapter {* Theory for MediumSPS Definitions and Lemmata *}

theory MediumSPS
imports MediumSPF spec.SPS

begin

(* ----------------------------------------------------------------------- *)
  section {* MediumSPS Definition for Verification *}
(* ----------------------------------------------------------------------- *)

text {* @{term MedSPS}: Lossy medium function set for the Alternating Bit Protocol. *}
definition MedSPS :: "nat \<Rightarrow> 'a medMessage tsyn SPS" where 
  "MedSPS n = Abs_uspec (Rev {(MedSPF ora) | ora. ora \<in> (oraFun n)}, Discr medInDom, 
  Discr medOutDom)"

(* ----------------------------------------------------------------------- *)
subsection {* Basic Properties of MedSPS *}
(* ----------------------------------------------------------------------- *)

text{* @{term MedSPS} is well-formed. *}
lemma medsps_uspecwell [simp]: 
  "uspecWell (Rev {(MedSPF ora) | ora. (#({True} \<ominus> ora) = \<infinity> \<and> snth n ora
   \<and> (\<forall>k<n. \<not>snth k ora))}) (Discr medInDom) (Discr medOutDom)"
  apply (rule uspec_wellI)
  apply (simp add: ufclDom_ufun_def)
  using medspf_ufdom apply blast
  apply (simp add: ufclRan_ufun_def)
  using medspf_ufran by blast

text{* The domain of @{term MedSPS}. *}
(*smt*)
lemma medsps_uspecdom: "uspecDom\<cdot>(MedSPS n) = medInDom"
  by (smt CollectD MedSPS_def medspf_ufdom medspf_ufran prod.sel(1) prod.sel(2) rep_abs_uspec 
    ufclDom_ufun_def ufclRan_ufun_def undiscr_Discr uspecWell.simps uspecdom_insert)

text{* The range of @{term MedSPS}. *}
(*smt*)
lemma medsps_uspecran: "uspecRan\<cdot>(MedSPS n) = medOutDom"
  by (smt CollectD MedSPS_def medspf_ufdom medspf_ufran prod.sel(2) rep_abs_uspec ufclDom_ufun_def 
    ufclRan_ufun_def undiscr_Discr uspecWell.simps uspecran_insert)

(* ----------------------------------------------------------------------- *)
subsection {* Medium State Lemmata *}
(* ----------------------------------------------------------------------- *)

text{* The nth element of ora will be true. *}
lemma snth_ora_true: assumes "#({True} \<ominus> ora) = \<infinity>" obtains n where "snth n ora = True"
  by (metis Inf'_neq_0_rev assms ex_snth_in_sfilter_nempty singleton_iff slen_empty_eq)

lemma slen_createbundle_getch: "#(createBundle (\<M> m) c  .  c) < \<infinity>"
  apply (simp add: ubgetch_insert createBundle_def)
  by (metis Fin_02bot Fin_Suc Fin_neq_inf bot_is_0 createBundle.rep_eq fun_upd_same inf_ub 
    lscons_conv option.sel order_less_le slen_scons strict_slen sup'_def ubabs_ubrep)

lemma medsps_0_uspecwell: 
(*smt*)
  "uspecWell (Rev{MedSPF ora |ora::bool stream. #({True} \<ominus> ora) = \<infinity> \<and> shd ora}) (Discr medInDom) 
  (Discr medOutDom)"
  proof -
    have "{MedSPF ora |ora::bool stream. #({True} \<ominus> ora) = \<infinity> \<and> shd ora} 
      = {(MedSPF ora) | ora. (#({True} \<ominus> ora) = \<infinity> \<and> snth 0 ora \<and> (\<forall>k<0. \<not>snth k ora))}"
      by simp
    then show ?thesis
      by (smt CollectD medInDom_def medspf_ufdom medspf_ufran ufclDom_ufun_def ufclRan_ufun_def 
        uspecWell.simps)
  qed

(* If a "null" comes in, send it out and stay in the same state. *)
lemma "spsConcIn (tsynbNull(\<C> ''ds'')) (MedSPS n) = spsConcOut (tsynbNull (\<C> ''dr''))\<cdot>(MedSPS n)"
sorry

lemma "spsConcIn (createBundle (Msg m) (\<C> ''ds'')) (MedSPS (Suc n))
  = spsConcOut (tsynbNull(\<C> ''dr''))\<cdot>(MedSPS n)"
sorry

lemma "spsConcIn (createBundle (Msg m) (\<C> ''ds'')) (MedSPS 0) 
  = spsConcOut (createBundle (Msg m) (\<C> ''dr''))\<cdot>(MedSPS n)"
sorry

end