(*  Title:        MediumSPS.thy
    Author:       Annika Savelsberg
    E-Mail:       annika.savelsberg@rwth-aachen.de

    Description:  Theory for MediumSPS Definitions and Lemmata.
*)

chapter {* Theory for MediumSPS Definitions and Lemmata *}

theory MediumSPS
imports MediumSPF

begin

default_sort countable

(* ----------------------------------------------------------------------- *)
  section {* MediumSPS Definition for Verification *}
(* ----------------------------------------------------------------------- *)

text {* @{term MedSPS}: Lossy medium function set for the Alternating Bit Protocol. *}
lift_definition MedSPS :: "nat \<Rightarrow> 'a medMessage tsyn SPS" is 
  "\<lambda> n. (Rev {(MedSPF ora) | ora. ora \<in> (oraFun n)}, Discr medInDom, Discr medOutDom)"
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  using medspf_ufdom medspf_ufran by blast

(* ----------------------------------------------------------------------- *)
subsection {* Basic Properties of MedSPS *}
(* ----------------------------------------------------------------------- *)

text{* The domain of @{term MedSPS}. *}
lemma medsps_uspecdom[simp]: "uspecDom\<cdot>(MedSPS n) = medInDom"
  apply (simp add: MedSPS_def uspecdom_insert oraFun_def)
  apply (subst rep_abs_uspec, simp_all)
  by (metis medspf_ufdom medspf_ufran ufclDom_ufun_def ufclRan_ufun_def)

text{* The range of @{term MedSPS}. *}
lemma medsps_uspecran[simp]: "uspecRan\<cdot>(MedSPS n) = medOutDom"
  apply (simp add: MedSPS_def uspecran_insert oraFun_def)
  apply (subst rep_abs_uspec, simp_all)
  by (metis medspf_ufdom medspf_ufran ufclDom_ufun_def ufclRan_ufun_def)

(* ----------------------------------------------------------------------- *)
subsection {* Medium State Lemmata *}
(* ----------------------------------------------------------------------- *)

lemma spf2sps: assumes "spfConcIn (sbe2SB sbe1)\<cdot>spf1 = spfConcOut (sbe2SB sbe2)\<cdot>spf2"
(*  and "sbeDom sbe1 = uspecDom\<cdot>sps"
  and "sbeDom sbe2 = uspecRan\<cdot>sps2" *)
  and "uspecDom\<cdot>sps1 = uspecDom\<cdot>sps2"
  and "uspecRan\<cdot>sps1 = uspecRan\<cdot>sps2"
  shows "spsConcIn (sbe2SB sbe1) sps1 
    = spsConcOut (sbe2SB sbe2) (uspecFlatten (uspecDom\<cdot>sps2)(uspecRan\<cdot>sps2)(Rev {sps2}))"
  apply (subst spsconcin_insert)
  apply (subst spsconcout_insert)
  apply (rule uspec_eqI)
  apply (subst uspecimage_useful_uspecrevset)
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  apply (subst uspecimage_useful_uspecrevset)
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  apply (simp add: uspecrevset_insert setrevImage_def)
  apply (rule image_cong, simp_all)
  defer 
  defer
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def assms)+
oops

(* step Lemmata *) 
text{* If null comes in, it will be sent and Medium stays in its state. *}
lemma  medsps_spsconc_null: "spsConcIn (medIn -)(MedSPS n) = spsConcOut (medOut -)(MedSPS n)"
  apply (subst spsconcin_insert)
  apply (subst spsconcout_insert)
  apply (rule uspec_eqI)
  apply (subst uspecimage_useful_uspecrevset)
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  apply (subst uspecimage_useful_uspecrevset)
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  apply (simp add: uspecrevset_insert setrevImage_def MedSPS.rep_eq)
  apply (rule image_cong, simp_all)
  using medspf_spfconc_null apply blast
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def)+

text{* If a message comes in and the counter is not zero, null will be sent and Medium stays in its 
  state. *}
lemma medsps_spsconc_msg_nzero: "spsConcIn (medIn (Msg m)) (MedSPS (Suc n)) = spsConcOut (medOut -)(MedSPS n)"
  apply (simp add: medIn_def medOut_def)
 (* apply (subst spf2sps, simp_all)*)
  oops

text{* If a message comes in and the counter is zero, the message will be sent and Medium changes 
  its state. *}
lemma medsps_spsconc_msg_zero:"spsConcIn (medIn (Msg m)) (MedSPS 0) 
  = spsConcOut (medOut (Msg m))(uspecFlatten medInDom medOutDom (Rev {MedSPS n | n. True}))"
  apply (simp add: medIn_def medOut_def)
 (* apply (subst spf2sps, simp_all)*)
  oops
(**)

lemma sps2spf_ndaconcoutflatten:
  assumes "\<And>state. uspecDom\<cdot>(other state) = In"
  and "\<And>state. uspecRan\<cdot>(other state) = Out"
  and "\<And>state. other state \<noteq> uspecMax In Out" 
  shows "spsConcIn (sbe2SB sbe) (other state) = ndaConcOutFlatten In Out (currentTransitions) other"
  apply (rule uspec_eqI)
  apply (simp add: spsconcin_insert)
  apply (subst uspecimage_useful_uspecrevset)
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  apply (simp add: uspecrevset_insert)
  apply (simp add: ndaConcOutFlatten_def)
  defer
  apply (subst spsconcin_dom)
  apply (simp add: ndaConcOutFlatten_def assms)
  apply (subst spsconcin_ran)
  apply (simp add: ndaConcOutFlatten_def assms)
sorry

lemma ndatrans_nempty[simp]: "(ndaTransition\<cdot>medFairAut) (n, sbe) \<noteq> Rev {}"
  apply (simp add: ndaTransition_def medFairAut.rep_eq)
sorry

lemma medsps_notuspecmax[simp]: "MedSPS n \<noteq> uspecMax medInDom medOutDom"
  by (metis (mono_tags, lifting) MedSPS.rep_eq all_not_in_conv empty_Collect_eq orafun_nempty 
    prod.inject rev.inject uspecMax.rep_eq)

thm nda_h_bottom_h
lemma medsps_strict[simp]: "uspecIsStrict (MedSPS n)"
  apply (simp add: uspecIsStrict_def)
  apply (rule uspec_ballI)
  apply (rule ufisstrictI)
  apply (simp add: ubclDom_ubundle_def)
sorry

thm nda_h_final_back
lemma medsps_medfair_subeq:
  shows "nda_h medFairAut \<sqsubseteq> MedSPS"
  apply (subst nda_h_final_back, simp_all)
  apply (subst sps2spf_ndaconcoutflatten, simp_all)
sorry
  
end