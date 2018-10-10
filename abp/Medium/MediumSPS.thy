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
lift_definition MedSPS :: "nat \<Rightarrow> 'a mediumMessage tsyn SPS" is 
  "\<lambda> n. (Rev {(MedSPF ora) | ora. ora \<in> (oraFun n)}, Discr mediumDom, Discr mediumRan)"
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  using medspf_ufdom medspf_ufran by blast

(* ----------------------------------------------------------------------- *)
subsection {* Basic Properties of MedSPS *}
(* ----------------------------------------------------------------------- *)

text{* The domain of @{term MedSPS}. *}
lemma medsps_uspecdom[simp]: "uspecDom\<cdot>(MedSPS n) = mediumDom"
  apply (simp add: MedSPS_def uspecdom_insert oraFun_def)
  apply (subst rep_abs_uspec, simp_all)
  by (metis medspf_ufdom medspf_ufran ufclDom_ufun_def ufclRan_ufun_def)

text{* The range of @{term MedSPS}. *}
lemma medsps_uspecran[simp]: "uspecRan\<cdot>(MedSPS n) = mediumRan"
  apply (simp add: MedSPS_def uspecran_insert oraFun_def)
  apply (subst rep_abs_uspec, simp_all)
  by (metis medspf_ufdom medspf_ufran ufclDom_ufun_def ufclRan_ufun_def)

(* ----------------------------------------------------------------------- *)
subsection {* Medium State Lemmata *}
(* ----------------------------------------------------------------------- *)

text{* If null comes in, it will be sent and Medium stays in its state. *}
lemma "spsConcIn (mediumIn_ar -)(MedSPS n) = spsConcOut (mediumOut_as -)(MedSPS n)"
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
lemma "spsConcIn (mediumIn_ar (Msg m)) (MedSPS (Suc n)) = spsConcOut (mediumOut_as -)(MedSPS n)"
sorry

(*lemma nda_h_final_back: assumes "\<And>state sbe. sbeDom sbe = ndaDom\<cdot>nda \<Longrightarrow> 
spsConcIn (sbe2SB sbe) (other state) = 
  ndaConcOutFlatten (ndaDom\<cdot>nda) (ndaRan\<cdot>nda) ((ndaTransition\<cdot>nda) (state,sbe)) (other)"
  and "\<And> state sbe. (ndaTransition\<cdot>nda) (state, sbe) \<noteq> Rev {}"
  and "\<And> state. other state \<noteq> uspecMax (ndaDom\<cdot>nda) (ndaRan\<cdot>nda)"
  and "\<And> state. uspecIsStrict (other state)"
  and "\<And> state. uspecDom\<cdot>(other state) = ndaDom\<cdot>nda" 
  and "\<And> state. uspecRan\<cdot>(other state) = ndaRan\<cdot>nda"
shows "nda_h nda \<sqsubseteq> other"*)

lemma spf2sps: assumes "spfConcIn (sbe2SB sbe1)\<cdot>spf1 = spfConcOut (sbe2SB sbe2)\<cdot>spf2"
  and "sbeDom sbe1 = uspecDom\<cdot>sps"
  and "sbeDom sbe2 = uspecRan\<cdot>sps2"
  shows "spsConcIn (sbe2SB sbe1) sps 
    = spsConcOut (sbe2SB sbe2) (uspecFlatten (uspecDom\<cdot>sps2)(uspecRan\<cdot>sps2)(Rev {sps2}))"
sorry

text{* If a message comes in and the counter is zero, the message will be sent and Medium changes 
  its state. *}
lemma "spsConcIn (mediumIn_ar (Msg m)) (MedSPS 0) 
  = spsConcOut (mediumOut_as (Msg m))(uspecFlatten mediumDom mediumRan (Rev {MedSPS n | n. True}))"
  apply (simp add: mediumIn_ar_def mediumOut_as_def)
  apply (subst spf2sps, simp_all)
  defer
sorry

lemma medsps_medfair_eq: 
  shows "MedSPS n = medFair n"
  apply (rule uspec_eqI, simp_all)
  apply (simp add: uspecrevset_insert)
sorry

end