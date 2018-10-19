(*  Title:        MediumSPS.thy
    Author:       Annika Savelsberg
    E-Mail:       annika.savelsberg@rwth-aachen.de

    Description:  Theory for MediumSPS Definitions and Lemmata.
*)

chapter {* Theory for MediumSPS Definitions and Lemmata *}

theory MediumSPS
imports spec.SPS MediumSPF

begin

default_sort countable

(* ----------------------------------------------------------------------- *)
  section {* MediumSPS Definition for Verification *}
(* ----------------------------------------------------------------------- *)

text {* @{term MedSPS}: Lossy medium function set for the Alternating Bit Protocol. *}
lift_definition MedSPS :: "nat \<Rightarrow> ('a mediumMessage tsyn,'a mediumMessage tsyn) SPS" is 
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

lemma spf2sps: assumes "spfConcIn In\<cdot>spf1 = spfConcOut Out\<cdot>spf2"
  and "spf1 \<in> uspecSet sps1"
  shows "\<exists>sps2. spf2 \<in> uspecSet sps2 \<and> spsConcIn In sps1
    = spsConcOut Out (uspecFlatten (uspecDom\<cdot>sps2)(uspecRan\<cdot>sps2)(Rev {sps2}))"
  apply (subst spsconcin_insert)
  apply (subst spsconcout_insert)
  apply (simp add: uspecImage_def)
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  apply (simp add: uspecrevset_insert setrevImage_def)
  apply (simp add: rep_rev_revset)
oops

(*
lemma spf2sps_b: assumes "spfConcIn (sbe2SB sbe1)\<cdot>spf1 = spfConcOut (sbe2SB sbe2)\<cdot>spf2"
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
  apply (rule image_cong)
  defer 
  defer
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def assms)+
oops*)

(* step Lemmata *) 
text{* If null comes in, it will be sent and Medium stays in its state. *}
lemma medsps_spsconc_null: "spsConcIn (mediumIn_i -)(MedSPS n) = spsConcOut (mediumOut_o -)(MedSPS n)"
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
lemma medsps_spsconc_msg_nzero: 
  "spsConcIn (mediumIn_i (Msg m)) (MedSPS (Suc n)) = spsConcOut (mediumOut_o -)(MedSPS n)"
  apply (subst spsconcin_insert)
  apply (subst spsconcout_insert)
  apply (rule uspec_eqI)
  apply (subst uspecimage_useful_uspecrevset)
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  apply (subst uspecimage_useful_uspecrevset)
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  apply (simp add: uspecrevset_insert setrevImage_def MedSPS.rep_eq)
  apply (rule)
  apply (rule image_Collect_subsetI)
  apply (subst setcompr_eq_image)
  apply (metis (mono_tags) image_eqI medspf_spfconc_msg_nzero mem_Collect_eq)
  apply (rule image_Collect_subsetI)
  apply (subst setcompr_eq_image, simp)
  apply (metis imageI medspf_spfconc_msg_nzero2)
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def)+

(*copied*)
lemma uspecflatten_rep_eq: "Rep_rev_uspec (uspecFlatten Dom Ran uspec) 
  = ((setflat\<cdot>(Rep_rev_uspec ` (inv Rev (uspec_set_filter Dom Ran\<cdot>uspec)))))"
  apply(simp add: uspecFlatten_def)
  using rep_abs_rev_simp uspecflatten_well by blast
(**)

text{* If a message comes in and the counter is zero, the message will be sent and Medium changes 
  its state. *}
lemma medsps_spsconc_msg_zero: "spsConcIn (mediumIn_i (Msg m)) (MedSPS 0) 
  = spsConcOut (mediumOut_o (Msg m))(uspecFlatten mediumDom mediumRan (Rev {MedSPS n | n. True}))"
  apply (subst spsconcin_insert)
  apply (subst spsconcout_insert)
  apply (rule uspec_eqI)
  apply (subst uspecimage_useful_uspecrevset)
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  apply (subst uspecimage_useful_uspecrevset)
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  apply (simp add: uspecrevset_insert setrevImage_def MedSPS.rep_eq)
  apply (simp add: uspecflatten_rep_eq)
  apply (simp add: uspec_set_filter_def setrevFilter_def)
oops
  
end