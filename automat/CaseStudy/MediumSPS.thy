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
lemma medsps_uspecdom: "uspecDom\<cdot>(MedSPS n) = medInDom"
  apply (simp add: MedSPS_def uspecdom_insert oraFun_def)
  apply (subst rep_abs_uspec, simp_all)
  by (metis medspf_ufdom medspf_ufran ufclDom_ufun_def ufclRan_ufun_def)

text{* The range of @{term MedSPS}. *}
lemma medsps_uspecran: "uspecRan\<cdot>(MedSPS n) = medOutDom"
  apply (simp add: MedSPS_def uspecran_insert oraFun_def)
  apply (subst rep_abs_uspec, simp_all)
  by (metis medspf_ufdom medspf_ufran ufclDom_ufun_def ufclRan_ufun_def)

(* ----------------------------------------------------------------------- *)
subsection {* Medium State Lemmata *}
(* ----------------------------------------------------------------------- *)

text{* If null comes in, it will be sent and Medium stays in its state. *}
lemma "spsConcIn (medIn -)(MedSPS n) = spsConcOut (medOut -)(MedSPS n)"
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
lemma "spsConcIn (medIn (Msg m)) (MedSPS (Suc n)) = spsConcOut (medOut -)(MedSPS n)"
sorry

text{* If a message comes in and the counter is zero, the message will be sent and Medium changes its 
  state. *}
lemma "spsConcIn (medIn (Msg m)) (MedSPS 0) 
  = spsConcOut (medOut (Msg m))(uspecFlatten medInDom medOutDom (Rev {MedSPS n | n. True}))"
sorry

end