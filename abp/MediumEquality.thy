(*  Title:        MediumEquality.thy
    Author:       Annika Savelsberg
    E-Mail:       annika.savelsberg@rwth-aachen.de

    Description:  Theory for Proof of Equality of MediumSPS and generated Medium.
*)

chapter {* Theory for Proof of Equality of MediumSPS and generated Medium *}

theory MediumEquality
imports spec.SPS abpMedium.MediumSPS abpGenerat.FairMediumAutomaton

begin

default_sort countable

lemma uspecflatten_rep_eq: "Rep_uspec (uspecFlatten Dom Ran uspec) 
  = (Rev ((setflat\<cdot>(Rep_rev_uspec ` (inv Rev (uspec_set_filter Dom Ran\<cdot>uspec))))), Discr Dom, Discr Ran)"
  apply(simp add: uspecFlatten_def)
  using rep_abs_uspec uspecflatten_well by blast

lemma sps2spf_ndaconcoutflatten:
  assumes "\<And>state. uspecDom\<cdot>(other state) = In"
  and "\<And>state. uspecRan\<cdot>(other state) = Out"
  and "\<And>state. other state \<noteq> uspecMax In Out"
  and "\<And>state. ndaTodo_h In Out (s, sb) other = spsConcOut (sbe2SB sbe) (other state)"
  shows "spsConcIn (sbe2SB sbe) (other state) = ndaConcOutFlatten In Out (currentTransitions) other"
  apply (rule uspec_eqI)
  apply (simp add: spsconcin_insert)
  apply (subst uspecimage_useful_uspecrevset)
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  apply (simp add: uspecrevset_insert setrevImage_def)
  defer
  apply (subst spsconcin_dom)
  apply (simp add: ndaConcOutFlatten_def assms)
  apply (subst spsconcin_ran)
  apply (simp add: ndaConcOutFlatten_def assms)
  apply (simp add: ndaConcOutFlatten_def)
  apply (simp add: uspecflatten_rep_eq)
oops

lemma ndatrans_nempty[simp]: "(ndaTransition\<cdot>fairMediumAutomaton) (n, sbe) \<noteq> Rev {}"
  apply (simp add: ndaTransition_def fairMediumAutomaton.rep_eq)
  apply (simp add: fairMediumTransition_def)
  apply rule
oops

lemma medsps_notuspecmax[simp]: "MedSPS n \<noteq> uspecMax mediumDom mediumRan"
  by (metis (mono_tags, lifting) MedSPS.rep_eq all_not_in_conv empty_Collect_eq orafun_nempty 
    prod.inject rev.inject uspecMax.rep_eq)

thm nda_h_bottom_h
lemma medsps_strict[simp]: "uspecIsStrict (MedSPS n)"
  apply (simp add: uspecIsStrict_def)
  apply (rule uspec_ballI)
  apply (rule ufisstrictI)
  apply (simp add: ubclDom_ubundle_def MedSPS.abs_eq)
oops

thm nda_h_final_back
lemma medsps_medfair_subeq:
  shows "nda_h fairMediumAutomaton state \<sqsubseteq> MedSPS n"
(*  apply (subst nda_h_final_back, simp_all)
  apply (subst sps2spf_ndaconcoutflatten, simp_all)*)
oops

end