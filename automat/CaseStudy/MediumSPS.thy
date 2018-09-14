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
  "\<lambda> n. (Rev {(MedSPF ora) | ora. ora \<in> (oraFun n)}, Discr medInDom, 
  Discr medOutDom)"
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

text{* The nth element of ora will be true. *}
lemma snth_ora_true: assumes "#({True} \<ominus> ora) = \<infinity>" obtains n where "snth n ora = True"
  by (metis Inf'_neq_0_rev assms ex_snth_in_sfilter_nempty singleton_iff slen_empty_eq)

lemma slen_createbundle_getch: "#(createBundle (\<M> m) c  .  c) < \<infinity>"
  apply (simp add: ubgetch_insert createBundle_def)
  by (metis Fin_02bot Fin_Suc Fin_neq_inf bot_is_0 createBundle.rep_eq fun_upd_same inf_ub 
    lscons_conv option.sel order_less_le slen_scons strict_slen sup'_def ubabs_ubrep)

lemma medsps_0_uspecwell: 
  "uspecWell (Rev{MedSPF ora |ora::bool stream. #({True} \<ominus> ora) = \<infinity> \<and> shd ora}) (Discr medInDom) 
    (Discr medOutDom)"    
  apply (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  using medspf_ufdom medspf_ufran by blast

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