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
lemma medsps_uspecdom: "uspecDom\<cdot>(MedSPS n) = medInDom"
  using medsps_uspecwell  
  apply (simp add: MedSPS_def uspecdom_insert oraFun_def)
sorry

text{* The range of @{term MedSPS}. *}
lemma medsps_uspecran: "uspecRan\<cdot>(MedSPS n) = medOutDom"
  using medsps_uspecwell 
  apply (simp add: MedSPS_def uspecran_insert oraFun_def)
sorry

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
  proof -
    have "{MedSPF ora |ora::bool stream. #({True} \<ominus> ora) = \<infinity> \<and> shd ora} 
      = {(MedSPF ora) | ora. (#({True} \<ominus> ora) = \<infinity> \<and> snth 0 ora \<and> (\<forall>k<0. \<not>snth k ora))}"
      by simp
    then show ?thesis
      using medsps_uspecwell by presburger
  qed

(* If a "null" comes in, send it out and stay in the same state. *)
lemma "spsConcIn (tsynbNull(\<C> ''ds'')) (MedSPS n) = spsConcOut (tsynbNull (\<C> ''dr''))\<cdot>(MedSPS n)"
 (* apply (subst spsconcin_insert)
  apply (case_tac "c=(\<C> ''dr'')", simp_all)
  apply (subst spsconcout_insert, simp)
  apply (simp add: spfConcIn_def spfConcOut_def)
  apply (simp add: uspecImage_def medsps_uspecran medsps_uspecdom ufclDom_ufun_def ufclRan_ufun_def)*)
sorry

lemma "spsConcIn (createBundle (Msg m) (\<C> ''ds'')) (MedSPS (Suc n))
  = spsConcOut (tsynbNull(\<C> ''dr''))\<cdot>(MedSPS n)"
(*  apply (subst spsconcin_insert)
  apply (case_tac "c=(\<C> ''dr'')", simp_all)
  apply (simp add: slen_createbundle_getch)
  apply (subst spsconcout_insert, simp)
  apply (simp add: uspecImage_def medsps_uspecdom medsps_uspecran ufclDom_ufun_def ufclRan_ufun_def)
  apply (simp add: spfConcIn_def spfConcOut_def)
  apply (simp add: uspecrevset_insert MedSPS_def)
  using medsps_uspecwell
  apply (simp add: setrevImage_def inv_rev_rev)
  apply (simp add: MedSPF_def)*)
sorry

(*lemma "\<And>x::(abpMessage tsyn stream\<^sup>\<Omega>) ufun.
       (x \<in> Rep_cfun (spfConcIn (createBundle (\<M> m) (\<C> ''ds''))) ` Rep_rev_uspec (MedSPS (0::nat))) =
       (x \<in> Rep_cfun (spfConcOut (createBundle (\<M> m) (\<C> ''dr''))) ` Rep_rev_uspec (MedSPS n))"
  apply (simp add: image_def spfConcIn_def spfConcOut_def)
  apply (simp add: MedSPS_def)
  apply (subst rep_abs_rev_simp)
  apply (smt CollectD medspf_ufdom medspf_ufran ufclDom_ufun_def ufclRan_ufun_def uspec_wellI)
  apply (subst rep_abs_rev_simp)
  apply (smt CollectD medspf_ufdom medspf_ufran ufclDom_ufun_def ufclRan_ufun_def uspec_wellI)
  proof -
    obtain xa where "xa \<in> {MedSPF ora |ora. #({True} \<ominus> ora) = \<infinity> \<and> shd ora}"    
  oops*)

lemma "spsConcIn (createBundle (Msg m) (\<C> ''ds'')) (MedSPS 0) 
  = spsConcOut (createBundle (Msg m) (\<C> ''dr''))\<cdot>(MedSPS n)"
(*  apply (subst spsconcin_insert)
  apply (simp add: slen_createbundle_getch)
  apply (subst spsconcout_insert)
  apply (simp add: slen_createbundle_getch)
  apply (simp add: uspecImage_def medsps_uspecdom medsps_uspecran ufclDom_ufun_def ufclRan_ufun_def)
  apply (rule uspec_eqI)
  defer
  apply (smt medsps_uspecdom medsps_uspecran spfConcIn_dom spfConcIn_ran spfConcOut_dom 
    spfConcOut_ran ufclDom_ufun_def ufclRan_ufun_def uspecImage_def uspecimage_useful_dom)
  apply (smt medsps_uspecdom medsps_uspecran spfConcIn_dom spfConcIn_ran spfConcOut_dom 
    spfConcOut_ran ufclDom_ufun_def ufclRan_ufun_def uspecImage_def uspecimage_useful_ran)
  apply (simp add: uspecrevset_insert)
  apply (rule setrev_eqI)
  apply (simp add: setrevImage_def inv_rev_rev)
  apply (subst rep_abs_rev_simp)
  defer
  apply (subst rep_abs_rev_simp)
  defer
  apply (simp add: set_eq_iff)*)
sorry

end