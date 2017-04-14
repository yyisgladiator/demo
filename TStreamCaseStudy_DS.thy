(* 
    Title:  TStreamCaseStudy_DS.thy
    Author: Dennis Slotboom
    e-mail: dennis.slotboom@rwth-aachen.de

    Description: Definitons and lemmas for tsum6, ttimes and tsscanl
*)

theory TStreamCaseStudy_DS
imports TStream
begin

(* Examples for weak causal functions *)

lemma tstake1of1tick: "Abs_tstream (\<up>\<surd>) \<down> 1 = Abs_tstream (\<up>\<surd>)"
by (simp add: tsTake_def2 One_nat_def)

lemma tstake1of2tick: "Abs_tstream (<[\<surd>, \<surd>]>) \<down> 1 = Abs_tstream (\<up>\<surd>)"
by (simp add: tsTake_def2 One_nat_def tstakefirst_insert_rep_eq)

lemma tstake2of1tick: "Abs_tstream (\<up>\<surd>) \<down> 2 = Abs_tstream (\<up>\<surd>)"
using tstake1of1tick tstake_fin2 by fastforce

lemma tstake2of2tick: "Abs_tstream (<[\<surd>, \<surd>]>) \<down> 2 = Abs_tstream (<[\<surd>, \<surd>]>)"
by (smt One_nat_def Rep_Abs list2s.simps(2) list2s_0 lscons_conv numeral_2_eq_2 sup'_def tick_msg
    tsconc_insert tstake1of1tick tstake_tick)

lemma tstake2ofinftick: "(tsinftimes (Abs_tstream (\<up>\<surd>))) \<down> 2 = Abs_tstream (<[\<surd>, \<surd>]>)"
by (smt One_nat_def Rep_Abs Rep_cfun_strict1 Suc_1 list2s.simps(2) list2s_0 lscons_conv sup'_def 
    tick_msg tsDropTake1 tsTake.simps(1) tsTakeDrop tsconc_assoc tsconc_insert tsinftimes_unfold
    tstake2of2tick tstake_tick)

lemma tstakenofinftick: "#(Rep_tstream tsinftimes (Abs_tstream (\<up>\<surd>)) \<down> n) < \<infinity>"
by (metis Abs_Rep Inf'_neq_0 Rep_tstream_strict inf_ub less_le sconc_fst_inf sconc_snd_empty
    slen_empty_eq tsDropNth tsDropTake1 ts_well_Rep ts_well_def tsconc_insert tsinf_nth
    tstake_tsnth tstickcount_insert)

(* Constructed non continous function on tstreams is monotone and weak causal *)
definition tsmonoweak :: "'a tstream \<Rightarrow> 'a tstream" where
"tsmonoweak ts \<equiv> if #(Rep_tstream ts)<\<infinity> then ts else ts \<bullet> Abs_tstream (\<up>\<surd>)"

lemma mono_tsmonoweak: "monofun tsmonoweak"
apply (rule monofunI)
apply (simp add: tsmonoweak_def, auto)
by (metis inf_less_eq leI tsInfTicks tsconc_id)+

lemma tsweak_tsmonoweak: "tsWeakCausal tsmonoweak"
by (simp add: tsMono2Weak2 mono_tsmonoweak not_less tsInfTicks tsmonoweak_def)

lemma tsmonoweak_inftick:
  "tsmonoweak (tsinftimes (Abs_tstream (\<up>\<surd>))) = tsinftimes (Abs_tstream (\<up>\<surd>)) \<bullet> Abs_tstream (\<up>\<surd>) "
apply (simp add: tsmonoweak_def)
by (metis ln_less neq_iff slen_scons tick_msg tsconc_rep_eq tsinftimes_unfold)

lemma tsmonoweak_inftick_is_ub:
  "range (\<lambda>i. tsmonoweak tsinftimes (Abs_tstream (\<up>\<surd>)) \<down> i ) <| tsinftimes (Abs_tstream (\<up>\<surd>))"
by (simp add: is_ub_def tsmonoweak_def tstakenofinftick)

lemma non_cont_tsmonoweak: "\<not>cont tsmonoweak"
apply (simp add: cont_def)
apply (rule_tac x="(\<lambda>i. (tsinftimes (Abs_tstream (\<up>\<surd>))) \<down> i )" in exI)
apply (simp add: tsmonoweak_inftick is_lub_def, auto)
apply (rule_tac x="tsinftimes (Abs_tstream (\<up>\<surd>))" in exI)
apply (simp add: tsmonoweak_inftick_is_ub)
sorry

end