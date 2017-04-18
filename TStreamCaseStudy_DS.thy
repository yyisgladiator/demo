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

lemma tstake2of1tick: "Abs_tstream (\<up>\<surd>) \<down> 2 = Abs_tstream (\<up>\<surd>)"
using tstake1of1tick tstake_fin2 by fastforce

lemma tstake1of2tick: "Abs_tstream (<[\<surd>, \<surd>]>) \<down> 1 = Abs_tstream (\<up>\<surd>)"
by (simp add: tsTake_def2 One_nat_def tstakefirst_insert_rep_eq)

lemma tstake2of2tick: "Abs_tstream (<[\<surd>, \<surd>]>) \<down> 2 = Abs_tstream (<[\<surd>, \<surd>]>)"
by (smt One_nat_def Rep_Abs list2s.simps(2) list2s_0 lscons_conv numeral_2_eq_2 sup'_def tick_msg
    tsconc_insert tstake1of1tick tstake_tick)

lemma tstake1ofinftick: "(tsinftimes (Abs_tstream (\<up>\<surd>))) \<down> 1 = Abs_tstream (\<up>\<surd>)"
by (metis One_nat_def Rep_cfun_strict1 tsDropTake1 tsTake.simps(1) tsTakeDrop tsinftimes_unfold
    tstake2of1tick tstake_tick)

lemma tstake2ofinftick: "(tsinftimes (Abs_tstream (\<up>\<surd>))) \<down> 2 = Abs_tstream (<[\<surd>, \<surd>]>)"
by (metis Rep_Abs Suc_1 list2s.simps(2) list2s_0 lscons_conv sconc_snd_empty tick_msg tsconc_insert
    tsinftimes_unfold tstake1ofinftick tstake_tick)

lemma slen_tstakenofinftick: "#(Rep_tstream tsinftimes (Abs_tstream (\<up>\<surd>)) \<down> n) < \<infinity>"
by (metis Abs_Rep Inf'_neq_0 Rep_tstream_strict inf_ub less_le sconc_fst_inf sconc_snd_empty
    slen_empty_eq tsDropNth tsDropTake1 ts_well_Rep ts_well_def tsconc_insert tsinf_nth
    tstake_tsnth tstickcount_insert)

lemma slen_inftick: "#(Rep_tstream (tsinftimes (Abs_tstream (\<up>\<surd>)))) = \<infinity>"
by (metis (no_types, lifting) less_irrefl ln_less sConc_Rep_fin_fin slen_scons tick_msg tsInfTicks
    tsconc_rep_eq tsinftimes_unfold tstickcount_insert)

lemma not_below_2tick_tick: "Abs_tstream (\<up>\<surd> \<bullet> \<up>\<surd>) \<notsqsubseteq> Abs_tstream (\<up>\<surd>)"
by (smt Rep_Abs Rep_tstream_inject list2s.simps(1) list2s.simps(2) list2s_inj lscons_conv 
    not_Cons_self po_eq_conv sup'_def tick_msg ts_tsconc_prefix ts_well_conc1 tsconc_rep_eq1)

(* Constructed function on tstreams is monotone and weak causal but not continous? *)
definition f1 :: "'a tstream \<Rightarrow> 'a tstream" where
"f1 ts \<equiv> if #(Rep_tstream ts)<\<infinity> then ts else ts \<bullet> Abs_tstream (\<up>\<surd>)"

definition finite_tick_chain :: "nat \<Rightarrow> 'a tstream" where
"finite_tick_chain = (\<lambda>i. (tsntimes 100 (Abs_tstream(\<up>\<surd>))) \<down> i)"

lemma "f1 (finite_tick_chain i) = finite_tick_chain i"
by (simp add: f1_def not_less tsconc_insert)

lemma mono_f1: "monofun f1"
apply (rule monofunI)
apply (simp add: f1_def, auto)
by (metis inf_less_eq leI tsInfTicks tsconc_id)+

lemma weak_f1: "tsWeakCausal f1"
apply (rule tsMono2Weak2)
apply (simp add: mono_f1)
apply (simp add: f1_def)
using lnle_def monofun_cfun_arg ts_tsconc_prefix by blast

lemma cont_f1_1: "cont f1"
by (metis Fin_02bot f1_def leI lnzero_def notinfI3 strict_slen tsWeak2cont ts_well_Rep ts_well_def
    tsconc_id tstickcount_insert weak_f1)

lemma f1_inftick:
  "f1 (tsinftimes (Abs_tstream (\<up>\<surd>))) = tsinftimes (Abs_tstream (\<up>\<surd>)) \<bullet> Abs_tstream (\<up>\<surd>)"
by (simp add: f1_def slen_inftick)

lemma f1_inftick_is_ub:
  "range (\<lambda>i. f1 tsinftimes (Abs_tstream (\<up>\<surd>)) \<down> i ) <| tsinftimes (Abs_tstream (\<up>\<surd>))"
by (simp add: is_ub_def f1_def slen_tstakenofinftick)

lemma cont_f1: "\<not>cont f1"
apply (simp add: cont_def)
apply (rule_tac x="(\<lambda>i. (tsinftimes (Abs_tstream (\<up>\<surd>))) \<down> i )" in exI)
apply (simp add: f1_inftick is_lub_def, auto)
apply (rule_tac x="tsinftimes (Abs_tstream (\<up>\<surd>))" in exI)
apply (simp add: f1_inftick_is_ub)
sorry

definition smedium :: "bool stream \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
"smedium \<equiv> fix\<cdot>(\<Lambda> h. (\<lambda>bs ms. if (bs=\<epsilon> \<or> ms=\<epsilon>) then \<epsilon> else 
                              (if shd bs=False then (h (srt\<cdot>bs) (srt\<cdot>ms)) else 
                                  (\<up>(shd ms) \<bullet> (h (srt\<cdot>bs) (srt\<cdot>ms))))))"

lemma cont_smedium: "\<And>bs ms. cont (\<lambda>h. if bs = \<epsilon> \<or> ms = \<epsilon> then \<epsilon> else 
                                     if shd bs = False then h (srt\<cdot>bs) (srt\<cdot>ms) else
                                        \<up>(shd ms) \<bullet> h (srt\<cdot>bs) (srt\<cdot>ms))"
apply (rule contI)
apply (rule_tac y=bs in scases', auto)
apply (rule is_lub_const)+
apply (subst lub_fun, assumption)
apply (rule_tac y=ms in scases', auto)
apply (metis ch2ch_fun lub_fun thelubE)
apply (rule is_lub_const)
by (smt ch2ch_fun lub_fun thelubE contlub_cfun_arg lub_eq monofun_cfun_arg chain_def)

lemma "#(smedium bs ms) = #({True} \<ominus> bs)"
apply (subst smedium_def [THEN fix_eq2])
apply (simp add: cont_smedium, auto)
sorry

lemma "smedium bs ms \<sqsubseteq> ms"
apply (subst smedium_def [THEN fix_eq2])
apply (simp add: cont_smedium, auto)
sorry

end