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



(* Constructed non monotone function on tstreams is not continous but weak causal *)
definition tsnonmono :: "'a tstream \<Rightarrow> 'a tstream" where
"tsnonmono ts \<equiv> if ts=\<bottom> then Abs_tstream (\<up>\<surd>) else \<bottom>"

(* \<bottom> \<sqsubseteq> x but <\<surd>> \<sqsubseteq> \<bottom> is false *)
lemma non_mono_tsnonmono: "\<not>monofun tsnonmono"
by (simp add: monofun_def tsnonmono_def)

lemma non_cont_tsnonmono: "\<not>cont tsnonmono"
using cont2mono non_mono_tsnonmono by auto

lemma tsweak_tsnonmono: "tsWeakCausal tsnonmono"
apply (rule tsWeakCausalI)
apply (simp add: tsnonmono_def, auto)
using tstakeBot by blast+

(* Constructed non monotone function on tstreams is not strong causal
   \<bottom> \<down> 0 = <\<surd>> \<down> 0 but \<bottom> \<down> 1 \<noteq> <\<surd>> \<down> 1 *)
lemma non_tsstrong_tsnonmono: "\<not>tsStrongCausal tsnonmono"
apply(auto simp add: tsnonmono_def tsStrongCausal_def)
apply (rule_tac x=0 in exI)
apply (rule_tac x="Abs_tstream (\<up>\<surd>)" in exI)
by (metis One_nat_def Rep_Abs Rep_cfun_strict1 Rep_tstream_bottom_iff stream.con_rews(2) sup'_def
    tick_msg tsTake.simps(1) tstake1of1tick up_defined)



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
by (simp add: is_ub_def tsmonoweak_def slen_tstakenofinftick)

lemma non_cont_tsmonoweak: "\<not>cont tsmonoweak"
apply (simp add: cont_def)
apply (rule_tac x="(\<lambda>i. (tsinftimes (Abs_tstream (\<up>\<surd>))) \<down> i )" in exI)
apply (simp add: tsmonoweak_inftick is_lub_def, auto)
apply (rule_tac x="tsinftimes (Abs_tstream (\<up>\<surd>))" in exI)
apply (simp add: tsmonoweak_inftick_is_ub)
sorry

end