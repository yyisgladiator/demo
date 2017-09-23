(*  Title:        TStreamCase_Study.thy
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Tests with tStreams, mostly a few function definitions
                  and definition of Strong/Weak Causality on TStream functions
*)

chapter {* Timed Streams *} 

theory TStreamCase_Study

imports "../TStream" StreamCase_Study
begin
default_sort countable
declare One_nat_def[simp del]
(* Examples for weak causal functions *)

(* tsTake on tstreams with only ticks *)
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

(* Constructed function on tstreams is not monotone, continous, weak and strong causal *)
definition tsf1 :: "nat tstream \<Rightarrow> nat tstream" where
"tsf1 ts \<equiv> if #(Rep_tstream ts)<\<infinity> then Abs_tstream (<[\<M> 1, \<surd>]>) else Abs_tstream (<[\<M> 2, \<surd>]>)"

(* \<bottom> \<sqsubseteq> <\<surd>, ...> but <1, \<surd>> \<sqsubseteq> <2, \<surd>> is false *)
lemma mono_tsf1: "\<not>monofun tsf1"
apply (simp add: monofun_def)
apply (rule_tac x="\<bottom>" in exI)
apply (rule_tac x="tsinftimes (Abs_tstream (\<up>\<surd>))" in exI)
apply (simp add: tsf1_def slen_inftick)
by (metis fold_inf)

lemma cont_tsf1: "\<not>cont tsf1"
using cont2mono mono_tsf1 by auto

(* <\<surd>> \<down> 1 = <\<surd>, ...> \<down> 1 but <1, \<surd>> \<down> 1 \<noteq> <2, \<surd>> \<down> 1 *)
lemma weak_tsf1: "\<not>tsWeakCausal tsf1"
apply (simp add: tsWeakCausal_def)
apply (rule_tac x=1 in exI)
apply (rule_tac x="tsinftimes (Abs_tstream (\<up>\<surd>))" in exI)
apply (rule_tac x="Abs_tstream (\<up>\<surd>)" in exI)
apply (simp add: tsf1_def slen_inftick)
by (smt One_nat_def Rep_Abs event.distinct(1) event.inject inject_scons numeral_eq_one_iff 
    semiring_norm(85) stwbl2stbl stwbl_f stwbl_t ts_well_sing_conc tstake1of1tick tstake1ofinftick
    tstakefirst_eq2 tstakefirst_insert_rep_eq)

lemma strong_tsf1: "\<not>tsStrongCausal tsf1"
using tsStrong2Weak weak_tsf1 by auto

(* Constructed function on tstreams is monotone but not continous, weak and strong causal *)
definition tsf2_m :: "'a tstream \<Rightarrow> 'a tstream" where
"tsf2_m ts \<equiv> if #(Rep_tstream ts)<\<infinity> then Abs_tstream (\<up>\<surd>) else Abs_tstream (<[\<surd>, \<surd>]>)"

lemma tsf2_m_inftick:
  "tsf2_m (tsinftimes (Abs_tstream (\<up>\<surd>))) = Abs_tstream (<[\<surd>, \<surd>]>)"
apply (simp add: tsf2_m_def)
by (metis ln_less lnless_def slen_scons tick_msg tsconc_rep_eq tsinftimes_unfold)

lemma tsf2_m_tick_is_ub: 
  "range (\<lambda>i. tsf2_m tsinftimes (Abs_tstream (\<up>\<surd>)) \<down> i ) <| Abs_tstream (\<up>\<surd>)"
by (simp add: is_ub_def tsf2_m_def slen_tstakenofinftick)

lemma mono_tsf2_m: "monofun tsf2_m"
apply (simp add: monofun_def tsf2_m_def below_tstream_def)
using leI mono_fst_infD by fastforce

(* Y = Take i <\<surd>, ...> \<Longrightarrow> range (\<lambda>i. tsf2_m (Y i)) <<| <\<surd>> \<noteq> tsf2_m (Lub Y = <\<surd>, ...>) =  <\<surd>, \<surd>> *)
lemma cont_tsf2_m: "\<not>cont tsf2_m"
apply (simp add: cont_def)
apply (rule_tac x="(\<lambda>i. (tsinftimes (Abs_tstream (\<up>\<surd>))) \<down> i )" in exI)
apply (simp add: tsf2_m_inftick is_lub_def, auto)
apply (rule_tac x="Abs_tstream (\<up>\<surd>)" in exI)
by (simp add: not_below_2tick_tick tsf2_m_tick_is_ub)

(* <\<surd>, \<surd>> \<down> 2 = <\<surd>, ...> \<down> 2 but <\<surd>> \<down> 2 \<noteq> <\<surd>, \<surd>> \<down> 2 *)
lemma weak_tsf2_m: "\<not>tsWeakCausal tsf2_m"
apply (simp add: tsWeakCausal_def)
apply (rule_tac x=2 in exI)
apply (rule_tac x="tsinftimes (Abs_tstream (\<up>\<surd>))" in exI)
apply (rule_tac x="Abs_tstream (<[\<surd>, \<surd>]>)" in exI)
by (smt Fin_02bot Fin_Suc Rep_Abs leI less_le list2s.simps(2) list2s_0 ln_less lnzero_def
    lscons_conv notinfI3 slen_scons strict_slen sup'_def tick_msg ts_well_sing_conc tsconc_rep_eq
    tsinftimes_unfold tsf2_m_def tstake2of1tick tstake2of2tick tstake2ofinftick)

lemma strong_tsf2_m: "\<not>tsStrongCausal tsf2_m"
using weak_tsf2_m tsStrong2Weak by auto

(* Constructed function on tstreams is monotone and continous but not weak and strong causal *)
definition tsf3_mc :: "'a tstream \<Rightarrow> 'a tstream" where
"tsf3_mc ts \<equiv> Abs_tstream (srt\<cdot>(Rep_tstream ts))"

lemma mono_tsf3_mc: "monofun tsf3_mc"
by (simp add: monofun_def tsf3_mc_def below_tstream_def monofun_cfun_arg)

(* cont g \<and> \<forall>x. ts_well (g x) \<Longrightarrow> cont (\<lambda>x. Abs_tstream (g x)) *)
lemma cont_tsf3_mc: "cont tsf3_mc"
apply (rule contI2)
apply (simp add: mono_tsf3_mc)
apply (simp add: tsf3_mc_def cont2contlubE)
by (smt Rep_Abs below_tstream_def lub_eq lub_tstream monofun_cfun_arg not_below2not_eq
    po_class.chain_def ts_well_Rep ts_well_drop1)

(* <\<surd>, \<surd>> \<down> 1 = <\<surd>> \<down> 1 but <\<surd>> \<down> 1 \<noteq> \<bottom> \<down> 1 *)
lemma weak_tsf3_mc: "\<not>tsWeakCausal tsf3_mc"
apply (simp add: tsWeakCausal_def tsf3_mc_def)
apply (rule_tac x=1 in exI)
apply (rule_tac x="Abs_tstream (\<up>\<surd>)" in exI)
apply (rule_tac x="Abs_tstream (<[\<surd>, \<surd>]>)" in exI)
by (metis (no_types, lifting) Abs_tstream_strict Rep_Abs Rep_tstream_strict list.distinct(1)
    list2s.simps(2) list2s_0 list2s_inj lscons_conv stream.con_rews(2) stream.sel_rews(5) strictI 
    sup'_def tick_msg tsDropTake1 tsTakeDrop ts_well_sing_conc tstake1of1tick tstake1of2tick)

lemma strong_tsf3_mc: "\<not>tsStrongCausal tsf3_mc"
using weak_tsf3_mc tsStrong2Weak by auto

(* Constructed function on tstreams is monotone, continous and weak causal but not strong causal *)
definition tsf4_mcw :: "'a tstream \<Rightarrow> 'a tstream" where
"tsf4_mcw ts \<equiv> ts"

lemma mono_tsf4_mcw: "monofun tsf4_mcw"
by (simp add: monofun_def tsf4_mcw_def)

lemma cont_tsf4_mcw: "cont tsf4_mcw"
by (metis mono_tsf4_mcw tsMono2weak2cont tsf4_mcw_def)

lemma weak_tsf4_mcw: "tsWeakCausal tsf4_mcw"
by (simp add: tsf4_mcw_def tsWeakCausalI)

(* <\<surd>> \<down> 1 = <\<surd>, \<surd>> \<down> 1 but <\<surd>> \<down> 2 \<noteq> <\<surd>, \<surd>> \<down> 2 *)
lemma strong_tsf4_mcw:"\<not>tsStrongCausal tsf4_mcw"
apply (simp add: tsf4_mcw_def tsStrongCausal_def)
apply (rule_tac x=1 in exI)
apply (rule_tac x="Abs_tstream (\<up>\<surd>)" in exI)
apply (rule_tac x="Abs_tstream (<[\<surd>, \<surd>]>)" in exI)
by (metis (no_types, lifting) Rep_Abs Suc_1 list2s_0 list2s_Suc list2s_inj lscons_conv
    not_Cons_self2 sup'_def tick_msg ts_well_sing_conc tstake1of1tick tstake1of2tick
    tstake2of1tick tstake2of2tick)

(* Constructed function on tstreams is monotone, continous, weak and strong causal *)
definition tsf5_mcws :: "'a tstream \<Rightarrow> 'a tstream" where
"tsf5_mcws ts = Abs_tstream (\<up>\<surd>) \<bullet> ts"

lemma mono_tsf5_mcws: "monofun tsf5_mcws"
by (simp add: monofun_def tsf5_mcws_def below_tstream_def tsconc_rep_eq monofun_cfun_arg)

lemma cont_tsf5_mcws: "cont tsf5_mcws"
apply (rule contI2)
apply (simp add: mono_tsf5_mcws)
by (simp add: tsf5_mcws_def cont2contlubE)

lemma weak_tsf5_mcws: "tsWeakCausal tsf5_mcws"
by (simp add: mono_tsf5_mcws tsMono2Weak2 tsf5_mcws_def)

lemma strong_tsf5_mcws: "tsStrongCausal tsf5_mcws"
by (simp add: tsStrongCausal_def tsf5_mcws_def)

(* Constructed function on tstreams is weak and strong causal but not monotone and continous *)
definition tsf6_ws :: "'a tstream \<Rightarrow> 'a tstream" where
"tsf6_ws ts \<equiv> if ts=\<bottom> then Abs_tstream (<[\<surd>, \<surd>]>) else Abs_tstream (\<up>\<surd>)"

(* \<bottom> \<sqsubseteq> x but <\<surd>, \<surd>> \<sqsubseteq> <\<surd>> is false *)
lemma mono_tsf6_ws: "\<not>monofun tsf6_ws"
by (simp add: monofun_def tsf6_ws_def not_below_2tick_tick)

lemma cont_tsf6_ws: "\<not>cont tsf6_ws"
using cont2mono mono_tsf6_ws by auto

lemma weak_tsf6_ws: "tsWeakCausal tsf6_ws"
apply (rule tsWeakCausalI)
apply (simp add: tsf6_ws_def, auto)
by (metis tstakeBot)+

lemma strong_tsf6_ws: "tsStrongCausal tsf6_ws"
apply (rule tsStrongCausalI)
apply (simp add: tsf6_ws_def, auto)
by (smt One_nat_def Rep_tstream_inverse tick_msg tsconc_rep_eq1 tsinftimes_unfold tstake1ofinftick
    tstakeBot tstake_tick)+

(* Constructed function on tstreams is weak causal but not monotone, continous and strong causal *)
definition tsf7_w :: "'a tstream \<Rightarrow> 'a tstream" where
"tsf7_w ts \<equiv> if ts=\<bottom> then Abs_tstream (\<up>\<surd>) else \<bottom>"

(* \<bottom> \<sqsubseteq> x but <\<surd>> \<sqsubseteq> \<bottom> is false *)
lemma mono_tsf7_w: "\<not>monofun tsf7_w"
by (simp add: monofun_def tsf7_w_def)

lemma cont_tsf7_w: "\<not>cont tsf7_w"
using cont2mono mono_tsf7_w by auto

lemma weak_tsf7_w: "tsWeakCausal tsf7_w"
apply (rule tsWeakCausalI)
apply (simp add: tsf7_w_def, auto)
using tstakeBot by blast+

(* \<bottom> \<down> 0 = <\<surd>> \<down> 0 but \<bottom> \<down> 1 \<noteq> <\<surd>> \<down> 1 *)
lemma strong_tsf7_w: "\<not>tsStrongCausal tsf7_w"
apply(auto simp add: tsf7_w_def tsStrongCausal_def)
apply (rule_tac x=0 in exI)
apply (rule_tac x="Abs_tstream (\<up>\<surd>)" in exI)
by (metis One_nat_def Rep_Abs Rep_cfun_strict1 Rep_tstream_bottom_iff stream.con_rews(2) sup'_def
    tick_msg tsTake.simps(1) tstake1of1tick up_defined)

(* Examples for weak causal function type *)

definition f1_spfw :: "'a \<leadsto>w 'a" where
"f1_spfw \<equiv> \<L> ts. if ts=\<bottom> then Abs_tstream (\<up>\<surd>) else \<bottom>"

lemma tsweak_f1_spfw: "tsWeakCausal (\<lambda>ts. if ts = \<bottom> then Abs_tstream (\<up>\<surd>) else \<bottom>)"
apply (rule tsWeakCausalI)
apply (simp add: f1_spfw_def, auto)
using tstakeBot by blast+

lemma non_mono_f1_spfw: "\<not>monofun (Rep_spfw (f1_spfw))"
apply (simp add: monofun_def f1_spfw_def)
by (simp add: abs_spfw_inverse2 tsweak_f1_spfw)

setup_lifting type_definition_spfw

lift_definition f2_spfw :: "'a \<leadsto>w 'a" is
"\<lambda>ts. if ts=\<bottom> then Abs_tstream (\<up>\<surd>) else \<bottom>"
apply (simp add: spfw_def)
apply (rule tsWeakCausalI)
apply (auto)
using tstakeBot by blast+

lemma non_mono_f2_spfw: "\<not>monofun (Rep_spfw f2_spfw)"
apply (transfer)
by (simp add: monofun_def f2_spfw_def)

(*Definition of tsum5 and verification with sum5*)
(*Helper like h for sum5 but over nat event streams*)
primrec tsh :: "nat \<Rightarrow> nat \<Rightarrow> nat event stream \<Rightarrow> nat event stream" where
"tsh 0 p ts =  \<epsilon>" |
"tsh (Suc n) p ts = (if ts = \<epsilon> then \<epsilon> 
                        else(if shd ts= \<surd> then (\<up>\<surd> \<bullet> (tsh n p (srt\<cdot>ts)))
                                else (\<up>(\<M> (p + (\<M>\<inverse> (shd ts))))) \<bullet> (tsh n (p +(\<M>\<inverse> (shd ts))) (srt\<cdot> ts))))"

(*Helper for tsum5 like sum5_h for sum5 but over nat event streams*)
definition tsum5_h :: " nat \<Rightarrow> nat event stream \<rightarrow> nat event stream" where
"tsum5_h p \<equiv> \<Lambda> ts. (\<Squnion>i. tsh i p ts)"

(*Definition of sum5 over timed streams*)
definition tsum5:: "nat tstream \<rightarrow> nat tstream" where
"tsum5 \<equiv> (\<Lambda> ts. Abs_tstream (tsum5_h 0\<cdot>(Rep_tstream ts)))"



(*\<bottom> contains no natural message *)
lemma tsAbs_bot[simp]: "tsAbs\<cdot>\<bottom> = \<epsilon>"
by(simp add: tsAbs_def)

(*tsh of the empty stream is the empty stream*)
lemma tsh_bot: "tsh n p \<epsilon> = \<epsilon>"
by(induct_tac n,auto)

(*tsAbs of \<surd> and a timed stream is tsAbs of the timed stream*)
lemma AbsStsAbs_tick[simp]: "ts_well as \<Longrightarrow> tsAbs\<cdot> (Abs_tstream (\<up>(\<surd>)\<bullet>as)) = tsAbs\<cdot>(Abs_tstream as)"
by(simp add: tsabs_insert)

(*tsh returns \<surd>s immediately *)
lemma tsh_tick: "tsh (Suc n) p ((\<up>\<surd>)\<bullet>as) = (\<up>\<surd>)\<bullet> tsh n p as"
by(simp add: tsh_def)

(*tsAbs of \<surd> timed stream is the empty stream*)
lemma tsabs_abs_tick[simp]:"tsAbs\<cdot>(Abs_tstream (\<up>\<surd>)) = \<epsilon>"
by(simp add: tsAbs_def)

(*the vent stream with infinitely many \<surd> is well formed*)
lemma tswellinftick: "ts_well ((\<up>\<surd>)\<infinity>)"
by (simp add: ts_well_def)

(*Implies that tsh of (\<up>\<surd>)\<infinity> equals (\<up>\<surd>)\<infinity>*)
lemma tsum5_hsinf: "tsh (Suc n) p (sinftimes(\<up>\<surd>)) = (\<up>\<surd>) \<bullet> tsh n p (sinftimes (\<up>\<surd>))"
by auto

(*tsh i works at most with the first i elements of the input*)
lemma contlub_tsh:
  "\<forall>s p. tsh i p (stake i\<cdot>s) = tsh i p s"
apply (induct_tac i, auto)
apply (rule_tac x=s in scases)
apply auto
apply (metis (no_types, lifting) inject_scons stake_Suc surj_scons)
apply (metis shd1 stake_Suc surj_scons)
apply (metis shd1 stake_Suc surj_scons)
apply (rule_tac x=s in scases)
by auto

(*helper for chain_tsh*)
lemma chain_tsh_helper: "xa\<noteq>\<epsilon> \<and> shd xa \<noteq>\<surd> \<Longrightarrow> tsh (Suc n) x (xa) = \<up>(\<M> (x + (\<M>\<inverse> (shd xa)))) \<bullet> tsh n (x + (\<M>\<inverse> (shd xa))) (srt\<cdot>xa)"
by simp

(*tsh i \<sqsubseteq> tsh (Suc i)*)
lemma chain_tsh: "chain tsh"
apply (rule chainI)
apply (subst fun_below_iff)+
apply (induct_tac i, auto)
apply(simp add: tsh_bot)+
apply (rule monofun_cfun_arg)
apply (erule_tac x="x" in allE)
apply presburger
apply (smt monofun_cfun_arg)
apply(simp add: tsh_bot)+
by (smt monofun_cfun_arg)+

(*helper for mono_tsh*)
lemma mono_tsh_helper: "x \<sqsubseteq> y \<and> x \<noteq> \<epsilon> \<Longrightarrow> shd x = shd y"
using lessD by fastforce

(* monotonicity of tsh *)
lemma mono_tsh: 
  "\<forall> x y q. x \<sqsubseteq> y \<longrightarrow> tsh n q x \<sqsubseteq> tsh n q y"
apply (induct_tac n, auto)
apply (drule lessD, erule disjE, simp)
apply (erule exE)+
apply (erule conjE)+
apply (simp, rule monofun_cfun_arg, simp)
using lessD apply fastforce
using lessD apply fastforce
using mono_tsh_helper
proof -
  fix na :: nat and x :: "nat event stream" and y :: "nat event stream" and q :: nat
  assume a1: "x \<sqsubseteq> y"
  assume a2: "x \<noteq> \<epsilon>"
  assume "\<forall>x y. x \<sqsubseteq> y \<longrightarrow> (\<forall>q. tsh na q x \<sqsubseteq> tsh na q y)"
  then show "\<up>(\<M> (q + (\<M>\<inverse> shd x))) \<bullet> tsh na (q + (\<M>\<inverse> shd x)) (srt\<cdot>x) \<sqsubseteq> \<up>(\<M> (q + (\<M>\<inverse> shd y))) \<bullet> tsh na (q + (\<M>\<inverse> shd y)) (srt\<cdot>y)"
    using a2 a1 by (simp add: mono_tsh_helper monofun_cfun)
qed

(*#(tsh n p s) = min(n, #s)*)
lemma cont_lub_tsum5_h2:
  "\<forall>s p. stake n\<cdot> (tsh n p s) = tsh n p s "
by(induct_tac n,auto)

(* tsum5_h is a continuous function *)
lemma cont_lub_tsum5_h: "cont (\<lambda> s. \<Squnion>i. tsh i p s)" 
apply (rule cont2cont_lub)
apply (rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "p"])
apply (rule chainE)
apply (metis (no_types, lifting) chain_tsh)
apply (rule pr_contI)
apply (rule monofunI)
apply (rule mono_tsh [rule_format], assumption)
apply (rule allI)
apply (rule_tac x="i" in exI)
by (simp add: contlub_tsh)

(*Describes the unfolding of tsum5_h if the first element of the stream is a natural message*)
lemma tsum5_h_scons:"a\<noteq>\<surd> \<Longrightarrow> tsum5_h n \<cdot>(\<up>a\<bullet>s) = (\<up>(\<M>(n+(\<M>\<inverse> a)))) \<bullet> (tsum5_h (n+ (\<M>\<inverse> a))\<cdot>s)"  
apply (simp add: tsum5_h_def)
apply (subst beta_cfun, rule cont_lub_tsum5_h)+
apply (subst contlub_cfun_arg)
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "a"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
apply (subst lub_range_shift [where j="Suc 0", THEN sym])
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "a"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
by (simp add: chain_tsh_helper)

(*Describes the unfolding of tsum5_h if the first element of the stream is a \<surd>*)
lemma tsum5_h_scons_tick:"tsum5_h n \<cdot>(\<up>\<surd>\<bullet>s) = \<up>\<surd> \<bullet> (tsum5_h n \<cdot>s)"
apply (simp add: tsum5_h_def)
apply (subst beta_cfun, rule cont_lub_tsum5_h)+
apply (subst contlub_cfun_arg)
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "n"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
apply (subst lub_range_shift [where j="Suc 0", THEN sym])
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "n"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
by (simp add: chain_tsh_helper)

(*Other lemma with the same meaning as tsum5_h_scons_tick*)
lemma tsum5_h_scons_tick_2: "s=\<up>\<surd>\<bullet>as \<Longrightarrow> tsum5_h n\<cdot>s = (\<up>\<surd>)\<bullet>(tsum5_h n\<cdot> as)"
by (simp add: tsum5_h_scons_tick)

(*Other lemma with the same meaning as tsum5_h_scons*)
lemma tsum5_h_scons_2:"shd s\<noteq>\<surd> \<and> s\<noteq>\<epsilon>\<Longrightarrow> tsum5_h n \<cdot>s = (\<up>(\<M>(n+(\<M>\<inverse> shd s)))) \<bullet> (tsum5_h (n+ (\<M>\<inverse> shd s))\<cdot>(srt\<cdot>s))"
using tsum5_h_scons
by (metis surj_scons)

lemma tsum5_h_scons_tick_alternative:"a=\<surd> \<Longrightarrow> tsum5_h n \<cdot>(\<up>a\<bullet>s) = \<up>a \<bullet> (tsum5_h n \<cdot>s)"
by(simp add: tsum5_h_scons_tick)

(*tsum5_h of an empty stream is an empty stream*)
lemma tsum5_empty[simp]: "tsum5_h p\<cdot>\<epsilon> = \<epsilon>"
by (simp add: cont_lub_tsum5_h tsh_bot tsum5_h_def)

(*unfolding tsum5_h with the definition*)
lemma tsum5_h_unfold_tsh: "tsum5_h n \<cdot>input = (\<Squnion>i. tsh i n input)"
apply (simp add:tsum5_h_def)
by (simp add: cont_lub_tsum5_h)

(*Shows that the message of a natural number of an nat event plus 0 is the nat event*)
lemma msg_plus0[simp]:fixes a::"nat event" shows" a\<noteq>\<surd> \<Longrightarrow>\<M> (0+(\<M>\<inverse> a)) = a"
by (metis add.left_neutral event.exhaust event.simps(4))

(*shd of tsum5_h if the head is not \<surd>*)
lemma tsum5_h_shd [simp]: "a\<noteq>\<surd> \<Longrightarrow> shd (tsum5_h n \<cdot>(\<up>a \<bullet> as)) = \<M> (n+(\<M>\<inverse> a))"
by (simp add: tsum5_h_scons)

(*shd of tsum5_h if the head is not \<surd>*)
lemma tsum5_h_shd_2 [simp]: "shd s\<noteq>\<surd> \<and> s\<noteq>\<epsilon> \<Longrightarrow> shd (tsum5_h n \<cdot>s) = \<M> (n+(\<M>\<inverse> shd s))"
by (simp add: tsum5_h_scons_2)

(*The head of tsum5_h is the head of the input*)
lemma tsum5_shd: "shd (tsum5_h 0\<cdot>ts) = shd ts"
apply(cases "ts= \<epsilon>")
apply simp
apply(cases "shd ts= \<surd>")
apply (metis shd1 surj_scons tsum5_h_scons_tick)
by (metis msg_plus0 surj_scons tsum5_h_shd)

(*A stream filtered by \<surd>s only contains \<surd>*)
lemma "#({\<surd>} \<ominus> s) = Fin (Suc n) \<Longrightarrow> ({\<surd>} \<ominus> s)= (\<up>\<surd>)\<bullet>(srt\<cdot>({\<surd>} \<ominus> s))"
by (metis Fin_02bot inject_Fin lnzero_def nat.simps(3) sfilter_resl2 singletonD slen_empty_eq surj_scons)

(*#(tsum5_h s)is at least the length of s*)
lemma tsum5_h_slen2: "#s \<le> #(tsum5_h a\<cdot>s)"
apply (rule spec [where x = a])
apply (rule ind [of _ s], auto)
apply(subst lnle_def, simp del: lnle_conv)
by (smt lnsuc_lnle_emb slen_scons tsum5_h_scons tsum5_h_scons_tick)

(*The rest of tsum5_h s is tsum5_h (srt s) if the head of s is a \<surd>*)
lemma tsum5_h_srt_tick: "shd s=\<surd> \<Longrightarrow>srt\<cdot>(tsum5_h n \<cdot>s) = tsum5_h n\<cdot> (srt\<cdot>s)"
by (metis (no_types, lifting) inject_scons lshd_updis stream.sel_rews(2) stream.sel_rews(3) surj_scons tsum5_empty tsum5_h_scons_tick)

(*Unfolding the rest of tsum5_h if the head is not a \<surd>*)
lemma tsum5_h_srt: "shd s\<noteq>\<surd> \<Longrightarrow>srt\<cdot>(tsum5_h n \<cdot>s) = tsum5_h (n+(\<M>\<inverse> shd s))\<cdot> (srt\<cdot>s)"
apply(cases "s=\<epsilon>")
apply simp
using tsum5_h_scons
proof -
  assume a1: "s \<noteq> \<epsilon>"
  assume a2: "shd s \<noteq> \<surd>"
  have f3: "\<up>(shd s) \<bullet> srt\<cdot>s = s"
    using a1 by (metis surj_scons)
  have "\<And>e s. updis (e::nat event) \<noteq> \<bottom> \<or> (\<epsilon>::nat event stream) = s"
    by simp
  then show ?thesis
    using f3 a2 a1 by (metis lscons_conv stream.sel_rews(5) tsum5_h_scons)
qed

(*tsum5_h has the length of the input*)
lemma tsum5_h_slen[simp]: "#(tsum5_h n\<cdot>s) = #s"
apply (rule spec [where x = n])
apply (rule ind [of _ s], auto)
using tsum5_h_scons
by (metis slen_scons tsum5_h_scons_tick)

(*Unfolds tsum5_h with a \<up>(Msg m) as the input*)
lemma [simp]: "a\<noteq>\<surd> \<Longrightarrow> tsum5_h n\<cdot>(\<up>a) = (\<up>(\<M>(n+(\<M>\<inverse> a))))"
by (metis lscons_conv sup'_def tsum5_empty tsum5_h_scons)

(*tsum5_h of a ts_well \<up>a is \<up>a*)
lemma tsum5_h_one[simp]: "ts_well (\<up>a) \<Longrightarrow> tsum5_h n\<cdot>(\<up>a) = \<up>(a)"
apply(cases "a\<noteq>\<surd>")
apply (simp add: tsOneTick)
apply auto
apply(insert tsum5_h_scons_tick [of n \<epsilon>])
by simp

(*Length of tsAbs ts of a timedstream ts*)
lemma tsAbs_len[simp]: "ts_well s \<Longrightarrow> #(tsAbs\<cdot>(Abs_tstream s)) = #({e. e\<noteq>\<surd>}\<ominus> s)"
by(subst tsabs_insert, simp)

(*Length of tsum5_h of a event stream without ticks is eqaul to the length of sum5 of tsAbs*)
lemma tsum5_h_sfilter_len: "ts_well s \<Longrightarrow> #(tsum5_h n\<cdot>({e. e\<noteq>\<surd>}\<ominus>s)) = #(sum5\<cdot>(tsAbs\<cdot>(Abs_tstream s)))"
by simp

(*sum5_h unfolding when the head of the stream is 0 is the parameter concatenated to sum5_h with the rest of the stream*)
lemma tsum5_unfold_tsum5: "tsum5_h n\<cdot>(\<up>(\<M> 0) \<bullet> s) =\<up>(\<M> (0+n)) \<bullet> tsum5_h n \<cdot>(s)"
apply(subst tsum5_h_scons)
apply simp
by simp

(*the (Suc nth) element of sum5_h when the head of the stream is 0 is the nth element of sum5_h with the rest stream*)
lemma test2_tsum5_h_help: "Fin n < #s \<longrightarrow> snth (Suc n) (tsum5_h m \<cdot>(\<up>(\<M> 0) \<bullet>s)) = snth n (tsum5_h m \<cdot>s)"
apply(induction n)
apply(subst tsum5_unfold_tsum5)
apply simp
by (simp add: tsum5_unfold_tsum5)

(*the (Suc nth) element of tsum5_h when the head of the stream is \<surd> is the nth element of tsum5_h with the rest stream*)
lemma tsum5_suc_snth_tick:"Fin n < #s \<and> shd s =\<surd> \<Longrightarrow> snth (Suc n) (tsum5_h m\<cdot>s) = snth n (tsum5_h m\<cdot>(srt\<cdot>s))"
apply(subst tsum5_h_scons_tick_2)
apply auto
by (metis Fin_0 less_le lnle_Fin_0 strict_slen surj_scons)

(**the (Suc nth) element of tsum5_h m s when the head of the stream is not \<surd> is the nth element of tsum5_h (m + shd s)  with the rest stream**)
lemma tsum5_suc_snth:"Fin n < #s \<and> shd s \<noteq>\<surd> \<and> s\<noteq>\<epsilon> \<Longrightarrow> snth (Suc n) (tsum5_h m\<cdot>s) = snth n (tsum5_h (m+ \<M>\<inverse> shd s)\<cdot>(srt\<cdot>s))"
apply(subst tsum5_h_scons_2)
by auto

(*taking only \<surd>s of tsum5_h is the same as taking \<surd>s of the input*)
lemma tsum5_ticknum_helper[simp]: "({\<surd>} \<ominus> tsum5_h n\<cdot>ts) =({\<surd>} \<ominus> ts) "
apply(cases "ts=\<epsilon>", simp)
apply(induction ts arbitrary: n,auto)
proof -
  fix u :: "nat event discr\<^sub>\<bottom>" and ts :: "nat event stream" and n:: nat
  assume a1: "u\<noteq>\<bottom>"
  assume a2: "(\<And>n. ts \<noteq> \<epsilon> \<Longrightarrow> {\<surd>} \<ominus> tsum5_h n\<cdot>ts = {\<surd>} \<ominus> ts)"
  then show "{\<surd>} \<ominus> tsum5_h n\<cdot>(u && ts) = {\<surd>} \<ominus> u && ts"
  apply(insert a1 a2)
  apply(cases "u=updis \<surd>")
  apply(insert lscons_conv[of \<surd> ts])
  apply(subst tsum5_h_scons_tick_2, auto)
  using a2 apply force
  apply(subst tsum5_h_scons_2)
  apply (metis stream.con_rews(2) stream.injects stream.sel_rews(5) surj_scons)
  apply simp
  using a2
  by (metis (no_types, lifting) sfilter_nin singletonD stream.con_rews(2) stream.sel_rews(4) stream.sel_rews(5) surj_scons tsum5_empty)
qed

(*There are as much \<surd>s in the output as there are in the Input*)
lemma tsum5_ticknum[simp]:"#({\<surd>} \<ominus> tsum5_h 0\<cdot>ts) =#({\<surd>} \<ominus> ts)"
by simp

(*helper for tswell_tsum5*)
lemma tsum5_srt2input:"(\<exists>x. srt\<cdot>(tsum5_h n\<cdot>s) = tsum5_h x\<cdot>(srt\<cdot>s))"
apply(cases "s=\<epsilon>", simp)
apply(cases "shd s=\<surd>")
apply(subst tsum5_h_scons_tick_2, auto)
using surj_scons apply fastforce
by(subst tsum5_h_scons_2, auto)

(*helper for tswell_tsum5*)
lemma tsum5_sucn_sdrop:"(\<exists>x. sdrop (Suc n)\<cdot>(tsum5_h 0\<cdot>s) = sdrop n\<cdot> (tsum5_h x\<cdot>(srt\<cdot>s)))"
apply(subst sdrop_forw_rt)
using tsum5_srt2input
by metis

(*helper for tswell_tsum5*)
lemma tsum5_sdrop2input:"(\<exists>x. sdrop n\<cdot>(tsum5_h 0\<cdot>s) = tsum5_h x\<cdot>(sdrop n\<cdot>s))"
apply(induction n arbitrary: s, auto)
using tsum5_sucn_sdrop
by (smt iterate_Suc lscons_conv sdrop_def stream.sel_rews(2) stream.sel_rews(5) surj_scons tsum5_empty tsum5_h_scons tsum5_h_srt_tick up_defined)

(*helper for tswell_tsum5*)
lemma tsum5_snth2input:" (\<exists>x. snth n (tsum5_h 0\<cdot>s) = shd (tsum5_h x\<cdot> (sdrop n\<cdot> s)))"
apply(simp add: snth_def)
using tsum5_sdrop2input by metis

(*if the nth element of the input is a \<surd> so is the nth element of the output*)
lemma tsum5_snthtick2output:" snth n s=\<surd> \<Longrightarrow> snth n (tsum5_h 0\<cdot>s) =\<surd>"
apply(simp add: snth_def)
apply(insert tsum5_snth2input[of n s])
apply auto
by (metis shd1 snth_def surj_scons tsum5_empty tsum5_h_scons_tick)

(*if the input has a \<surd> at the end so does the output*)
lemma tsum5_sfoot_helper:"#s<\<infinity> \<Longrightarrow> sfoot (tsum5_h 0\<cdot>(s \<bullet> \<up>\<surd>)) = \<surd>"
apply(simp add: sfoot_def)
apply(subst tsum5_snthtick2output, auto)
by(insert sfoot12[of s \<surd>],simp add: sfoot_def)

(*if the input of tsum5_h is well formed so is the output*)
lemma tswell_tsum5:"ts_well ts \<Longrightarrow> ts_well (tsum5_h 0\<cdot>ts)"
apply(cases "#ts=\<infinity>")
apply(simp add: ts_well_def, auto)+
using tsum5_sfoot_helper
by (metis inf_ub less_le sconc_fst_inf sfoot2)

(*unfolding of tsum5 with the definition*)
lemma tsum5_unfold: "tsum5\<cdot> ts = Abs_tstream (tsum5_h 0\<cdot> (Rep_tstream ts))"
by (simp add: tsum5_def tswell_tsum5)


(*Test of tsum5*)

(*the test nat event stream is well formed*)
lemma tswell_test: "ts_well ((<[n1,\<surd>,n2,\<surd>,\<surd>,n3]>) \<bullet> (sinftimes(\<up>\<surd>)))"
by(simp add: ts_well_def)

(*Result of the first part of the teststream with tsum5_h 0*)
lemma tsum5_h_test_helper1: "tsum5_h 0\<cdot>(<[\<M> 1,\<surd>,\<M> 2,\<surd>,\<surd>,\<M> 4]>) =(<[\<M> 1,\<surd>,\<M> 3,\<surd>,\<surd>,\<M> 7]>)"
by (simp add: tsum5_h_scons tsum5_h_scons_tick numeral_3_eq_3)

(*result of the last part of the teststream with tsum5_h n*)
lemma tsum5_h_test_helper2: "tsum5_h n \<cdot>(sinftimes(\<up>\<surd>)) = sinftimes(\<up>\<surd>)"
by (metis s2sinftimes sinftimes_unfold tsum5_h_scons_tick)

(*result of the teststream with tsum5_h 0*)
lemma tsum5_h_test: "tsum5_h 0 \<cdot>((<[\<M> 1,\<surd>,\<M> 2,\<surd>,\<surd>,\<M> 4]>) \<bullet> (sinftimes(\<up>\<surd>))) = ((<[\<M> 1,\<surd>,\<M> 3,\<surd>,\<surd>,\<M> 7]>) \<bullet> (sinftimes(\<up>\<surd>)))"
using tsum5_h_test_helper1 tsum5_h_test_helper2
by (simp add: tsum5_h_scons tsum5_h_scons_tick numeral_3_eq_3)

(*Tests the output of tsum5*)
lemma tssum5_test:"tsum5\<cdot> (Abs_tstream ((<[\<M> 1, \<surd>, \<M> 2, \<surd>, \<surd>, \<M> 4]>) \<bullet> (sinftimes(\<up>\<surd>))))
 =(Abs_tstream ((<[\<M> 1,\<surd>,\<M> 3,\<surd>,\<surd>,\<M> 7]>) \<bullet> (sinftimes(\<up>\<surd>))))"
apply(simp add: tsum5_unfold)
apply (subst Rep_Abs)
using tswell_test apply auto
using tsum5_h_test_helper2
by (simp add: tsum5_h_scons tsum5_h_scons_tick numeral_3_eq_3)


(*tsAbs(tsum5 ts) = sum5(tsAbs ts)*)

(*\<M>\<inverse> of \<M> a is a*)
lemma[simp]:"\<M>\<inverse> (\<M> a) = a "
by simp

(*the (Suc nth) element of tsum5_h m s of a stream without \<surd>s is the nth element of tsum5_h (m+ shd s) with the rest stream*)
lemma tsum5_sfilter_snth_helper:"Fin n < #({e. e\<noteq>\<surd>}\<ominus> s) \<and> ({e. e\<noteq>\<surd>}\<ominus> s)\<noteq>\<epsilon> \<Longrightarrow> snth (Suc n) (tsum5_h m\<cdot>({e. e\<noteq>\<surd>}\<ominus> s)) = snth n (tsum5_h (m+ \<M>\<inverse> shd ({e. e\<noteq>\<surd>}\<ominus> s))\<cdot>(srt\<cdot>({e. e\<noteq>\<surd>}\<ominus> s)))"
apply(subst tsum5_h_scons_2)
using sfilter_ne_resup apply auto[1]
by auto

(*sfilter_lemmas*)
lemma sfilter_filtered: "({a} \<ominus> ({e. e \<noteq> a} \<ominus> s)) = \<epsilon>"
using ex_snth_in_sfilter_nempty by auto

lemma sfilter_length_srt: "#({a}\<ominus> (srt\<cdot>s)) \<le> #({a}\<ominus> s)"
by (metis (no_types, lifting) eq_iff less_lnsuc sfilter_in sfilter_nin slen_scons stream.sel_rews(2) surj_scons)

(*helper for tsum5_h_sfilter_snth*)
lemma sfilter_filtered_len_srt: "({a} \<ominus> (srt\<cdot>({e. e \<noteq> a} \<ominus> s))) = \<epsilon>"
by (metis (mono_tags, lifting) mem_Collect_eq sdom_sfilter1 sfilter2dom sfilter_srtdwl3)

(*The nat of snth nat event of tsum5_h m s is the snth of tsum5_h 0 s + m*)
lemma tsum5_sfilter_snth_unfold:"Fin n < #s \<and> #({\<surd>}\<ominus> s) = 0 \<Longrightarrow> \<M>\<inverse> snth n (tsum5_h m\<cdot>s) = \<M>\<inverse> snth n (tsum5_h 0\<cdot>s) + m"
apply(induction n arbitrary: m s, simp)
apply(subst tsum5_h_scons_2)
apply (metis lnsuc_neq_0_rev sfilter_in singletonI slen_empty_eq slen_scons surj_scons)
apply (subst tsum5_h_shd_2)
apply (metis lnsuc_neq_0_rev sfilter_in singletonI slen_empty_eq slen_scons surj_scons)
apply simp
apply simp
apply(simp add: snth_rt)
apply(insert tsum5_h_srt, auto)
by (smt Fin_Suc add.commute add.left_commute insert_iff less_imp_not_less lnle_Fin_0 lnsuc_lnle_emb lscons_conv not_less old.nat.distinct(2) ord_eq_less_trans sfilter_in sfilter_nin slen_empty_eq slen_scons stream.con_rews(2) surj_scons)


(*without \<surd>s in stream tsum5_h unfolding the snth+1 element *)
lemma tsum5_h_sfilter_snth:"Fin (Suc n) < #({e. e\<noteq>\<surd>}\<ominus> s) \<and> ({e. e\<noteq>\<surd>}\<ominus> s)\<noteq>\<epsilon> \<Longrightarrow> 
\<M>\<inverse> snth (Suc n) (tsum5_h m\<cdot>({e. e\<noteq>\<surd>}\<ominus> s)) = \<M>\<inverse> snth n (tsum5_h 0\<cdot>(srt\<cdot>({e. e\<noteq>\<surd>}\<ominus> s))) +(m+ \<M>\<inverse> shd ({e. e\<noteq>\<surd>}\<ominus> s))"
apply(subst tsum5_sfilter_snth_helper)
apply simp
apply (metis Fin_leq_Suc_leq Suc_n_not_le_n less2nat_lemma less_le)
apply(subst tsum5_sfilter_snth_unfold)
apply(subst sfilter_filtered_len_srt, simp)
apply (metis Fin_Suc lnsuc_lnle_emb not_less slen_scons surj_scons)
by simp

lemma tsum5_sfilter_snth:"Fin (Suc n) < #({e. e\<noteq>\<surd>}\<ominus> s) \<and> ({e. e\<noteq>\<surd>}\<ominus> s)\<noteq>\<epsilon> \<Longrightarrow> 
\<M>\<inverse> snth (Suc n) (tsum5_h 0\<cdot>({e. e\<noteq>\<surd>}\<ominus> s)) = \<M>\<inverse> snth n (tsum5_h 0\<cdot>(srt\<cdot>({e. e\<noteq>\<surd>}\<ominus> s))) +\<M>\<inverse> shd ({e. e\<noteq>\<surd>}\<ominus> s)"
by(insert tsum5_h_sfilter_snth [of n s 0], simp)

lemma sum3_snth_2:"Fin (Suc n) < #s \<Longrightarrow> snth (Suc n) (sum3\<cdot>s) = snth n (sum3\<cdot>(srt\<cdot>s)) + shd s"
apply(insert sum3_snth[of n s 0], simp)
by (metis less_le lnle_Fin_0 nat.distinct(1) not_less slen_rt_ile_eq strict_slen sum4_snth sum52sum3 sum52sum4 surj_scons)

(*special case for snth 0 (smap f\<cdot>s)*)
lemma [simp]:"s\<noteq> \<epsilon> \<Longrightarrow> shd (smap f\<cdot>s) = f (shd s)"
apply(insert smap_snth_lemma [of 0], simp)
by (smt shd1 smap_scons surj_scons)

(*another variant of sum4_snth*)
lemma sum4_snth_2:"Fin (Suc n) < #s \<Longrightarrow> snth (Suc n) (sum4\<cdot>s) = snth n (sum4\<cdot>(srt\<cdot>s)) + shd s"
using sum4_snth
by (metis less_le lnle_Fin_0 nat.distinct(1) not_less slen_rt_ile_eq strict_slen surj_scons)

lemma sfilter_sfilter[simp]: "{a}\<ominus>{a}\<ominus>s = {a}\<ominus>s"
by simp

lemma tsum5_h_snth2sum3_snth:"Fin n < #({e. e\<noteq>\<surd>}\<ominus> s) \<and> ({e. e\<noteq>\<surd>}\<ominus> s)\<noteq>\<epsilon> \<Longrightarrow>
 \<M>\<inverse> snth n (tsum5_h 0\<cdot>({e. e\<noteq>\<surd>}\<ominus> s)) = snth n (sum3\<cdot>(smap (\<lambda>e. \<M>\<inverse> e)\<cdot>({e. e\<noteq>\<surd>}\<ominus> s)))"
apply(induction n arbitrary: s, simp+)
apply(subst tsum5_h_shd_2, simp)
using sfilter_ne_resup apply auto[1]
apply simp
apply(subst tsum5_sfilter_snth)
apply linarith
apply(subst sum3_snth_2)
apply simp+
by (smt inject_scons less2lnleD lnle_Fin_0 nat.distinct(1) not_less sfilter_srtdwl3 slen_rt_ile_eq slen_smap smap1 smap_split strict_slen surj_scons)

(*helper for tsum52sum4_helper*)
lemma tsum5_h2sum3:"smap (\<lambda>e. \<M>\<inverse> e)\<cdot> (tsum5_h 0\<cdot>({e. e\<noteq>\<surd>}\<ominus> s)) = sum3\<cdot>(smap (\<lambda>e. \<M>\<inverse> e)\<cdot>({e. e\<noteq>\<surd>}\<ominus> s))"
apply(rule snths_eq, simp)
apply auto
apply(subst smap_snth_lemma)
apply simp
apply(rule tsum5_h_snth2sum3_snth, auto)
by (metis Fin_0 less_le lnle_Fin_0)

(*If you filter out \<surd>s the length of the input stream is equal to the length of the output stream*)
lemma sfilter_in_tsum_helper_len[simp]: " #({e. e \<noteq> \<surd>} \<ominus> tsum5_h n\<cdot>ts) = #({e. e \<noteq> \<surd>} \<ominus> ts)"
apply(induction ts arbitrary: n, auto)
proof -
  fix u :: "nat event discr\<^sub>\<bottom>" and ts :: "nat event stream" and n:: nat
  assume a1: "u\<noteq>\<bottom>"
  assume a2: "(\<And>n. #({e. e \<noteq> \<surd>} \<ominus> tsum5_h n\<cdot>ts) = #({e. e \<noteq> \<surd>} \<ominus> ts))"
  then show "#({e. e \<noteq> \<surd>} \<ominus> tsum5_h n\<cdot>(u && ts)) = #({e. e \<noteq> \<surd>} \<ominus> u && ts)"
  apply(insert a1 a2)
  apply(cases "u=updis \<surd>")
  apply(insert lscons_conv[of \<surd> ts])
  apply(subst tsum5_h_scons_tick_2, auto)
  apply(subst tsum5_h_scons_2)
  apply (metis stream.con_rews(2) stream.injects stream.sel_rews(5) surj_scons)
  apply simp
by (smt lshd_updis mem_Collect_eq sfilter_in slen_scons stream.con_rews(2) stream.sel_rews(4) stream.sel_rews(5) surj_scons)
qed

(*it does not matter if i filter out the \<surd>s in at the input or the output*)
lemma sfilter_in_tsum5:"{e. e \<noteq> \<surd>} \<ominus> tsum5_h n\<cdot>ts = tsum5_h n\<cdot>({e. e \<noteq> \<surd>} \<ominus> ts)"
apply(cases "ts=\<epsilon>",simp)
apply(induction ts arbitrary: n, auto)
proof -
  fix u :: "nat event discr\<^sub>\<bottom>" and ts :: "nat event stream" and n:: nat
  assume a1: "u\<noteq>\<bottom>"
  assume a2: "(\<And>n. ts \<noteq> \<epsilon> \<Longrightarrow> {e. e \<noteq> \<surd>} \<ominus> tsum5_h n\<cdot>ts = tsum5_h n\<cdot>({e. e \<noteq> \<surd>} \<ominus> ts))"
  then show "{e. e \<noteq> \<surd>} \<ominus> tsum5_h n\<cdot>(u && ts) = tsum5_h n\<cdot>({e. e \<noteq> \<surd>} \<ominus> u && ts)"
  apply(insert a1 a2)
  apply(cases "u=updis \<surd>")
  apply(insert lscons_conv[of \<surd> ts])
  apply(subst tsum5_h_scons_tick_2, auto)
  apply fastforce
  apply(subst tsum5_h_scons_2)
  apply (metis stream.con_rews(2) stream.injects stream.sel_rews(5) surj_scons)
  apply simp
  by (smt mem_Collect_eq sfilter_in stream.con_rews(2) stream.injects stream.sel_rews(5) strict_sfilter surj_scons tsum5_empty tsum5_h_scons)
qed

(*helper for tsum52sum4*)
lemma tsum52sum3_helper:"smap (\<lambda>e. \<M>\<inverse> e)\<cdot> ({e. e\<noteq>\<surd>}\<ominus> (Rep_tstream (tsum5\<cdot> ts))) = sum3\<cdot>(smap (\<lambda>e. \<M>\<inverse> e)\<cdot>({e. e\<noteq>\<surd>}\<ominus> (Rep_tstream ts)))"
apply(subst tsum5_unfold)
apply(subst Rep_Abs)
using tswell_tsum5 apply auto
apply(subst sfilter_in_tsum5)
apply(subst tsum5_h2sum3)
by simp

(*tsum5 and sum4 work the same way over naturals*)
lemma tsum52sum3:"tsAbs\<cdot>(tsum5\<cdot> ts) = sum3\<cdot>(tsAbs\<cdot>ts)"
apply(simp add: tsabs_insert)
by(rule tsum52sum3_helper)

(*shows that tsum5 is a weak causal*)
lemma tsWeak2tsum5:"tsWeakCausal (\<lambda> ts. Abs_tstream (tsum5_h 0\<cdot>(Rep_tstream ts)))"
apply(subst tsWeak2cont2)
apply(simp add: tsTickCount_def)
apply(subst Rep_Abs, auto)
by(simp add: tswell_tsum5)+

lemma tsWeak_tsum5:"tsWeakCausal(\<lambda> ts. tsum5\<cdot>ts)"
by(simp add: tsum5_unfold tsWeak2tsum5)

(*definition tsum_nth like sum_nth*)
primrec tsum_nth:: "nat \<Rightarrow> nat event stream \<Rightarrow> nat" where
"tsum_nth 0 s = (if shd s=\<surd> then 0 else \<M>\<inverse> shd s)" |
"tsum_nth (Suc n) s = (if shd s=\<surd> then 0 + tsum_nth n (srt\<cdot>s) else (\<M>\<inverse>(shd s)) + tsum_nth n (srt\<cdot>s))"



(*if the nth element of the output is a \<surd> so is the nth element of the input*)
lemma tsum5_snthtick2input:" snth n (tsum5_h 0\<cdot>s) =\<surd> \<Longrightarrow> snth n s =\<surd>"
by (metis event.distinct(1) shd1 snth_def surj_scons tsum5_empty tsum5_h_scons tsum5_sdrop2input)

lemma tsum5_snthtick2input_equiv:" snth n (tsum5_h 0\<cdot>s) =\<surd> \<longleftrightarrow> snth n s =\<surd>"
by(insert tsum5_snthtick2input[of n s] tsum5_snthtick2output[of n s], auto)

(*if the shd s is \<surd> the sum of s is the sum of the rest of s*)
lemma tsum_nth_suc_tick: "shd s=\<surd> \<Longrightarrow> tsum_nth (Suc n) s = tsum_nth n (srt\<cdot>s)"
by(simp add: tsum_nth_def)

(*if the shd s is not \<surd> the sum of s is the sum of the rest of s plus shd s*)
lemma tsum_nth_suc: "shd s\<noteq>\<surd> \<Longrightarrow> tsum_nth (Suc n) s = \<M>\<inverse> shd s + tsum_nth n (srt\<cdot>s)"
by(simp add: tsum_nth_def)

(* \<M> before \<M>\<inverse>*)
lemma MsginvMsg: "x\<noteq>\<surd> \<Longrightarrow> \<M> \<M>\<inverse>x=x"
by (metis event.exhaust event.simps(4))

(*helper for tsum5_h_2tsum_tnh_helper*)
lemma tsum5_h_extract_state:"Fin n < #s \<and>  snth n s \<noteq> \<surd> \<and> s\<noteq>\<epsilon> \<Longrightarrow> snth n (tsum5_h m\<cdot>s) = \<M> \<M>\<inverse> snth n (tsum5_h 0\<cdot>s) + m"
apply(induction n arbitrary: m s, auto)
apply(simp add: snth_rt)
proof -
  fix s :: "nat event stream" and n:: nat and m:: nat
  assume a1: "(\<And>m s. Fin n < #s \<and> snth n s \<noteq> \<surd> \<and> s \<noteq> \<epsilon> \<Longrightarrow> snth n (tsum5_h m\<cdot>s) = \<M> \<M>\<inverse> snth n (tsum5_h 0\<cdot>s) + m)"
  assume a2: "Fin (Suc n) < #s"
  assume a3: " snth n (srt\<cdot>s) \<noteq> \<surd>"
  assume a4: "s \<noteq> \<epsilon>"
  then show "snth n (srt\<cdot>(tsum5_h m\<cdot>s)) = \<M> \<M>\<inverse> snth n (srt\<cdot>(tsum5_h 0\<cdot>s)) + m"
  apply(cases "shd s=\<surd>")
  apply(simp add: tsum5_h_srt_tick)
  apply(insert a1 a2 a3)
  apply(metis less2lnleD lnle_Fin_0 nat.distinct(1) not_less slen_rt_ile_eq strict_slen)
  apply(simp add: tsum5_h_srt)
  by (smt a2 add.left_commute add.right_neutral event.inject event.simps(4) less2lnleD lnle_Fin_0 not_le old.nat.distinct(2) slen_empty_eq slen_rt_ile_eq)
qed


(*if the nth element of the input is not \<surd>, then the nth element of the output is equal to tsum_nth n input*)
lemma tsum5_h2tsum_nth_helper:"Fin n < #s \<Longrightarrow> snth n s \<noteq> \<surd> \<Longrightarrow> snth n (tsum5_h 0\<cdot>s) = \<M> tsum_nth n s"
apply(cases "s=\<epsilon>")
apply(simp add: lnless_def MsginvMsg)
apply(induction n arbitrary: s,auto)
apply(subst tsum5_suc_snth_tick)
apply(metis Fin_leq_Suc_leq less_le not_le)
apply (metis less2lnleD lnle_Fin_0 nat.distinct(1) not_le slen_rt_ile_eq snth_rt strict_slen)
apply(subst tsum5_h_scons_2,simp+)
apply(subst tsum5_h_extract_state)
apply (metis less2lnleD lnle_Fin_0 nat.simps(3) not_le slen_rt_ile_eq snth_rt strict_slen)
apply auto
by (metis event.simps(4) less2lnleD lnle_Fin_0 not_le old.nat.distinct(2) slen_empty_eq slen_rt_ile_eq snth_rt)


(*helper for tsum52tsum_nth*)
lemma tsum5_h2tsum_nth:"Fin n< #s \<Longrightarrow> snth n (tsum5_h 0\<cdot> s) = (case (snth n s) of Msg a \<Rightarrow> \<M> tsum_nth n s | \<surd> \<Rightarrow> \<surd>)"
apply(cases "snth n s =\<surd>")
apply(induction n arbitrary: s, simp add: tsum5_shd)
apply(subst tsum5_snthtick2output, auto)
apply(subst tsum5_h2tsum_nth_helper, auto)
by (metis event.exhaust event.simps(4))

(*if the nth element of the input is \<surd>, so is the nth element of the output. Otherwise it is tsum n input for the nth element*)
lemma tsum52tsum_nth:"Fin n< #(Rep_tstream ts) \<Longrightarrow> snth n (Rep_tstream(tsum5\<cdot> ts)) = (case (snth n (Rep_tstream ts)) of Msg a \<Rightarrow> \<M> tsum_nth n (Rep_tstream ts) | \<surd> \<Rightarrow> \<surd>) "
apply(simp add: tsum5_unfold)
apply(subst Rep_Abs)
using tswell_tsum5 apply simp
by(subst tsum5_h2tsum_nth, simp+)


lemma tsum_nth_shd:"shd s\<noteq>\<surd> \<Longrightarrow> tsum_nth 0 s = \<M>\<inverse>shd s"
by auto

lemma "({e. e\<noteq>\<surd>}\<ominus> s) \<noteq>\<epsilon> \<Longrightarrow> shd ({e. e \<noteq> \<surd>} \<ominus> s) \<noteq> \<surd>"
using sfilter_ne_resup by auto

lemma filtereps2tsAbseps:"ts_well s \<and> {e. e \<noteq> \<surd>} \<ominus> s = \<epsilon> \<Longrightarrow> tsAbs\<cdot>(Abs_tstream s) = \<epsilon>"
by(subst tsabs_insert, simp)


lemma tsum_nth2sum_nth_helper:" {e. e \<noteq> \<surd>} \<ominus> s \<noteq> \<epsilon> \<Longrightarrow> shd ({e. e \<noteq> \<surd>} \<ominus> s) \<noteq> \<surd>"
using sfilter_ne_resup by auto

lemma srtSmap:"srt\<cdot>(smap f\<cdot>s) = smap f\<cdot>(srt\<cdot>s)"
by (metis sdrop_0 sdrop_forw_rt sdrop_smap)

lemma tsum_nth_nth: "Fin (Suc n) <#({e. e\<noteq>\<surd>}\<ominus> s) \<longrightarrow> tsum_nth (Suc n) ({e. e\<noteq>\<surd>}\<ominus> s) = tsum_nth n ({e. e\<noteq>\<surd>}\<ominus> s) + \<M>\<inverse>snth (Suc n) ({e. e\<noteq>\<surd>}\<ominus> s)"
apply(induction n arbitrary: s)
apply (metis (mono_tags, lifting) mem_Collect_eq sfilterl7 snth_rt snth_shd tsum_nth.simps(1) tsum_nth.simps(2))
using Fin_Suc lnat_po_eq_conv lnle_def lnless_def lnsuc_lnle_emb lnzero_def minimal slen_scons snth_scons strict_slen surj_scons
by (smt add.assoc not_less sfilter_srtdwl3 tsum_nth.simps(2))

lemma tsum_nth2sum_nth:"Fin  n <#({e. e\<noteq>\<surd>}\<ominus> s)\<and>({e. e\<noteq>\<surd>}\<ominus> s) \<noteq> \<epsilon> \<Longrightarrow>ts_well s \<Longrightarrow> tsum_nth n ({e. e\<noteq>\<surd>}\<ominus> s) = sum_nth n (tsAbs\<cdot>(Abs_tstream s))"
apply(induction n)
apply(subst tsum_nth_shd)
using sfilter_ne_resup mem_Collect_eq apply blast
apply(subst sum_nth.simps)
apply(simp add: tsabs_rep_eq)
apply(subst tsum_nth_nth, simp)
apply(subst sum_nth_nth, simp)
apply(simp add: tsabs_insert)
apply(simp add: snth_rt)
apply(subst srtSmap)
by (smt Suc_n_not_le_n less2nat_lemma not_le slen_rt_ile_eq smap_snth_lemma trans_lnless)

lemma sdrop_eps:"Fin  n \<ge> #s \<Longrightarrow> sdrop n\<cdot>s=\<epsilon>"
apply (induction n arbitrary: s, auto)
by (simp add: sdrop_forw_rt slen_rt_ile_eq)

lemma snth_eps:"Fin  n \<ge> #s \<Longrightarrow> snth n s= shd \<epsilon>"
apply(simp add: snth_def)
by(subst sdrop_eps, auto)

lemma tsum_nth2sum_nth_inf:"#({e. e\<noteq>\<surd>}\<ominus> s) =\<infinity> \<Longrightarrow>ts_well s \<Longrightarrow> tsum_nth n ({e. e\<noteq>\<surd>}\<ominus> s) = sum_nth n (tsAbs\<cdot>(Abs_tstream s))"
by (metis Inf'_neq_0_rev leI notinfI3 slen_empty_eq tsum_nth2sum_nth)


  
primrec list2ts_alter :: "'a event list \<Rightarrow> 'a tstream"
where
  list2ts_alter_0:   "list2ts_alter [] = \<bottom>" |
  list2ts_alter_Suc: "list2ts_alter (a#as) = tsLscons\<cdot> (updis a) \<cdot>(list2ts_alter as)"

(*Test tsRemDups*)
lemma "tsRemDups\<cdot>(<[Msg 1, Msg 1, Tick, Msg 1]>\<surd>) = <[Msg 1, Tick]>\<surd>"
  apply (simp add: tsremdups_insert)
  by (simp add: tsmlscons_lscons tsremdups_h_delayfun)

(*Tests tsProjFst*)
lemma "tsProjFst\<cdot>(<[Msg (1, 11), Msg (2, 12), Tick]>\<surd>) = <[Msg 1, Msg 2, Tick]>\<surd>"
  apply(simp add: tsProjFst_def)
  by (metis (mono_tags, lifting) delayfun_nbot tsmlscons_nbot tsprojfst_delayfun tsprojfst_insert 
  tsprojfst_mlscons tsprojfst_strict up_defined)

lemma "tsProjFst\<cdot>(<[Msg (1, 11), Msg (2, 12), Tick, Msg (100, 200)]>\<surd>) = <[Msg 1, Msg 2, Tick]>\<surd>"
  apply(simp add: tsProjFst_def)
  by (metis (mono_tags, lifting) delayfun_nbot tsmlscons_nbot tsprojfst_delayfun tsprojfst_insert 
  tsprojfst_mlscons tsprojfst_strict up_defined)  

(************************************************)
  subsection \<open>list2ts_alter\<close>    
(************************************************)
(*contains list2ts_alter def and some proofs to verify list2ts and list2ts_alter*)       
 
thm tslscons_bot2
    
    (* NIEEE: Abs_tstream (updis \<surd> && \<epsilon>) *)
lemma "list2tsM [Msg 1, Msg 2, Tick, Msg 3, Tick, Msg 4] = s"
  apply simp
  oops

lemma list2ts_empty [simp]: "list2ts_alter [] = \<bottom>"
  by simp

lemma list2ts_onetick: "list2ts_alter[\<surd>]= Abs_tstream (updis \<surd> && \<bottom>)"
  by (simp add: tslscons_insert espf2tspf_def)

lemma list2ts_onemsg[simp]:"a\<noteq>\<surd> \<Longrightarrow> list2ts_alter[a] =\<bottom> "
  by simp

lemma list2ts_tickfirst:"list2ts_alter (\<surd>#as) =(Abs_tstream(<[\<surd>]>)) \<bullet> list2ts_alter as"
  apply (simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  apply (subst lscons_conv)+
  by (simp add: tsconc_insert)

lemma list2ts_nottickfirst:"a\<noteq>\<surd> \<and> as=(b # \<surd> # bs) \<Longrightarrow>list2ts_alter (a#as) =Abs_tstream (\<up>a \<bullet> Rep_tstream (list2ts_alter as))"
  apply (simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  by (simp add: lscons_conv)

lemma tstickcount_lscons1: "t\<noteq>\<surd> \<Longrightarrow> #\<surd> tsLscons\<cdot>(updis t)\<cdot>ts = #\<surd> (ts)"
  apply (cases "ts=\<bottom>", simp)
  apply (subst tslscons2lscons,simp)
  apply (simp add: tslscons2lscons tstickcount_insert)
  by (metis lscons_conv sfilter_nin singletonD)

lemma tstickcount_lscons2: " #\<surd> tsLscons\<cdot>(updis \<surd>)\<cdot>ts = lnsuc\<cdot>(#\<surd> (ts))"
  apply (cases "ts=\<bottom>", simp)
  apply (metis DiscrTick_def delayFun_dropFirst delayfun_nbot delayfun_tslscons_bot strict_tstickcount
  tsdropfirst_len)
  apply (subst tslscons2lscons,simp)
  apply (simp add: tslscons2lscons tstickcount_insert)
  by (simp add: lscons_conv)


lemma "#\<surd> (list2ts_alter l) \<le> #\<surd> (list2ts_alter (a#l))"
  apply(cases "a=\<surd>",simp)
  apply (metis DiscrTick_def delayfun_insert delayfun_tslscons less_lnsuc tstickcount_tscons)
  by(simp add:tstickcount_lscons1)
  

lemma list2ts_nbot2[simp]:"list2ts_alter (a@[\<surd>])\<noteq>\<bottom>"
  by (induction a, simp+)

lemma list2ts_nbot1[simp]: "list2ts_alter (a@\<surd>#as)\<noteq>\<bottom>"
  by(induction a, simp+)

lemma list2ts_unfold1:"a\<noteq>\<surd> \<Longrightarrow>list2ts_alter (a # b @ [\<surd>]) =Abs_tstream (\<up>a \<bullet> Rep_tstream (list2ts_alter (b @ [\<surd>])))"
  apply (simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  by (simp add: lscons_conv)

lemma list2ts_droplist: "filter (\<lambda>e. e=\<surd>) as =[] \<Longrightarrow> list2ts_alter as = \<bottom>"
  apply (induction as, simp)
  apply (subgoal_tac "a\<noteq>\<surd>")
  apply (simp add: tslscons_insert)
  by auto

lemma list2ts_unfold2:"a \<noteq> \<surd> \<Longrightarrow> list2ts_alter (a # b @ \<surd> # bs) = Abs_tstream (\<up>a \<bullet> Rep_tstream (list2ts_alter (b @ \<surd> # bs)))"
  apply(induction bs)
  apply(subst list2ts_unfold1,auto)
  apply(simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  by (simp add: lscons_conv)

lemma list2ts_split:"list2ts_alter (a @ \<surd> # as) = (list2ts_alter (a @ [\<surd>])) \<bullet> (list2ts_alter as)"
  apply (induction a, simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  apply (simp add: lscons_conv tsconc_insert)
  apply (simp add: tslscons_insert, auto)
  by (simp add: espf2tspf_def lscons_conv tsconc_insert)+

lemma list2ts_dropend:"filter (\<lambda>e. e=\<surd>) as=[] \<Longrightarrow> list2ts_alter (a @ \<surd> # as) = list2ts_alter(a @ [\<surd>])"
  by(subst list2ts_split, simp add: list2ts_droplist)
  

lemma list2ts_lshd1 [simp]: "a\<noteq>[] \<Longrightarrow> tsLshd\<cdot>(list2ts_alter (a @ [\<surd>])) = updis (hd a)"
  apply(induction a,simp)
  by (metis append_Cons list.sel(1) list2ts_alter_Suc list2ts_nbot2 tslscons_lshd)

lemma list2ts_lshd_tick [simp]: "tsLshd\<cdot>(list2ts_alter (\<surd> # a)) = updis \<surd>"
  by simp

lemma list2ts_srt [simp]: "t\<noteq>\<bottom> \<Longrightarrow> tsRt\<cdot>(list2ts_alter (a # as)) = list2ts_alter (as)"
  by simp

lemma list2ts_lshd [simp]: "a\<noteq>[] \<Longrightarrow> tsLshd\<cdot>(list2ts_alter (a @ \<surd> # as)) = updis (hd a)"
  by(induction a, simp+)

lemma list2ts2list2s_lscons: "list2ts_alter (a # as @ [\<surd>]) = Abs_tstream (lscons\<cdot>(updis a)\<cdot>(list2s (as@[\<surd>])))"
  apply (induction as arbitrary: a, simp+)
  apply (auto simp add: tslscons_insert espf2tspf_def lscons_conv)
  apply (metis list2ts_nbot1 lscons_conv tslscons2lscons tslscons_nbot up_defined)
  apply (subst Rep_Abs)
  apply (auto simp add: ts_well_def)
  apply (simp add: less_le slen_lnsuc)
  apply (metis sconc_scons)
  apply (subst Rep_Abs)
  apply (auto simp add: ts_well_def)
  apply (simp add: less_le slen_lnsuc)
  by (metis sconc_scons)


lemma [simp]:" #({\<surd>} \<ominus> <ls>) \<noteq> \<infinity>"
apply (subgoal_tac "#(<ls>)\<noteq>\<infinity>")
using sfilterl4 apply blast
by simp

lemma list2ts2list2s_well[simp]:"ts_well (list2s ls) \<Longrightarrow> Rep_tstream (list2ts_alter ls) = list2s (ls)"
proof(induction ls)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ls)
  then show ?case
    apply simp 
    by (metis Abs_Rep Rep_Abs absts2tslscons lscons_conv stream.sel_rews(5) ts_well_drop1 up_defined)
qed

lemma list2s2list2ts_well[simp]:"ts_well (list2s ls) \<Longrightarrow>  Abs_tstream (list2s ls) = list2ts_alter (ls)"
proof(induction ls)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ls)
  then show ?case
    apply simp
    by (metis Abs_Rep Rep_Abs absts2tslscons lscons_conv stream.sel_rews(5) ts_well_drop1 up_defined)
qed

(*Test*)
lemma testlist2ts: "list2ts_alter ([\<M> True,\<M> False, \<surd>,\<M> False]) = Abs_tstream (<[Msg True,Msg False,\<surd>]>)"
  apply (simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  apply (subst lscons_conv)+
  by simp

(*Test*)
lemma testlist2tsM: "list2tsM ([\<M> True,\<M> False, \<surd>,\<M> False]) = tsMLscons\<cdot>(updis True)\<cdot>(tsMLscons\<cdot>(updis False)\<cdot>(delayFun\<cdot>\<bottom>))"
  by (simp add: tslscons_insert)

(*list2s*)
lemma list2s_sfoot_ntk:"b\<noteq>\<surd> \<Longrightarrow> sfoot (<(a@[b])>) \<noteq> \<surd> "
  apply(subst sfoot1, simp)
  by (simp add: less_le slen_lnsuc,simp)
  

lemma tswell_list:"ls \<noteq> [] \<Longrightarrow> last ls \<noteq>\<surd> \<Longrightarrow> \<not> ts_well (list2s ls)"
  apply (simp add: ts_well_def, auto)
  using list2s_inj apply fastforce
  by (metis append_butlast_last_id list2s_sfoot_ntk sfoot1)

lemma list2ts_tsntimes:"ts_well (list2s as) \<Longrightarrow>tsntimes n (list2ts_alter as) = tsntimes n (Abs_tstream (list2s as))"
  by simp


lemma list2ts_tsinftimes2: "tsinftimes (list2ts_alter (as@[\<surd>])) = tsinftimes (Abs_tstream (list2s (as@[\<surd>])))"
  apply (subst list2s2list2ts_well,auto)
  apply (simp add: ts_well_def, auto)
  by (simp add: less_le slen_lnsuc)
  
lemma list2ts_alter2list2tsM: "list2ts_alter l = list2tsM l"
proof(induction l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    apply (simp add: delayFun_def, auto)
    apply (metis DiscrTick_def delayfun_insert delayfun_tslscons)
    by (simp add: MsginvMsg tsmlscons2tslscons)
qed

(*Spezifikation tsfork*)

definition tsfork_fst::"bool event stream \<Rightarrow> 'a event stream \<Rightarrow> 'a event stream" where
"tsfork_fst \<equiv> fix\<cdot>(\<Lambda> h. (\<lambda> bs as. if (as = \<epsilon> \<or> bs=\<epsilon>) then \<epsilon> else ( if shd bs=\<surd> then (\<up>\<surd>) \<bullet> (h(srt\<cdot>bs)(srt\<cdot>as)) else
                        (if shd bs=\<M> True then (h (srt\<cdot>bs) (srt\<cdot>as)) else (\<up>(shd as) \<bullet> (h (srt\<cdot>bs) (srt\<cdot>as)))))))"

definition tsfork_snd::"bool event stream \<Rightarrow> 'a event stream \<Rightarrow> 'a event stream" where
"tsfork_snd \<equiv> fix\<cdot>(\<Lambda> h. (\<lambda> bs as. if (as = \<epsilon> \<or> bs =\<epsilon>) then \<epsilon> else( if shd bs=\<surd> then (\<up>\<surd>) \<bullet> (h(srt\<cdot>bs)(srt\<cdot>as)) else
                        (if shd bs=\<M> False then (h (srt\<cdot>bs) (srt\<cdot>as)) else (\<up>(shd as) \<bullet> (h (srt\<cdot>bs) (srt\<cdot>as)))))))"

definition tsfork::"bool tstream \<Rightarrow> 'a tstream \<Rightarrow> 'a tstream \<times> 'a tstream" where
"tsfork \<equiv> \<lambda> tbs tas. (Abs_tstream (tsfork_fst (Rep_tstream tbs)(Rep_tstream tas)),Abs_tstream(tsfork_snd (Rep_tstream tbs)(Rep_tstream tas)))"
  
  
  
(* Definition of tsum6 and verification with tsum5 *)

(* Compute sum of previous inputs and emit it *)
definition tsum6 :: "nat tstream \<rightarrow> nat tstream" where
"tsum6 \<equiv> tsscanl plus 0"

lemma tsum5_h_unfold_tick: "shd s=\<surd> \<and> s\<noteq>\<epsilon> \<Longrightarrow> tsum5_h q\<cdot>s = \<up>\<surd> \<bullet> tsum5_h q\<cdot>(srt\<cdot>s)"
by (metis surj_scons tsum5_h_scons_tick)

(* Nth element of tsum6 and tsum5 are equal *)
lemma tsum6_h2tsum5_h_snth: 
  "Fin n < #(tsscanl_h op + q\<cdot>s) \<longrightarrow> snth n (tsscanl_h op + q\<cdot>s) = snth n (tsum5_h q\<cdot>s)"
proof (induction n arbitrary: q s, auto)
  fix  n :: "nat" and q :: "nat" and s :: "nat event stream" and k :: "lnat"
  assume a1: "#s = lnsuc\<cdot>k"
  hence h1: "s \<noteq> \<epsilon>"
    using lnsuc_neq_0 strict_slen by auto
  thus "shd (tsscanl_h op + q\<cdot>s) = shd (tsum5_h q\<cdot>s)"
    apply (cases "shd s=\<surd>")
    apply (simp add: tsscanl_h_unfold_shd_tick tsum5_h_unfold_tick)
    by (simp add: tsscanl_h_unfold_shd)
next
  fix  n :: "nat" and q :: "nat" and s :: "nat event stream"
  assume a2: "\<And>q s. Fin n < #s \<longrightarrow> snth n (tsscanl_h op + q\<cdot>s) = snth n (tsum5_h q\<cdot>s)"
  assume a3: "Fin (Suc n) < #s"
  thus "snth (Suc n) (tsscanl_h op + q\<cdot>s) = snth (Suc n) (tsum5_h q\<cdot>s)"
  by (smt Suc_n_not_le_n a2 less2nat_lemma less_imp_not_eq2 lnle_Fin_0 not_less slen_empty_eq 
      slen_rt_ile_eq snth_scons surj_scons trans_lnless tsscanl_h_scons tsscanl_h_scons_tick 
      tsum5_suc_snth tsum5_suc_snth_tick)
qed

(* tsum6 equals tsum5 on event streams *)
lemma tsum6_h2tsum5_h: "tsscanl_h plus 0\<cdot>s = tsum5_h 0\<cdot>s"
apply (rule snths_eq)
apply (simp)
by (simp add: tsum6_h2tsum5_h_snth)

(* tsum6 equals tsum5 *)
lemma tsum62tsum5: "tsum6=tsum5"
by (simp add: tsscanl_def tsum5_def tsum6_def tsum6_h2tsum5_h)

(* Definition of ttimes and verification with ttimes_nth *)

(* Compute product of previous inputs and emit it *)
definition ttimes :: "nat tstream \<rightarrow> nat tstream" where
"ttimes \<equiv> tsscanl times 1"

(* Calculates the product of the nat stream elements until the nth element *)
primrec ttimes_nth:: "nat \<Rightarrow> nat event stream \<Rightarrow> nat" where
"ttimes_nth 0 s = (if shd s=\<surd> then 1 else 1 * \<M>\<inverse> shd s)" |
"ttimes_nth (Suc n) s = (if shd s=\<surd> then 1 * ttimes_nth n (srt\<cdot>s) 
                         else (\<M>\<inverse>(shd s)) * ttimes_nth n (srt\<cdot>s))"

(* Switch initial element for tsscanl_h times to one *)
lemma tsscanl_h_times_switch_initial:
  "Fin n<#(s :: nat event stream) \<and> snth n s\<noteq>\<surd> 
    \<Longrightarrow> snth n (tsscanl_h times q\<cdot>s) = \<M> q * \<M>\<inverse> snth n (tsscanl_h times 1\<cdot>s)"
proof (induction n arbitrary: q s, auto)
  fix q :: "nat" and s :: "nat event stream" and k :: "lnat"
  assume a1: "shd s \<noteq> \<surd>"
  assume a2: "#s = lnsuc\<cdot>k"
  hence h1: "s \<noteq> \<epsilon>"
    using lnsuc_neq_0_rev strict_slen by auto
  thus "shd (tsscanl_h op * q\<cdot>s) = \<M> q * \<M>\<inverse> shd (tsscanl_h op * 1\<cdot>s)"
    by (simp add: a1 tsscanl_h_unfold_shd)
next
  fix n :: "nat" and q :: "nat" and s :: "nat event stream"
  assume a3: "\<And>q s. Fin n < #(s :: nat event stream) \<and> snth n s \<noteq> \<surd> 
                \<Longrightarrow> snth n (tsscanl_h op * q\<cdot>s) = \<M> q * \<M>\<inverse> snth n (tsscanl_h op * 1\<cdot>s)"
  assume a4: "Fin (Suc n) < #s"
  assume a5: "snth (Suc n) s \<noteq> \<surd>"
  thus "snth (Suc n) (tsscanl_h op * q\<cdot>s) = \<M> q * \<M>\<inverse> snth (Suc n) (tsscanl_h op * 1\<cdot>s)"
    by (smt Suc_neq_Zero a3 a4 event.simps(4) less_imp_not_eq2 lnle_Fin_0 mult.assoc 
        mult.comm_neutral not_less slen_rt_ile_eq snth_scons strict_slen surj_scons trans_lnless
        tsscanl_h_scons tsscanl_h_scons_tick)  
qed

(* Nth element of tsscanl_h times is equal to ttimes_nth *)
lemma tsscanl_h2ttimes_nth_snth: 
  "Fin n<#s \<and> snth n s\<noteq>\<surd> \<Longrightarrow> snth n (tsscanl_h times 1\<cdot>s) = \<M> ttimes_nth n s"
proof (induction n arbitrary: s, auto)
  fix s :: "nat event stream" and k :: "lnat"
  assume a1: "shd s \<noteq> \<surd>"
  assume a2: "#s = lnsuc\<cdot>k"
  hence h1: "s \<noteq> \<epsilon>"
    using bot_is_0 lnat.con_rews strict_slen by auto
  thus "shd (tsscanl_h op * 1\<cdot>s) = \<M> \<M>\<inverse> shd s"
    by (simp add: a1 h1 tsscanl_h_unfold_shd)
next  
  fix n :: "nat" and s :: "nat event stream"
  assume a3: "\<And>s. Fin n < #s \<and> snth n s \<noteq> \<surd> \<Longrightarrow> snth n (tsscanl_h op * 1\<cdot>s) = \<M> ttimes_nth n s"
  assume a4: "Fin (Suc n) < #s"
  assume a5: "snth (Suc n) s \<noteq> \<surd>"
  thus "shd s = \<surd> \<Longrightarrow> snth (Suc n) (tsscanl_h op * 1\<cdot>s) = \<M> ttimes_nth n (srt\<cdot>s)"
    by (metis a3 a4 not_less slen_rt_ile_eq snth_rt tsscanl_h_unfold_srt_tick)
  thus "shd s \<noteq> \<surd> \<Longrightarrow> snth (Suc n) (tsscanl_h op * 1\<cdot>s) = \<M> \<M>\<inverse> shd s * ttimes_nth n (srt\<cdot>s)"
    by (smt a3 a4 a5 event.simps(4) mult.left_neutral not_less slen_rt_ile_eq snth_rt 
        tsscanl_h_times_switch_initial tsscanl_h_unfold_srt)
qed

(* Nth element of tsscanl_h times is equal to ttimes_nth otherwise tick *)
lemma tsscanl_h2ttimes_nth: "Fin n<#s \<Longrightarrow> 
  snth n (tsscanl_h times 1\<cdot>s) = (case (snth n s) of Msg a \<Rightarrow> \<M> ttimes_nth n s | \<surd> \<Rightarrow> \<surd>)"
apply (cases "snth n s =\<surd>", simp add: tsscanl_h_snth_tick2tick)
by (metis event.exhaust event.simps(4) tsscanl_h2ttimes_nth_snth)

(* Nth element of ttimes is equal to ttimes_nth otherwise tick *)
lemma ttimes2ttimes_nth: 
  "Fin n<#(Rep_tstream ts) \<Longrightarrow> snth n (Rep_tstream (ttimes\<cdot>ts)) =
      (case (snth n (Rep_tstream ts)) of Msg a \<Rightarrow> \<M> ttimes_nth n (Rep_tstream ts) | \<surd> \<Rightarrow> \<surd>)"
by (simp add: ttimes_def tsscanl_unfold ts_well_tsscanl_h tsscanl_h2ttimes_nth)

(* Verification of tsscanl with tsscanl_nth under assumptions
   f associative operator and q neutral element of f *)

(* Calculates like scanl the event stream elements until the nth element *)
primrec tsscanl_nth :: "nat \<Rightarrow> ('a \<Rightarrow> 'a  \<Rightarrow> 'a) \<Rightarrow> 'a  \<Rightarrow> 'a event stream \<Rightarrow> 'a" where
"tsscanl_nth 0 f q s = (if shd s=\<surd> then q else f q (\<M>\<inverse> shd s))" |
"tsscanl_nth (Suc n) f q s = (if shd s=\<surd> then f q (tsscanl_nth n f q (srt\<cdot>s))
                              else f (\<M>\<inverse> shd s) (tsscanl_nth n f q (srt\<cdot>s)))"

(* Switch initial element for tsscanl_h to neutral element auxiliary function *)
lemma tsscanl_h_switch_initial_h:
  "Fin n<#s \<and> snth n s\<noteq>\<surd> \<and> (\<forall>a. f q a=a) \<and> (\<forall>a b c. f (f a b) c = f a (f b c))
    \<Longrightarrow> \<M> f p \<M>\<inverse> snth n (tsscanl_h f r\<cdot>s)  = \<M> f (f p r) \<M>\<inverse> snth n (tsscanl_h f q\<cdot>s)"
proof (induction n arbitrary: p q r s, auto)
  fix p :: "'a" and q :: "'a" and r :: "'a" and s :: "'a event stream" and k :: "lnat"
  assume a1: "#s = lnsuc\<cdot>k"
  hence h1: "s \<noteq> \<epsilon>"
    using lnsuc_neq_0_rev strict_slen by auto
  assume a2: "shd s \<noteq> \<surd>"
  assume a3: "\<forall>a. f q a = a"
  assume a4: "\<forall>a b c. f (f a b) c = f a (f b c)"
  thus "f p \<M>\<inverse> shd (tsscanl_h f r\<cdot>s) = f p (f r \<M>\<inverse> shd (tsscanl_h f q\<cdot>s))"
    by (simp add: a2 a3 h1 tsscanl_h_unfold_shd)
next
  fix n :: "nat" and p :: "'a" and  q :: "'a" and r :: "'a" and s :: "'a event stream"
  assume a5: "\<And>p q r s. Fin n < #s \<and> snth n s \<noteq> \<surd> \<and> (\<forall>a. f q a = a) 
                \<Longrightarrow> f p \<M>\<inverse> snth n (tsscanl_h f r\<cdot>s) = f p (f r \<M>\<inverse> snth n (tsscanl_h f q\<cdot>s))"
  assume a6: "Fin (Suc n) < #s"
  hence h2: "Fin n < #(srt\<cdot>s)"
    by (meson not_less slen_rt_ile_eq)
  assume a7: "snth (Suc n) s \<noteq> \<surd>"
  hence h3: "snth n (srt\<cdot>s) \<noteq> \<surd>"
    by (simp add: snth_rt)
  assume a8: "\<forall>a. f q a = a"
  assume a9: "\<forall>a b c. f (f a b) c = f a (f b c)"
  thus "f p \<M>\<inverse> snth (Suc n) (tsscanl_h f r\<cdot>s) = f p (f r \<M>\<inverse> snth (Suc n) (tsscanl_h f q\<cdot>s))"
    apply (cases "shd s=\<surd>")
    apply (metis (no_types, lifting) a5 a6 a7 a8 not_less slen_rt_ile_eq snth_rt 
           tsscanl_h_unfold_srt_tick)
    apply (simp add: snth_rt tsscanl_h_unfold_srt)
    by (metis (no_types, lifting) a5 a8 h2 h3)
qed

(* Switch initial element for tsscanl_h to neutral element *)
lemma tsscanl_h_switch_initial:
  "Fin n<#s \<and> snth n s\<noteq>\<surd> \<and> (\<forall>a. f q a=a) \<and> (\<forall>a b c. f (f a b) c = f a (f b c))
    \<Longrightarrow> snth n (tsscanl_h f p\<cdot>s) = \<M> f p \<M>\<inverse> snth n (tsscanl_h f q\<cdot>s)"
proof (induction n arbitrary: p q s, auto)
  fix p :: "'a" and q :: "'a" and s :: "'a event stream" and k :: "lnat"
  assume a1: "#s = lnsuc\<cdot>k"
  hence h1: "s \<noteq> \<epsilon>"
    using lnsuc_neq_0_rev strict_slen by auto
  assume a2: "shd s \<noteq> \<surd>"
  assume a3: "\<forall>a. f q a = a"
  assume a4: "\<forall>a b c. f (f a b) c = f a (f b c)"
  thus "shd (tsscanl_h f p\<cdot>s) = \<M> f p \<M>\<inverse> shd (tsscanl_h f q\<cdot>s)"
    by (simp add: a2 a3 h1 tsscanl_h_unfold_shd)
next
  fix n :: "nat" and p :: "'a" and  q :: "'a" and s :: "'a event stream"
  assume a5: "\<And>p q s. Fin n < #s \<and> snth n s \<noteq> \<surd> \<and> (\<forall>a. f q a = a)
                \<Longrightarrow> snth n (tsscanl_h f p\<cdot>s) = \<M> f p \<M>\<inverse> snth n (tsscanl_h f q\<cdot>s)"
  assume a6: "Fin (Suc n) < #s"
  assume a7: "snth (Suc n) s \<noteq> \<surd>"
  assume a8: "\<forall>a. f q a = a"
  assume a9: "\<forall>a b c. f (f a b) c = f a (f b c)"
  thus "snth (Suc n) (tsscanl_h f p\<cdot>s) = \<M> f p \<M>\<inverse> snth (Suc n) (tsscanl_h f q\<cdot>s)"
    apply (cases "shd s=\<surd>")
    apply (metis (no_types, lifting) a5 a6 a7 a8 convert_inductive_asm not_less slen_rt_ile_eq 
           snth_rt tsscanl_h_snth_tick)
    apply (simp add: snth_rt tsscanl_h_unfold_srt)
    apply (insert tsscanl_h_switch_initial_h [of n "srt\<cdot>s" f q p "f q \<M>\<inverse> shd s"])
    by (metis a5 a6 a7 a8 not_less slen_rt_ile_eq snth_rt)
qed

(* Nth element of tsscanl_h is equal to tsscanl_nth *)
lemma tsscanl_h2tsscanl_nth_snth: 
  "Fin n<#s \<and> snth n s\<noteq>\<surd> \<and> (\<forall>a. f q a=a) \<and> (\<forall>a b c. f (f a b) c = f a (f b c))
     \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth n f q s"
proof (induction n arbitrary: q s, auto)
  fix q :: "'a" and s :: "'a event stream" and k :: "lnat"
  assume a1: "#s = lnsuc\<cdot>k"
  assume a2: "shd s \<noteq> \<surd>"
  assume a3: "\<forall>a. f q a = a"
  assume a4: "\<forall>a b c. f (f a b) c = f a (f b c)"
  thus "shd (tsscanl_h f q\<cdot>s) = \<M> \<M>\<inverse> shd s"
    by (metis a1 a2 a3 lnsuc_neq_0 slen_empty_eq tsscanl_h_unfold_shd)
next  
  fix n :: "nat" and  q :: "'a" and s :: "'a event stream"
  assume a4: "\<And>q s. Fin n < #s \<and> snth n s \<noteq> \<surd> \<and> (\<forall>a. f q a = a) 
                \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth n f q s"
  assume a5: "Fin (Suc n) < #s"
  assume a6: "snth (Suc n) s \<noteq> \<surd>"
  assume a7: "\<forall>a. f q a = a"
  assume a8: "\<forall>a b c. f (f a b) c = f a (f b c)"
  thus "shd s = \<surd> \<Longrightarrow> snth (Suc n) (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth n f q (srt\<cdot>s)"
    by (metis (no_types, lifting) a4 a5 a6 a7 convert_inductive_asm not_less slen_rt_ile_eq snth_rt
        tsscanl_h_snth_tick)
  thus "shd s \<noteq> \<surd> \<Longrightarrow> snth (Suc n) (tsscanl_h f q\<cdot>s) = \<M> f \<M>\<inverse> shd s (tsscanl_nth n f q (srt\<cdot>s))"
    apply (simp add: snth_rt tsscanl_h_unfold_srt a7)
    apply (insert tsscanl_h_switch_initial [of n "srt\<cdot>s" f q "\<M>\<inverse> shd s"])
    by (metis (no_types, lifting) a4 a5 a6 a7 a8 event.simps(4) not_less slen_rt_ile_eq snth_rt)
qed

(* Nth element of tsscanl_h is equal to tsscanl_nth otherwise tick *)
lemma tsscanl_h2tsscanl_nth: 
  "Fin n<#s \<and> (\<forall>a. f q a=a) \<and> (\<forall>a b c. f (f a b) c = f a (f b c)) 
     \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) = (case (snth n s) of Msg a \<Rightarrow> \<M> tsscanl_nth n f q s | \<surd> \<Rightarrow> \<surd>)"
apply (cases "snth n s=\<surd>", simp add: tsscanl_h_snth_tick2tick)
by (metis event.exhaust event.simps(4) tsscanl_h2tsscanl_nth_snth)

(* Nth element of tsscanl is equal to tsscanl_nth otherwise tick *)
lemma tsscanl2tsscanl_nth:
  "Fin n<#(Rep_tstream ts) \<and> (\<forall>a. f q a=a) \<and> (\<forall>a b c. f (f a b) c = f a (f b c))
     \<Longrightarrow> snth n (Rep_tstream (tsscanl f q\<cdot>ts)) =
       (case (snth n (Rep_tstream ts)) of Msg a \<Rightarrow> \<M> tsscanl_nth n f q (Rep_tstream ts) | \<surd> \<Rightarrow> \<surd>)"
by (simp add: tsscanl_unfold ts_well_tsscanl_h tsscanl_h2tsscanl_nth)





definition sMerge :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
"sMerge \<equiv> \<mu> h. (\<lambda> n s1 s2. if (s1=\<bottom>\<or>s2=\<bottom>) then s1\<bullet>s2 else (if (n mod 2 = 1) then (lshd\<cdot>s1 && h (n div 2) (srt\<cdot>s1) s2) 
  else (lshd\<cdot>s2 && h (n div 2) s1 (srt\<cdot>s2))))"

lemma "monofun (\<lambda> h n s1 s2. (if (n mod 2 = 1 \<and> s1\<noteq>\<bottom>) then (lshd\<cdot>s1 && h (n div 2) (srt\<cdot>s1) s2) 
  else (lshd\<cdot>s2 && h (n div 2) s1 (srt\<cdot>s2))))"
  apply(rule monofunI)
  apply(rule fun_belowI, rule fun_belowI, rule fun_belowI)
  apply auto
    apply (simp add: fun_below_iff)
   apply(rule monofun_cfun_arg)
   apply (simp add: fun_below_iff)
  apply(rule monofun_cfun_arg)
  apply (simp add: fun_below_iff)
done

lemma [simp]: "cont (\<lambda> h n s1 s2. (if ((s1=\<epsilon>)\<or>(s2=\<epsilon>)) then (s1 \<bullet> s2) else (if (n mod 2 = 1) then (lshd\<cdot>s1 && h (n div 2) (srt\<cdot>s1) s2) 
  else (lshd\<cdot>s2 && h (n div 2) s1 (srt\<cdot>s2)))))"
sorry

lemma s_merge_unfold1: assumes "n mod 2 = 1" and  "s1\<noteq>\<bottom>" and  "s2\<noteq>\<bottom>"
  shows "sMerge n s1 s2 = lshd\<cdot>s1 && sMerge (n div 2) (srt\<cdot>s1) s2"
apply(subst sMerge_def [THEN fix_eq2])
by (simp add: assms)

lemma s_merge_unfold0: assumes "n mod 2 = 0" and "s1\<noteq>\<bottom>" and  "s2\<noteq>\<bottom>"
  shows "sMerge n s1 s2 = lshd\<cdot>s2 && sMerge (n div 2) s1 (srt\<cdot>s2)"
apply(subst sMerge_def [THEN fix_eq2])
by (simp add: assms)

lemma smerge_eps [simp]: "sMerge n \<epsilon> \<epsilon> = \<epsilon>"
apply(subst sMerge_def [THEN fix_eq2])
by simp

lemma smerge_eps1[simp]: "sMerge n \<epsilon> s = s"
apply(subst sMerge_def [THEN fix_eq2])
by simp

lemma smerge_eps2[simp]: "sMerge n s \<epsilon> = s"
apply(subst sMerge_def [THEN fix_eq2])
by simp

lemma lsconc_suc: "#(u&&s) = Fin (Suc n) \<Longrightarrow> #s = Fin n"
by (metis Fin_Suc Zero_not_Suc fun_approxl2 lnat.sel_rews(2) lnle_Fin_0 refl_lnle slen_scons stream.con_rews(2) stream.sel_rews(5) strict_slen surj_scons)

lemma lsconc_suc2: "#s = Fin n \<Longrightarrow> u\<noteq>\<bottom> \<Longrightarrow> #(u&&s) = Fin (Suc n)"
  apply(induction s arbitrary: u)
    apply(rule admI)
    apply auto
    using inf_chainl4 l42 apply force
   apply (metis Fin_02bot Fin_Suc lnzero_def slen_scons stream.con_rews(2) stream.sel_rews(5) strict_slen surj_scons)
  by (metis Fin_Suc slen_scons stream.con_rews(2) stream.sel_rews(5) surj_scons)

lemma assumes "#s1 = Fin n1" and "#s2 = Fin n2" and "s1\<noteq>\<bottom>" and  "s2\<noteq>\<bottom>"
  shows "#(sMerge n s1 s2) = Fin (n1+n2)"
using assms apply (induction s1 arbitrary: n1 n2 s2 n)
apply(rule admI)
apply(case_tac "finite_chain Y")
using l42 apply force
apply (simp add: inf_chainl4)
apply auto[1]
apply(case_tac "n mod 2 = 1")
apply (simp add: s_merge_unfold1)

oops
(*
apply (metis Fin_0 Zero_not_Suc lsconc_suc2 stream.con_rews(2) strict_slen)
apply(simp add: add: s_merge_unfold0)
by (metis bot_is_0 lnle_Fin_0 lsconc_suc2 nat.simps(3) refl_lnle stream.con_rews(2) strict_slen)
*)


(*
definition tMerge:: "bool stream \<Rightarrow> 'a tstream \<Rightarrow> 'a tstream \<Rightarrow> 'a tstream" where
"tMerge  \<equiv> \<mu> h. (\<lambda> oracle ts1 ts2.
  if (oracle=\<bottom>) then \<bottom> else if(shd oracle \<and> ts1\<noteq>\<bottom>) then tsTakeFirst\<cdot>ts1 \<bullet> (h (srt\<cdot>oracle) tsDropFirstts1 ts2)
  else tsTakeFirst\<cdot>ts2 \<bullet> (h (srt\<cdot>oracle) ts1 (tsDropFirst\<cdot>ts2)))"
*)

end





