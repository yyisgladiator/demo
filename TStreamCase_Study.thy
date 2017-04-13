(*  Title:        TStreamCase_Study.thy
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Tests with tStreams, mostly a few function definitions
                  and definition of Strong/Weak Causality on TStream functions
*)

chapter {* Timed Streams *} 

theory TStreamCase_Study

imports TStream Tsum5_HK
begin
default_sort countable

(* Examples for weak causal functions *)

(* tsTake on tstreams with only ticks *)
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

(* Identity function on tstreams is monotone, continous and weak causal *)
definition tsident :: "'a tstream \<Rightarrow> 'a tstream" where
"tsident ts \<equiv> ts"

lemma mono_tsident: "monofun tsident"
by (simp add: monofunI tsident_def)

lemma cont_tsident: "cont tsident"
by (metis mono_tsident tsMono2weak2cont tsident_def)

lemma tsweak_tsident:"tsWeakCausal tsident"
by (simp add: tsident_def tsWeakCausalI)

(* Identity function on tstreams is not strong causal
   <\<surd>> \<down> 1 = <\<surd>, \<surd>> \<down> 1 but <\<surd>> \<down> 2 \<noteq> <\<surd>, \<surd>> \<down> 2 *)
lemma non_tsstrong_tsident:"\<not>tsStrongCausal tsident"
apply (simp add: tsident_def tsStrongCausal_def)
apply (rule_tac x=1 in exI)
apply (rule_tac x="Abs_tstream (\<up>\<surd>)" in exI)
apply (rule_tac x="Abs_tstream (<[\<surd>, \<surd>]>)" in exI)
by (metis (no_types, lifting) Rep_Abs Suc_1 list2s_0 list2s_Suc list2s_inj lscons_conv
    not_Cons_self2 sup'_def tick_msg ts_well_sing_conc tstake1of1tick tstake1of2tick
    tstake2of1tick tstake2of2tick)

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

(* Constructed non weak causal function on tstreams is monotone and continous *)
definition tsnontsweak :: "'a tstream \<Rightarrow> 'a tstream" where
"tsnontsweak ts \<equiv> Abs_tstream (srt\<cdot>(Rep_tstream ts))"

lemma mono_tsnontsweak: "monofun tsnontsweak"
by (simp add: monofun_def tsnontsweak_def below_tstream_def monofun_cfun_arg)

(* cont g \<and> \<forall>x. ts_well (g x) \<Longrightarrow> cont (\<lambda>x. Abs_tstream (g x)) *)
lemma cont_tsnontsweak: "cont tsnontsweak"
apply (rule contI2)
apply (simp add: mono_tsnontsweak)
apply (simp add: tsnontsweak_def cont2contlubE)
by (smt Rep_Abs below_tstream_def lub_eq lub_tstream monofun_cfun_arg not_below2not_eq
    po_class.chain_def ts_well_Rep ts_well_drop1)

(* <\<surd>, \<surd>> \<down> 1 = <\<surd>> \<down> 1 but <\<surd>> \<down> 1 \<noteq> \<bottom> \<down> 1 *)
lemma non_tsweak_tsnontsweak: "\<not>tsWeakCausal tsnontsweak"
apply (simp add: tsWeakCausal_def tsnontsweak_def)
apply (rule_tac x=1 in exI)
apply (rule_tac x="Abs_tstream (\<up>\<surd>)" in exI)
apply (rule_tac x="Abs_tstream (<[\<surd>, \<surd>]>)" in exI)
by (metis (no_types, lifting) Abs_tstream_strict Rep_Abs Rep_tstream_strict list.distinct(1)
    list2s.simps(2) list2s_0 list2s_inj lscons_conv stream.con_rews(2) stream.sel_rews(5) strictI 
    sup'_def tick_msg tsDropTake1 tsTakeDrop ts_well_sing_conc tstake1of1tick tstake1of2tick)

(* Constructed non weak causal function on tstreams is not strong causal *)
lemma non_tsstrong_tsnontsweak: "\<not>tsStrongCausal tsnontsweak"
using non_tsweak_tsnontsweak tsStrong2Weak by auto

(* Constructed non continous function on tstreams is not weak causal but monotone *)
definition tsnoncont :: "'a tstream \<Rightarrow> 'a tstream" where
"tsnoncont ts \<equiv> if #(Rep_tstream ts)<\<infinity> then Abs_tstream (\<up>\<surd>) else Abs_tstream (<[\<surd>, \<surd>]>)"

lemma tsnoncont_inftick:
  "tsnoncont (tsinftimes (Abs_tstream (\<up>\<surd>))) = Abs_tstream (<[\<surd>, \<surd>]>)"
apply (simp add: tsnoncont_def)
by (metis ln_less lnless_def slen_scons tick_msg tsconc_rep_eq tsinftimes_unfold)

lemma not_below_2tick_tick: "Abs_tstream (\<up>\<surd> \<bullet> \<up>\<surd>) \<notsqsubseteq> Abs_tstream (\<up>\<surd>)"
by (smt Rep_Abs Rep_tstream_inject list2s.simps(1) list2s.simps(2) list2s_inj lscons_conv 
    not_Cons_self po_eq_conv sup'_def tick_msg ts_tsconc_prefix ts_well_conc1 tsconc_rep_eq1)

lemma tsnoncont_tick_is_ub: 
  "range (\<lambda>i. tsnoncont tsinftimes (Abs_tstream (\<up>\<surd>)) \<down> i ) <| Abs_tstream (\<up>\<surd>)"
by (simp add: is_ub_def tsnoncont_def tstakenofinftick)

lemma mono_tsnoncont: "monofun tsnoncont"
apply (rule monofunI)
apply (simp add: tsnoncont_def below_tstream_def, auto)
by (metis inf_ub lnle_def lnless_def mono_fst_infD)

(* Y = Take i <\<surd>, ...>
   \<Longrightarrow> range (\<lambda>i. tsnoncont (Y i)) <<| <\<surd>> \<noteq> tsnoncont (Lub Y = <\<surd>, ...>) =  <\<surd>, \<surd>> *)
lemma non_cont_tsnoncont: "\<not>cont tsnoncont"
apply (simp add: cont_def)
apply (rule_tac x="(\<lambda>i. (tsinftimes (Abs_tstream (\<up>\<surd>))) \<down> i )" in exI)
apply (simp add: tsnoncont_inftick is_lub_def, auto)
apply (rule_tac x="Abs_tstream (\<up>\<surd>)" in exI)
by (simp add: not_below_2tick_tick tsnoncont_tick_is_ub)

(* <\<surd>, \<surd>> \<down> 2 = <\<surd>, ...> \<down> 2 but <\<surd>> \<down> 2 \<noteq> <\<surd>, \<surd>> \<down> 2 *)
lemma non_tsweak_tsnoncont: "\<not>tsWeakCausal tsnoncont"
apply (simp add: tsWeakCausal_def)
apply (rule_tac x=2 in exI)
apply (rule_tac x="tsinftimes (Abs_tstream (\<up>\<surd>))" in exI)
apply (rule_tac x="Abs_tstream (<[\<surd>, \<surd>]>)" in exI)
by (smt Fin_02bot Fin_Suc Rep_Abs leI less_le list2s.simps(2) list2s_0 ln_less lnzero_def
    lscons_conv notinfI3 slen_scons strict_slen sup'_def tick_msg ts_well_sing_conc tsconc_rep_eq
    tsinftimes_unfold tsnoncont_def tstake2of1tick tstake2of2tick tstake2ofinftick)

(* Constructed non continous function on tstreams is not strong causal *)
lemma non_tsstrong_tsnoncont: "\<not>tsStrongCausal tsnoncont"
using non_tsweak_tsnoncont tsStrong2Weak by auto

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





