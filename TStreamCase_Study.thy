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
apply (auto)
by (metis One_nat_def Rep_Abs Rep_tstream_strict list2s.simps(1) list2s.simps(2) list2s_inj
    not_Cons_self2 sup'_def tick_msg tstake1of1tick)

(* Examples for weak causal function type *)

definition f1_spfw :: "'a \<leadsto>w 'a" where
"f1_spfw \<equiv> \<L> ts. if ts=\<bottom> then Abs_tstream (\<up>\<surd>) else \<bottom>"

lemma tsweak_f1_spfw: "tsWeakCausal (\<lambda>ts. if ts = \<bottom> then Abs_tstream (\<up>\<surd>) else \<bottom>)"
apply (rule tsWeakCausalI)
apply (simp add: f1_spfw_def, auto)
using tstakeBot by blast+

lemma non_mono_f1_spfw: "\<not>monofun (Rep_spfw (f1_spfw))"
apply (simp add: monofun_def f1_spfw_def)
by (simp add: Abs_spfw_inverse2 tsweak_f1_spfw)

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





