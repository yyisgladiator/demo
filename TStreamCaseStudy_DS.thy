(* 
    Title:  TStreamCaseStudy_DS.thy
    Author: Dennis Slotboom
    e-mail: dennis.slotboom@rwth-aachen.de

    Description: Definitons and lemmas for tsum6, ttimes and tsscanl
*)

theory TStreamCaseStudy_DS
imports TStream
begin

primrec sscanl_nth :: "nat \<Rightarrow> ('a \<Rightarrow> 'a  \<Rightarrow> 'a) \<Rightarrow> 'a  \<Rightarrow> 'a stream \<Rightarrow> 'a" where
"sscanl_nth 0 f q s =  f q (shd s)" |
"sscanl_nth (Suc n) f q s = f (shd s) (sscanl_nth n f q (srt\<cdot>s))"

lemma h1: "s\<noteq>\<epsilon> \<Longrightarrow> shd (sscanl f (f q a)\<cdot>s) = f a (shd (sscanl f q\<cdot>s))"
apply (simp add: sscanl_shd)
oops

lemma sscanl_snth2: "Fin n<#s \<Longrightarrow> snth (Suc n) (sscanl f q\<cdot>(\<up>a\<bullet>s)) = f a (snth n (sscanl f q\<cdot>s))"
apply (induction n arbitrary: f q a s)
apply (simp add: snth_rt)
oops

(* Nth element of sscanl is equal to sscanl_nth *)
lemma sscanl2sscanl_nth:
  "Fin n<#s \<Longrightarrow> snth n (sscanl f q\<cdot>s) = sscanl_nth n f q s"
proof (induction n arbitrary: q s, auto)
  fix q :: "'a" and s :: "'a stream" and k :: "lnat"
  assume a1: "#s = lnsuc\<cdot>k"
  hence h1: "s \<noteq> \<epsilon>"
    using lnsuc_neq_0_rev strict_slen by auto
  thus "shd (sscanl f q\<cdot>s) = f q (shd s)"
    by (simp add: sscanl_shd)
next
  fix n :: "nat" and  q :: "'a" and s :: "'a stream"
  assume a2: "\<And>q s. Fin n < #s \<Longrightarrow> snth n (sscanl f q\<cdot>s) = sscanl_nth n f q s"
  assume a3: "Fin (Suc n) < #s"
  thus "snth (Suc n) (sscanl f q\<cdot>s) = f (shd s) (sscanl_nth n f q (srt\<cdot>s))"
    sorry
(*
    by (metis Suc_neq_Zero a2 less_le lnle_Fin_0 not_less slen_rt_ile_eq sscanl_snth2 strict_slen
        surj_scons)
*)
qed

(* Verification of tsscanl with tsscanl_nth without assumptions *)

(* Calculates like scanl the event stream elements until the nth element *)
primrec tsscanl_nth :: "nat \<Rightarrow> ('a \<Rightarrow> 'a  \<Rightarrow> 'a) \<Rightarrow> 'a  \<Rightarrow> 'a event stream \<Rightarrow> 'a" where
"tsscanl_nth 0 f q s = (if shd s=\<surd> then q else f q (\<M>\<inverse> shd s))" |
"tsscanl_nth (Suc n) f q s = (if shd s=\<surd> then tsscanl_nth n f q (srt\<cdot>s)
                              else f (\<M>\<inverse> shd s) (tsscanl_nth n f q (srt\<cdot>s)))"

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

(* Constructed non continous function on tstreams is not weak causal but monotone *)
definition tsnoncont :: "'a tstream \<Rightarrow> 'a tstream" where
"tsnoncont ts \<equiv> if #(Rep_tstream ts)<\<infinity> then Abs_tstream (\<up>\<surd>)
                else Abs_tstream (<[\<surd>, \<surd>]>)"

lemma tstake2ofinftick: "(tsinftimes (Abs_tstream (\<up>\<surd>))) \<down> 2 = Abs_tstream (<[\<surd>, \<surd>]>)"
by (smt One_nat_def Rep_Abs Rep_cfun_strict1 Suc_1 list2s.simps(2) list2s_0 lscons_conv sup'_def 
    tick_msg tsDropTake1 tsTake.simps(1) tsTakeDrop tsconc_assoc tsconc_insert tsinftimes_unfold
    tstake2of2tick tstake_tick)

lemma mono_tsnoncont: "monofun tsnoncont"
apply (rule monofunI)
apply (simp add: tsnoncont_def below_tstream_def, auto)
by (metis inf_ub lnle_def lnless_def mono_fst_infD)

lemma non_cont_tsnoncont: "\<not>cont tsnoncont"
apply (simp add: cont_def)
apply (rule_tac x="(\<lambda>i. tsntimes i (Abs_tstream (\<up>\<surd>)))" in exI)
apply (simp add: tsnoncont_def)
sorry

(* <\<surd>, \<surd>> \<down> 2 = <\<surd>, ...> \<down> 2 but <\<surd>> \<down> 2 \<noteq> <\<surd>, \<surd>> \<down> 2 *)
lemma non_tsweak_tsnoncont: "\<not>tsWeakCausal tsnoncont"
apply (simp add: tsWeakCausal_def)
apply (rule_tac x=2 in exI)
apply (rule_tac x="tsinftimes (Abs_tstream (\<up>\<surd>))" in exI)
apply (rule_tac x="Abs_tstream (<[\<surd>, \<surd>]>)" in exI)
by (smt Fin_02bot Fin_Suc Rep_Abs leI less_le list2s.simps(2) list2s_0 ln_less lnzero_def
    lscons_conv notinfI3 slen_scons strict_slen sup'_def tick_msg ts_well_sing_conc tsconc_rep_eq
    tsinftimes_unfold tsnoncont_def tstake2of1tick tstake2of2tick tstake2ofinftick)

end