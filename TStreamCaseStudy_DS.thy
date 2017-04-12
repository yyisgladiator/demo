(* 
    Title:  TStreamCaseStudy_DS.thy
    Author: Dennis Slotboom
    e-mail: dennis.slotboom@rwth-aachen.de

    Description: Definitons and lemmas for tsum6, ttimes and tsscanl
*)

theory TStreamCaseStudy_DS
imports TStream
begin

(* tsTake is cont, tsTake is chain *)
lemma adm_spfw: "adm (\<lambda>x. x \<in> spfw)"
apply (simp only: spfw_def tsWeakCausal_def adm_def mem_Collect_eq)
by (metis (mono_tags, lifting) ch2ch_fun contlub_cfun_arg lub_eq lub_fun)

(* Verification of sscanl with sscanl_nth *)
primrec sscanl_nth :: "nat \<Rightarrow> ('a \<Rightarrow> 'a  \<Rightarrow> 'a) \<Rightarrow> 'a  \<Rightarrow> 'a stream \<Rightarrow> 'a" where
"sscanl_nth 0 f q s =  f q (shd s)" |
"sscanl_nth (Suc n) f q s = f (shd s) (sscanl_nth n f q (srt\<cdot>s))"

lemma sscanl_snth2: "Fin n<#s \<Longrightarrow> snth (Suc n) (sscanl f q\<cdot>(\<up>a\<bullet>s)) = f a (snth n (sscanl f q\<cdot>s))"
proof (induction n arbitrary: q a s, auto)
  fix q :: "'a" and a :: "'a" and s :: "'a stream" and k :: "lnat"
  assume a1: "#s = lnsuc\<cdot>k"
  hence h1: "s \<noteq> \<epsilon>"
    using lnsuc_neq_0 strict_slen by auto
  thus "shd (sscanl f (f q a)\<cdot>s) = f a (shd (sscanl f q\<cdot>s))"
    apply (simp add: sscanl_shd)
    sorry
next
  fix n :: "nat" and q :: "'a" and a :: "'a" and s :: "'a stream"
  assume a2: "\<And>q a s. Fin n < #s \<Longrightarrow> snth n (sscanl f (f q a)\<cdot>s) = f a (snth n (sscanl f q\<cdot>s))"
  assume a3: "Fin (Suc n) < #s"
  hence h2: "Fin n < #s"
    using convert_inductive_asm by auto
  thus "snth (Suc n) (sscanl f (f q a)\<cdot>s) = f a (snth (Suc n) (sscanl f q\<cdot>s))"
    apply (simp add: a2 a3 sscanl_snth)
    sorry
qed

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
    by (metis Suc_neq_Zero a2 less_le lnle_Fin_0 not_less slen_rt_ile_eq sscanl_snth2 strict_slen
        surj_scons)
qed

(* Verification of tsscanl with tsscanl_nth *)

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

lemma tstake2ofinftick: "(tsinftimes (Abs_tstream (\<up>\<surd>))) \<down> 2 = Abs_tstream (<[\<surd>, \<surd>]>)"
by (smt One_nat_def Rep_Abs Rep_cfun_strict1 Suc_1 list2s.simps(2) list2s_0 lscons_conv sup'_def 
    tick_msg tsDropTake1 tsTake.simps(1) tsTakeDrop tsconc_assoc tsconc_insert tsinftimes_unfold
    tstake2of2tick tstake_tick)

(* Constructed non continous function on tstreams is monotone and weak causal *)
definition tsmonoweak :: "'a tstream \<Rightarrow> 'a tstream" where
"tsmonoweak ts \<equiv> if (#\<surd> ts)<\<infinity> then tsntimes (THE a. Fin a=#\<surd> ts) (Abs_tstream (\<up>\<surd>)) 
  else tsinftimes (Abs_tstream (\<up>\<surd>))"

lemma mono_tsmonoweak: "monofun tsmonoweak"
apply (rule monofunI)
apply (simp add: tsmonoweak_def below_tstream_def, auto)
sorry

(*
lemma tsnoncont_inftick:
  "tsnoncont (tsinftimes (Abs_tstream (\<up>\<surd>))) = Abs_tstream (<[\<surd>, \<surd>]>)"
apply (simp add: tsnoncont_def)
by (metis ln_less lnless_def slen_scons tick_msg tsconc_rep_eq tsinftimes_unfold)

lemma not_below_2tick_tick: "Abs_tstream (\<up>\<surd> \<bullet> \<up>\<surd>) \<notsqsubseteq> Abs_tstream (\<up>\<surd>)"
by (smt Rep_Abs Rep_tstream_inject list2s.simps(1) list2s.simps(2) list2s_inj lscons_conv 
    not_Cons_self po_eq_conv sup'_def tick_msg ts_tsconc_prefix ts_well_conc1 tsconc_rep_eq1)

lemma tsnoncont_tick_is_ub: "range (\<lambda>i. tsnoncont tsinftimes (Abs_tstream (\<up>\<surd>)) \<down> i ) <| Abs_tstream (\<up>\<surd>)"
apply (simp add: is_ub_def tsnoncont_def, auto)
by (metis below_bottom_iff inf_ub less_le tsDropNth tsDropTake1 ts_tsconc_prefix tsinf_nth 
    tstickcount_insert tstreaml1)

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
*)

end