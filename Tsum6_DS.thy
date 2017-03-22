(*  Title:  Tsum6_DS.thy
    Author: Dennis Slotboom
    e-mail: dennis.slotboom@rwth-aachen.de

    Description:  Definitons and lemmas for tsum6 
*)

theory Tsum6_DS
imports TStream StreamCase_Study Tsum5_HK
begin

(* Definition of tsum6 and verification with tsum5 *)

(* Compute sum of previous inputs and emit it *)
definition tsum6 :: "nat tstream \<rightarrow> nat tstream" where
"tsum6 \<equiv> tsscanl plus 0"

lemma tsum5_h_unfold_tick: "shd s=\<surd> \<and> s\<noteq>\<epsilon> \<Longrightarrow> tsum5_h q\<cdot>s = \<up>\<surd> \<bullet> tsum5_h q\<cdot>(srt\<cdot>s)"
by (metis surj_scons tsum5_h_scons_tick)

(* Nth element of tsum6 and tsum5 are equal *)
lemma tsum6_h2tsum5_h_snth: 
  "Fin n < #(tsscanl_h op + q\<cdot>s) \<longrightarrow> snth n (tsscanl_h op + q\<cdot>s) = snth n (tsum5_h q\<cdot>s)"
apply (induction n arbitrary: q s, auto)
proof -
  fix  n :: "nat" and q :: "nat" and s :: "nat event stream" and k :: "lnat"
  assume a1: "#s = lnsuc\<cdot>k"
  hence h1: "s\<noteq>\<epsilon>"
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

primrec ttimes_nth:: "nat \<Rightarrow> nat event stream \<Rightarrow> nat" where
"ttimes_nth 0 s = (if shd s=\<surd> then 1 else 1 * \<M>\<inverse> shd s)" |
"ttimes_nth (Suc n) s = (if shd s=\<surd> then 1 * ttimes_nth n (srt\<cdot>s) 
                         else (\<M>\<inverse>(shd s)) * ttimes_nth n (srt\<cdot>s))"

lemma tsscanl_h_times_switch_initial:
  "Fin n<#(s :: nat event stream) \<and> snth n s\<noteq>\<surd> 
    \<Longrightarrow> snth n (tsscanl_h times q\<cdot>s) = \<M> q * \<M>\<inverse> snth n (tsscanl_h times 1\<cdot>s)"
proof (induction n arbitrary: q s, auto)
  fix q :: "nat" and s :: "nat event stream" and k :: "lnat"
  assume a1: "shd s \<noteq> \<surd>"
  assume a2: "#s = lnsuc\<cdot>k"
  hence h1: "s\<noteq>\<epsilon>"
    using bot_is_0 lnat.con_rews strict_slen by auto
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

lemma tsscanl_h2ttimes_nth_snth: 
  "Fin n<#s \<and> snth n s\<noteq>\<surd> \<Longrightarrow> snth n (tsscanl_h times 1\<cdot>s) = \<M> ttimes_nth n s"
proof (induction n arbitrary: s, auto)
  fix s :: "nat event stream" and k :: "lnat"
  assume a1: "shd s \<noteq> \<surd>"
  assume a2: "#s = lnsuc\<cdot>k"
  hence h1: "s\<noteq>\<epsilon>"
    using bot_is_0 lnat.con_rews strict_slen by auto
  thus "shd (tsscanl_h op * 1\<cdot>s) = \<M> \<M>\<inverse> shd s"
    by (simp add: a1 h1 tsscanl_h_unfold_shd)
next  
  fix n :: "nat" and s :: "nat event stream"
  assume a3: "\<And>s. Fin n < #s \<and> snth n s \<noteq> \<surd> \<Longrightarrow> snth n (tsscanl_h op * 1\<cdot>s) = \<M> ttimes_nth n s"
  assume a4: " Fin (Suc n) < #s"
  assume a5: "snth (Suc n) s \<noteq> \<surd>"
  thus "shd s = \<surd> \<Longrightarrow> snth (Suc n) (tsscanl_h op * 1\<cdot>s) = \<M> ttimes_nth n (srt\<cdot>s)"
    by (metis a3 a4 not_less slen_rt_ile_eq snth_rt tsscanl_h_unfold_srt_tick)
  thus "shd s \<noteq> \<surd> \<Longrightarrow> snth (Suc n) (tsscanl_h op * 1\<cdot>s) = \<M> \<M>\<inverse> shd s * ttimes_nth n (srt\<cdot>s)"
    by (smt a3 a4 a5 event.simps(4) mult.left_neutral not_less slen_rt_ile_eq snth_rt 
        tsscanl_h_times_switch_initial tsscanl_h_unfold_srt)
qed

lemma tsscanl_h2ttimes_nth: 
  "Fin n<#s \<Longrightarrow> snth n (tsscanl_h times 1\<cdot>s) = (case (snth n s) of Msg a \<Rightarrow> \<M> ttimes_nth n s | \<surd> \<Rightarrow> \<surd>)"
apply (cases "snth n s =\<surd>", simp add: tsscanl_h_snth_tick2tick)
by (metis event.exhaust event.simps(4) tsscanl_h2ttimes_nth_snth)

lemma ttimes2ttimes_nth: 
  "Fin n<#(Rep_tstream ts) \<Longrightarrow> snth n (Rep_tstream (ttimes\<cdot>ts)) =
      (case (snth n (Rep_tstream ts)) of Msg a \<Rightarrow> \<M> ttimes_nth n (Rep_tstream ts) | \<surd> \<Rightarrow> \<surd>)"
by (simp add: ttimes_def tsscanl_unfold ts_well_tsscanl_h tsscanl_h2ttimes_nth)

(* Workspace *)

(* Definition of tsscanl_nth_nq (neutral element q) and unfold lemmata *)

primrec tsscanl_nth_nq :: "nat \<Rightarrow> ('a \<Rightarrow> 'a  \<Rightarrow> 'a) \<Rightarrow> 'a  \<Rightarrow> 'a event stream \<Rightarrow> 'a" where
"tsscanl_nth_nq 0 f q s = (if shd s=\<surd> then q else f q (\<M>\<inverse> (shd s)))" |
"tsscanl_nth_nq (Suc n) f q s = (if shd s=\<surd> then f q (tsscanl_nth_nq n f q (srt\<cdot>s))
                                 else f (\<M>\<inverse> (shd s)) (tsscanl_nth_nq n f q (srt\<cdot>s)))"

lemma tsscanl_nth_nq_suc: 
  "shd s\<noteq>\<surd> \<Longrightarrow> tsscanl_nth_nq (Suc n) f q s = f (\<M>\<inverse> (shd s)) (tsscanl_nth_nq n f q (srt\<cdot>s))"
by (simp add: tsscanl_nth_nq_def)

lemma tsscanl_nth_nq_suc_tick: 
  "shd s=\<surd> \<Longrightarrow> tsscanl_nth_nq (Suc n) f q s = f q (tsscanl_nth_nq n f q (srt\<cdot>s))"
by (simp add: tsscanl_nth_nq_def)

(* Verification of tsscanl with tsscanl_nth_nq *)

lemma tsscanl_h_nq_switch_initial: "Fin n<#s \<and> snth n s\<noteq>\<surd> \<and> (\<forall>a. f q a=a) 
  \<Longrightarrow> snth n (tsscanl_h f p\<cdot>s) = \<M> f p (\<M>\<inverse> snth n (tsscanl_h f q\<cdot>s))"
proof (induction n arbitrary: p q s, auto)
  fix p :: "'a" and q :: "'a" and s :: "'a event stream" and k :: "lnat"
  assume a1: "#s = lnsuc\<cdot>k"
  hence h1: "s\<noteq>\<epsilon>"
    using lnsuc_neq_0_rev strict_slen by auto
  assume a2: "shd s \<noteq> \<surd>"
  assume a3: "\<forall>a. f q a = a"
  thus "shd (tsscanl_h f p\<cdot>s) = \<M> f p \<M>\<inverse> shd (tsscanl_h f q\<cdot>s)"
    by (simp add: a2 h1 tsscanl_h_unfold_shd)
next
  fix n :: "nat" and p :: "'a" and q :: "'a" and s :: "'a event stream"
  assume a4: "\<And>p q s. Fin n < #s \<and> snth n s \<noteq> \<surd> \<and> (\<forall>a. f q a = a) 
                \<Longrightarrow> snth n (tsscanl_h f p\<cdot>s) = \<M> f p \<M>\<inverse> snth n (tsscanl_h f q\<cdot>s)"
  assume a5: "Fin (Suc n) < #s"
  assume a6: "snth (Suc n) s \<noteq> \<surd>"
  assume a7: "\<forall>a. f q a = a"
  thus "snth (Suc n) (tsscanl_h f p\<cdot>s) = \<M> f p \<M>\<inverse> snth (Suc n) (tsscanl_h f q\<cdot>s)"
    apply (cases "shd s=\<surd>")
    apply (metis a4 a5 a6 convert_inductive_asm not_less slen_rt_ile_eq snth_rt tsscanl_h_snth_tick)
    apply (simp add: a5 convert_inductive_asm tsscanl_h_snth)
    sorry
qed

(*
  thus "snth (Suc n) (tsscanl_h op * q\<cdot>s) = \<M> q * \<M>\<inverse> snth (Suc n) (tsscanl_h op * 1\<cdot>s)"
    by (smt Suc_neq_Zero a3 a4 event.simps(4) less_imp_not_eq2 lnle_Fin_0 mult.assoc 
        mult.comm_neutral not_less slen_rt_ile_eq snth_scons strict_slen surj_scons trans_lnless
        tsscanl_h_scons tsscanl_h_scons_tick)  
*)

lemma tsscanl_h2tsscanl_nth_nq_snth: 
  "Fin n<#s \<and> snth n s\<noteq>\<surd> \<and> (\<forall>a. f q a=a) \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth_nq n f q s"
proof (induction n arbitrary: q s, auto)
  fix q :: "'a" and s :: "'a event stream" and k :: "lnat"
  assume a1: "#s = lnsuc\<cdot>k"
  assume a2: "shd s \<noteq> \<surd>"
  assume a3: "\<forall>a. f q a = a"
  thus "shd (tsscanl_h f q\<cdot>s) = \<M> \<M>\<inverse> shd s"
    by (metis a1 a2 lnat.con_rews lnzero_def slen_empty_eq tsscanl_h_unfold_shd)
next  
  fix n :: "nat" and  q :: "'a" and s :: "'a event stream"
  assume a4: "\<And>q s. Fin n < #s \<and> snth n s \<noteq> \<surd> \<and> (\<forall>a. f q a = a) 
                \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth_nq n f q s"
  assume a5: "Fin (Suc n) < #s"
  assume a6: "snth (Suc n) s \<noteq> \<surd>"
  assume a7: "\<forall>a. f q a = a"
  thus "shd s = \<surd> \<Longrightarrow> snth (Suc n) (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth_nq n f q (srt\<cdot>s)"
    by (metis (no_types, lifting) a4 a5 a6 convert_inductive_asm not_less slen_rt_ile_eq snth_rt tsscanl_h_snth_tick)
  thus "shd s \<noteq> \<surd> \<Longrightarrow> snth (Suc n) (tsscanl_h f q\<cdot>s) = \<M> f \<M>\<inverse> shd s (tsscanl_nth_nq n f q (srt\<cdot>s))"
    apply (simp add: snth_rt tsscanl_h_unfold_srt a7)
    apply (insert tsscanl_h_nq_switch_initial [of n "srt\<cdot>s" f q "\<M>\<inverse> shd s"])
    by (metis (no_types, lifting) a4 a5 a6 a7 event.simps(4) not_less slen_rt_ile_eq snth_rt)
qed

lemma tsscanl_h2tsscanl_nth_nq: 
  "Fin n<#s \<and> (\<forall>a. f q a=a) \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) = (case (snth n s) of Msg a \<Rightarrow> \<M> tsscanl_nth_nq n f q s | \<surd> \<Rightarrow> \<surd>)"
apply (cases "snth n s =\<surd>", simp add: tsscanl_h_snth_tick2tick)
by (metis event.exhaust event.simps(4) tsscanl_h2tsscanl_nth_nq_snth)

lemma tsscanl2tsscanl_nth_nq: 
  "Fin n<#(Rep_tstream ts) \<and> (\<forall>a. f q a=a) \<Longrightarrow> snth n (Rep_tstream (tsscanl f q\<cdot>ts)) =
      (case (snth n (Rep_tstream ts)) of Msg a \<Rightarrow> \<M> tsscanl_nth_nq n f q (Rep_tstream ts) | \<surd> \<Rightarrow> \<surd>)"
by (simp add: ttimes_def tsscanl_unfold ts_well_tsscanl_h tsscanl_h2tsscanl_nth_nq)

(* The n+1st element produced by tsscanl_h is the result of merging the n+1st item of s with the nth
   element produced by tsscanl *)
lemma tsscanl_h_snth_merge_tick: 
  "Fin (Suc n)<#s \<and> snth (Suc n) s\<noteq>\<surd> \<and> (\<forall>m. m<(Suc n) \<and> snth m s=\<surd>)
    \<Longrightarrow> snth (Suc n) (tsscanl_h f q\<cdot>s) = \<M> f q \<M>\<inverse> (snth (Suc n) s)"
by (auto)

lemma tsscanl_h_snth_merge: 
  "Fin (Suc n)<#s \<and> snth (Suc n) s\<noteq>\<surd> \<and> (\<exists>m. m<(Suc n) \<and> snth m s\<noteq>\<surd>)
    \<Longrightarrow> snth (Suc n) (tsscanl_h f q\<cdot>s) =
    \<M> f \<M>\<inverse> (snth (THE m. Fin m=#({e. e\<noteq>\<surd>} \<ominus> stake n\<cdot>s)) (tsscanl_h f q\<cdot>s)) \<M>\<inverse> (snth (Suc n) s)"
proof (induction n arbitrary: q s, auto)
  fix q :: "'b" and s :: "'a event stream"
  assume a1: "Fin (Suc 0) < #s"
  assume a2: "snth (Suc 0) s \<noteq> \<surd>"
  assume a3: "shd s \<noteq> \<surd>"
  thus "snth (Suc 0) (tsscanl_h f q\<cdot>s) = \<M> f \<M>\<inverse> shd (tsscanl_h f q\<cdot>s) \<M>\<inverse> snth (Suc 0) s"
    by (smt Fin_02bot Fin_Suc MsginvMsg Suc_neq_Zero a1 a2 event.distinct(1) event.inject less2lnleD
        lnle_Fin_0 lnzero_def neq_iff slen_scons snth_rt snth_shd strict_slen surj_scons
        tsscanl_h_unfold_shd tsscanl_h_unfold_srt)
next
  fix n :: "nat" and q :: "'b" and s :: "'a event stream" and m :: "nat"
  assume a4: "\<And>q s. Fin (Suc n) < #s \<and> snth (Suc n) s \<noteq> \<surd> \<and> (\<exists>m<Suc n. snth m s \<noteq> \<surd>) \<Longrightarrow>
               snth (Suc n) (tsscanl_h f q\<cdot>s) = \<M> f \<M>\<inverse> snth (THE m. Fin m = #({e. e \<noteq> \<surd>} \<ominus> stake n\<cdot>s)) (tsscanl_h f q\<cdot>s) \<M>\<inverse> snth (Suc n) s"
  assume a5: "Fin (Suc (Suc n)) < #s"
  assume a6: "snth (Suc (Suc n)) s \<noteq> \<surd>"
  assume a7: "m < Suc (Suc n)"
  assume a8: "snth m s \<noteq> \<surd>"
  thus "snth (Suc (Suc n)) (tsscanl_h f q\<cdot>s) =
       \<M> f \<M>\<inverse> snth (THE m. Fin m = #({e. e \<noteq> \<surd>} \<ominus> stake (Suc n)\<cdot>s)) (tsscanl_h f q\<cdot>s) \<M>\<inverse> snth (Suc (Suc n)) s"
    apply (simp add: snth_rt)
oops

(* Definition of tsscanl_nth and unfold lemmata *)

primrec tsscanl_nth :: "nat \<Rightarrow> ('a \<Rightarrow> 'a  \<Rightarrow> 'a) \<Rightarrow> 'a  \<Rightarrow> 'a event stream \<Rightarrow> 'a" where
"tsscanl_nth 0 f q s = (if shd s=\<surd> then q else f q (\<M>\<inverse> (shd s)))" |
"tsscanl_nth (Suc n) f q s = (if shd s=\<surd> then tsscanl_nth n f q (srt\<cdot>s)
                              else f (\<M>\<inverse> (shd s)) (tsscanl_nth n f q (srt\<cdot>s)))"

lemma tsscanl_nth_suc: 
  "shd s\<noteq>\<surd> \<Longrightarrow> tsscanl_nth (Suc n) f q s = f (\<M>\<inverse> (shd s)) (tsscanl_nth n f q (srt\<cdot>s))"
by (simp add: tsscanl_nth_def)

lemma tsscanl_nth_suc_tick: "shd s=\<surd> \<Longrightarrow> tsscanl_nth (Suc n) f q s = tsscanl_nth n f q (srt\<cdot>s)"
by (simp add: tsscanl_nth_def)

(* Verification of tsscanl with tsscanl_nth *)

(*
lemma tsscanl_nth_unfold: "Fin (Suc n)<#s \<and> shd s\<noteq>\<surd> \<and> snth (Suc n) s \<noteq> \<surd>
   \<Longrightarrow> tsscanl_nth (Suc n) f q s = tsscanl_nth n f (f q \<M>\<inverse> shd s) (srt\<cdot>s)"
apply (cases "shd s=\<surd>", simp)
apply (induction n arbitrary: q s, auto)
apply (simp add: snth_rt)
sorry

lemma tsscanl_h2tsscanl_nth_h: 
  "Fin n<#s \<and> snth n s\<noteq>\<surd> \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth n f q s"
apply (induction n arbitrary: q s)
apply auto[1]
proof -
  fix q :: "'a" and s :: "'a event stream" and k :: "lnat"
  assume a1: "shd s \<noteq> \<surd>"
  assume a2: "#s = lnsuc\<cdot>k"
  thus "shd (tsscanl_h f q\<cdot>s) = \<M> f q \<M>\<inverse> shd s"
    using a1 lnsuc_neq_0 strict_slen tsscanl_h_unfold_shd by fastforce
next  
  fix n :: "nat" and  q :: "'a" and s :: "'a event stream"
  assume a3: "\<And>q s. Fin n < #s \<and> snth n s \<noteq> \<surd> \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth n f q s"
  thus "Fin (Suc n) < #s \<and> snth (Suc n) s \<noteq> \<surd> \<Longrightarrow> 
        snth (Suc n) (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth (Suc n) f q s"
    by (metis (no_types, lifting) not_less slen_rt_ile_eq snth_rt tsscanl_nth_unfold 
        tsscanl_h_unfold_srt tsscanl_h_unfold_srt_tick tsscanl_nth_suc_tick)
qed

*)  

lemma tsscanl_h2tsscanl_nth_h: 
  "Fin n<#s \<and> snth n s\<noteq>\<surd> \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth n f q s"
proof (induction n arbitrary: q s, auto)
  fix q :: "'a" and s :: "'a event stream" and k :: "lnat"
  assume a1: "shd s \<noteq> \<surd>"
  assume a2: "#s = lnsuc\<cdot>k"
  thus "shd (tsscanl_h f q\<cdot>s) = \<M> f q \<M>\<inverse> shd s"
    using a1 lnsuc_neq_0 strict_slen tsscanl_h_unfold_shd by fastforce
next  
  fix n :: "nat" and  q :: "'a" and s :: "'a event stream"
  assume a3: "\<And>q s. Fin n < #s \<and> snth n s \<noteq> \<surd> \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth n f q s"
  assume a4: " Fin (Suc n) < #s"
  assume a5: "snth (Suc n) s \<noteq> \<surd>"
  thus "shd s = \<surd> \<Longrightarrow> snth (Suc n) (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth n f q (srt\<cdot>s)"
    by (metis (no_types, lifting) a3 a4 convert_inductive_asm not_less slen_rt_ile_eq snth_rt 
        tsscanl_h_snth_tick)
  thus "shd s \<noteq> \<surd> \<Longrightarrow> snth (Suc n) (tsscanl_h f q\<cdot>s) = \<M> f \<M>\<inverse> shd s (tsscanl_nth n f q (srt\<cdot>s))"
    apply (simp add: snth_rt tsscanl_h_unfold_srt)
    sorry
qed

lemma tsscanl_h2tsscanl_nth: 
  "Fin n<#s \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) = (case (snth n s) of Msg a \<Rightarrow> \<M> tsscanl_nth n f q s | \<surd> \<Rightarrow> \<surd>)"
apply (cases "snth n s =\<surd>", simp add: tsscanl_h_snth_tick2tick)
by (metis event.exhaust event.simps(4) tsscanl_h2tsscanl_nth_h)

lemma tsscanl2tsscanl_nth: 
  "Fin n<#(Rep_tstream ts) \<Longrightarrow> snth n (Rep_tstream (tsscanl f q\<cdot>ts)) =
      (case (snth n (Rep_tstream ts)) of Msg a \<Rightarrow> \<M> tsscanl_nth n f q (Rep_tstream ts) | \<surd> \<Rightarrow> \<surd>) "
by (simp add: tsscanl_unfold ts_well_tsscanl_h tsscanl_h2tsscanl_nth)

(* Verification of tsscanl with sscanl *)

(* Use tsscanl_h2sscanl_snth? *)

lemma sfilter_msg_shd:" {e. e \<noteq> \<surd>} \<ominus> s\<noteq>\<epsilon> \<Longrightarrow> shd ({e. e \<noteq> \<surd>} \<ominus> s) \<noteq> \<surd>"
using sfilter_ne_resup by auto

lemma tsscanl_h2tsscanl_h: "Fin n<#s \<and> snth n s\<noteq>\<surd> \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) =
   snth (THE m. Fin m = #({e. e \<noteq> \<surd>} \<ominus> stake n\<cdot>s)) (tsscanl_h f q\<cdot>({e. e\<noteq>\<surd>} \<ominus> s))"
proof (induction n arbitrary: q s, auto)
  fix q :: 'b and s :: "'a event stream" and k :: "lnat"
  assume a1: "#s = lnsuc\<cdot>k"
  assume a2: "shd s \<noteq> \<surd>"
  thus "shd (tsscanl_h f q\<cdot>s) = shd (tsscanl_h f q\<cdot>({e. e \<noteq> \<surd>} \<ominus> s))"
    by (smt a1 lnat.con_rews lnzero_def mem_Collect_eq sfilter_in shd1 slen_empty_eq surj_scons
        tsscanl_h_scons)
next
  fix n :: "nat" and q :: "'b" and s :: "'a event stream"
  assume a3: "\<And>q s. Fin n < #s \<and> snth n s \<noteq> \<surd> \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) =
              snth (THE m. Fin m = #({e. e \<noteq> \<surd>} \<ominus> stake n\<cdot>s)) (tsscanl_h f q\<cdot>({e. e \<noteq> \<surd>} \<ominus> s))"
  assume a4: "Fin (Suc n) < #s"
  assume a5: "snth (Suc n) s \<noteq> \<surd>"
  obtain m where h1: "(THE m. Fin m = #({e. e \<noteq> \<surd>} \<ominus> stake n\<cdot>s))=m"
    by simp
  hence h2: "snth (Suc n) s \<noteq> \<surd> \<Longrightarrow> (THE m. Fin m = #({e. e \<noteq> \<surd>} \<ominus> stake (Suc n)\<cdot>s))= Suc m"
    sorry
  thus "snth (Suc n) (tsscanl_h f q\<cdot>s) = snth (THE m. Fin m = #({e. e \<noteq> \<surd>} \<ominus> stake (Suc n)\<cdot>s)) (tsscanl_h f q\<cdot>({e. e \<noteq> \<surd>} \<ominus> s))"
    apply (simp add: a5 h2)
    apply (simp add: snth_rt)
    apply (cases "shd s=\<surd>")
    apply (simp add: tsscanl_h_unfold_srt_tick)
oops

lemma tsscanl_h2sscanl: 
  "Fin n<#s \<and> snth n s\<noteq>\<surd> \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) =
    \<M> snth (THE m. Fin m = #({e. e \<noteq> \<surd>} \<ominus> stake n\<cdot>s)) (sscanl f q\<cdot>(smap (\<lambda>e. \<M>\<inverse> e)\<cdot>({e. e\<noteq>\<surd>} \<ominus> s)))"
proof (induction n arbitrary: q s, auto)
  fix q :: "'b" and s :: "'a event stream" and k :: "lnat"
  assume a1: "shd s \<noteq> \<surd>"
  assume a2: "#s = lnsuc\<cdot>k"
  thus "shd (tsscanl_h f q\<cdot>s) = \<M> shd (sscanl f q\<cdot>(smap inversMsg\<cdot>({e. e \<noteq> \<surd>} \<ominus> s)))"
    by (smt a1 lnat.con_rews lnzero_def mem_Collect_eq sfilter_in shd1 slen_empty_eq smap_scons
        sscanl_scons surj_scons tsscanl_h_unfold_shd)
next
  fix n :: "nat" and q :: "'b" and s :: "'a event stream"
  assume a3: "\<And>q s. Fin n < #s \<and> snth n s \<noteq> \<surd> \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) =
   \<M> snth (THE m. Fin m = #({e. e \<noteq> \<surd>} \<ominus> stake n\<cdot>s)) (sscanl f q\<cdot>(smap inversMsg\<cdot>({e. e \<noteq> \<surd>} \<ominus> s)))"
  assume a4: "Fin (Suc n) < #s"
  assume a5: "snth (Suc n) s \<noteq> \<surd>"
  obtain m where h1: "(THE m. Fin m = #({e. e \<noteq> \<surd>} \<ominus> stake n\<cdot>s))=m"
    by simp
  hence h2: "snth (Suc n) s \<noteq> \<surd> \<Longrightarrow> (THE m. Fin m = #({e. e \<noteq> \<surd>} \<ominus> stake (Suc n)\<cdot>s))= Suc m"
    sorry
  thus "snth (Suc n) (tsscanl_h f q\<cdot>s) =
    \<M> snth (THE m. Fin m = #({e. e \<noteq> \<surd>} \<ominus> stake (Suc n)\<cdot>s)) (sscanl f q\<cdot>(smap inversMsg\<cdot>({e. e \<noteq> \<surd>} \<ominus> s)))"
  apply (simp add: a5 h2)
  apply (cases "shd s=\<surd>")
  apply (simp add: snth_rt sscanl_srt tsscanl_h_unfold_srt)
  sorry
qed

lemma tsscanl2sscanl:
  "Fin n<#(Rep_tstream ts) \<Longrightarrow> snth n (Rep_tstream (tsscanl f q\<cdot>ts)) =
      (case (snth n (Rep_tstream ts)) of Msg a \<Rightarrow> 
        \<M> snth (THE m. Fin m=#({e. e\<noteq>\<surd>} \<ominus> stake n\<cdot>(Rep_tstream ts)))
          (sscanl f q\<cdot>(tsAbs\<cdot>ts)) | \<surd> \<Rightarrow> \<surd>)"
apply (simp add: tsscanl_unfold ts_well_tsscanl_h)
apply (cases "snth n (Rep_tstream ts)=\<surd>", simp add: tsscanl_h_snth_tick2tick)
apply (subst tsabs_insert)
apply (simp add: tsscanl_h2sscanl)
by (metis (no_types, lifting) event.exhaust event.simps(4))

end