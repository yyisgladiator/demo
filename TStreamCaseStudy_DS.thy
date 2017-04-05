(* 
    Title:  TStreamCaseStudy_DS.thy
    Author: Dennis Slotboom
    e-mail: dennis.slotboom@rwth-aachen.de

    Description: Definitons and lemmas for tsum6, ttimes and tsscanl
*)

theory TStreamCaseStudy_DS
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

(* Verification of tsscanl with tsscanl_nth under assumptions:
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

(* Examples for weak causal functions *)

(* Identity function on tstreams is monotone, continous and weak causal *)
definition tsident :: "'a tstream \<Rightarrow> 'a tstream" where
"tsident ts \<equiv> ts"

lemma mono_tsident: "monofun tsident"
by (simp add: monofunI tsident_def)

lemma cont_tsident: "cont tsident"
by (metis mono_tsident tsMono2weak2cont tsident_def)

lemma tsweak_tsident:"tsWeakCausal tsident"
by (simp add: tsident_def tsWeakCausalI)

(* Dropfirst is a monotone and continous but not weak causal function on tstreams *)
lemma mono_tsdropfirst: "monofun (\<lambda>ts. tsDropFirst\<cdot>ts)"
by (simp add: monofun_Rep_cfun2)

lemma cont_tsdropfirst: "cont (\<lambda>ts. tsDropFirst\<cdot>ts)"
by (simp add: cont_Rep_cfun2)

lemma non_tsweak_tsdropfirst: "\<not>tsWeakCausal (\<lambda>ts. tsDropFirst\<cdot>ts)"
apply (simp add: tsWeakCausal_def)
by (metis Rep_cfun_strict1 delayFun_dropFirst delayFun_sCausal tsTake.simps(1) ts_existsNBot
    tstake_bot tstake_fin2)

(* Constructed non monotone function on tstreams is not continous but weak causal *)
definition tsbottick :: "'a tstream \<Rightarrow> 'a tstream" where
"tsbottick ts \<equiv> if ts=\<bottom> then Abs_tstream (\<up>\<surd>) else \<bottom>"

lemma non_mono_tsbottick: "\<not>monofun tsbottick"
by (simp add: monofun_def tsbottick_def)

lemma non_cont_tsbottick: "\<not>cont tsbottick"
using cont2mono non_mono_tsbottick by auto

lemma tsweak_tsbottick: "tsWeakCausal tsbottick"
apply (rule tsWeakCausalI)
apply (simp add: tsbottick_def, auto)
using tstakeBot apply blast
using tstakeBot by blast

(* Set of weak causal functions *)
definition "spfw = {f ::'a tstream => 'b tstream. tsWeakCausal f}"

pcpodef ('a, 'b) spfw ("(_ \<leadsto>w/ _)" [1, 0] 0) = "spfw :: ('a tstream => 'b tstream) set"
apply (simp add: spfw_def tsWeakCausal_def)
by (simp add: spfw_def tsWeakCausal_def)

end