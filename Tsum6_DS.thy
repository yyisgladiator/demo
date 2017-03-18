(*  Title:  Tsum6_DS.thy
    Author: Dennis Slotboom
    e-mail: dennis.slotboom@rwth-aachen.de

    Description:  Definitons and lemmas for tsum6 
*)

theory Tsum6_DS
imports TStream StreamCase_Study Tsum5_HK
begin

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

(* Definition of ttimes1 and ttimes_nth *)
definition ttimes1 :: "nat tstream \<rightarrow> nat tstream" where
"ttimes1 \<equiv> tsscanl times 1"

primrec ttimes_nth:: "nat \<Rightarrow> nat event stream \<Rightarrow> nat" where
"ttimes_nth 0 s = (if shd s=\<surd> then 1 else \<M>\<inverse> shd s)" |
"ttimes_nth (Suc n) s = (if shd s=\<surd> then 1 * ttimes_nth n (srt\<cdot>s) 
                         else (\<M>\<inverse>(shd s)) * ttimes_nth n (srt\<cdot>s))"

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



lemma neutral_tsscanl_h_unfold: "Fin n<#s \<and> snth n s\<noteq>\<surd> \<and> (\<forall>a. f q a=a) 
  \<Longrightarrow> snth n (tsscanl_h f p\<cdot>s) =\<M> f (\<M>\<inverse> snth n (tsscanl_h f q\<cdot>s)) p"
apply (induction n arbitrary: p q s, auto)
proof -
  fix p :: "'a" and q :: "'a" and s :: "'a event stream" and k :: "lnat"
  assume a1: "#s = lnsuc\<cdot>k"
  hence h1: "s\<noteq>\<epsilon>"
    using lnsuc_neq_0_rev strict_slen by auto
  assume a2: "shd s \<noteq> \<surd>"
  assume a3: "\<forall>a. f q a = a"
  thus "shd (tsscanl_h f p\<cdot>s) = \<M> f \<M>\<inverse> shd (tsscanl_h f q\<cdot>s) p"
    apply (simp add: a2 h1 tsscanl_h_unfold_shd)
    sorry
next
*)  

lemma tsscanl_h2tsscanl_nth_h: 
  "Fin n<#s \<and> snth n s\<noteq>\<surd> \<Longrightarrow> snth n (tsscanl_h f q\<cdot>s) = \<M> tsscanl_nth n f q s"
apply (induction n arbitrary: q s, auto)
proof -
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
apply (induction n arbitrary: q s, auto)
proof -
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
apply (induction n arbitrary: q s, auto)
proof -
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