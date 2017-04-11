(* 
    Title:  TStreamCaseStudy_DS.thy
    Author: Dennis Slotboom
    e-mail: dennis.slotboom@rwth-aachen.de

    Description: Definitons and lemmas for tsum6, ttimes and tsscanl
*)

theory TStreamCaseStudy_DS
imports TStream
begin

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
using tstakeBot apply blast
using tstakeBot by blast

(* Constructed non weak causal function on tstreams is monotone and continous *)
setup_lifting type_definition_cfun

lift_definition tsnontsweak1 :: "'a tstream \<rightarrow> 'a tstream" is "\<lambda>ts. Abs_tstream (srt\<cdot>(Rep_tstream ts))"
by (simp add: cfun_def)

definition tsnontsweak2 :: "'a tstream \<Rightarrow> 'a tstream" where
"tsnontsweak2 ts \<equiv> Abs_tstream (srt\<cdot>(Rep_tstream ts))"

lemma tstake1of1_tick: "Abs_tstream (\<up>\<surd>) \<down> 1 = Abs_tstream (\<up>\<surd>)"
by (simp add: tsTake_def2 One_nat_def)

lemma tstake1of2_tick: "Abs_tstream (<[\<surd>, \<surd>]>) \<down> 1 = Abs_tstream (\<up>\<surd>)"
by (simp add: tsTake_def2 One_nat_def tstakefirst_insert_rep_eq)

lemma mono_tsnontsweak1: "monofun (Rep_cfun tsnontsweak1)"
by (simp add: monofun_Rep_cfun2)

lemma mono_tsnontsweak2: "monofun tsnontsweak2"
by (simp add: monofun_def tsnontsweak2_def below_tstream_def monofun_cfun_arg)

lemma cont_tsnontsweak1: "cont (Rep_cfun tsnontsweak1)"
by (simp add: cont_Rep_cfun2)

lemma cont_tsnontsweak2: "cont tsnontsweak2"
apply (rule contI2)
apply (simp add: mono_tsnontsweak2)
apply (simp add: tsnontsweak2_def below_tstream_def)
by (smt Rep_Abs Rep_tstream_inject contlub_cfun_arg eq_imp_below lub_eq ts_well_Rep ts_well_drop1
    tsnontsweak1.rep_eq)

(* <\<surd>, \<surd>> \<down> 1 = <\<surd>> \<down> 1 but <\<surd>> \<down> 1 \<noteq> \<bottom> \<down> 1 *)
lemma non_tsweak_tsnontsweak: "\<not>tsWeakCausal tsnontsweak2"
proof -
  have h1: "tsnontsweak2 (Abs_tstream (<[\<surd>, \<surd>]>)) = Abs_tstream (\<up>\<surd>)"
    by (simp add: tsnontsweak2_def)
  have h2: "tsnontsweak2 (Abs_tstream (\<up>\<surd>)) = \<bottom>"
    by (simp add: tsnontsweak2_def)
  hence h3: "((tsnontsweak2 (Abs_tstream (<[\<surd>, \<surd>]>))) \<down> 1) \<noteq> ((tsnontsweak2 (Abs_tstream (\<up>\<surd>))) \<down> 1)"
    by (simp add: h1 tsnontsweak2_def tstake1of1_tick)
  have h4: "Abs_tstream (<[\<surd>, \<surd>]>) \<down> 1 = Abs_tstream (\<up>\<surd>) \<down> 1"
    by (metis tstake1of1_tick tstake1of2_tick)
  thus "\<not>tsWeakCausal tsnontsweak2"
    apply (simp add: tsWeakCausal_def)
    using h3 by auto    
qed

(* Constructed non continous function on tstreams is not weak causal but monotone *)
definition tsnoncont :: "'a tstream \<Rightarrow> 'a tstream" where
"tsnoncont ts \<equiv> if #(Rep_tstream ts)<\<infinity> then Abs_tstream (\<up>\<surd>)
                else Abs_tstream (<[\<surd>, \<surd>]>)"

lemma tstake2of1_tick: "Abs_tstream (\<up>\<surd>) \<down> 2 = Abs_tstream (\<up>\<surd>)"
using tstake1of1_tick tstake_fin2 by fastforce

lemma tstake2of2_tick: "Abs_tstream (<[\<surd>, \<surd>]>) \<down> 2 = Abs_tstream (<[\<surd>, \<surd>]>)"
by (smt One_nat_def Rep_Abs list2s.simps(2) list2s_0 lscons_conv numeral_2_eq_2 sup'_def tick_msg
    tsconc_insert tstake1of1_tick tstake_tick)

lemma tstake2ofinf_tick: "(tsinftimes (Abs_tstream (\<up>\<surd>))) \<down> 2 = Abs_tstream (<[\<surd>, \<surd>]>)"
by (smt One_nat_def Rep_Abs Rep_cfun_strict1 Suc_1 list2s.simps(2) list2s_0 lscons_conv sup'_def 
    tick_msg tsDropTake1 tsTake.simps(1) tsTakeDrop tsconc_assoc tsconc_insert tsinftimes_unfold
    tstake2of2_tick tstake_tick)

lemma mono_tsnoncont: "monofun tsnoncont"
apply (rule monofunI)
apply (simp add: tsnoncont_def below_tstream_def, auto)
by (metis inf_ub lnle_def lnless_def mono_fst_infD)

lemma non_cont_tsnoncont: "\<not>cont tsnoncont"
proof -  
  have h1: "chain (\<lambda>i. (tsinftimes (Abs_tstream (\<up>\<surd>))) \<down> i)"
    by (simp)              
  have h2: "Lub (\<lambda>i. (tsinftimes (Abs_tstream (\<up>\<surd>))) \<down> i) = tsinftimes (Abs_tstream (\<up>\<surd>))"
    by (simp)
  hence h3: "tsnoncont (Lub (\<lambda>i. (tsinftimes (Abs_tstream (\<up>\<surd>))) \<down> i)) = Abs_tstream (<[\<surd>, \<surd>]>)"
    by (metis (mono_tags, lifting) ln_less order_less_irrefl slen_scons tick_msg tsconc_rep_eq
        tsinftimes_unfold tsnoncont_def)
  have h4: "\<Squnion>i. tsnoncont ((tsinftimes (Abs_tstream (\<up>\<surd>))) \<down> i) = Abs_tstream (\<up>\<surd>)"
    apply (simp add: tsnoncont_def)
    sorry
  thus "\<not>cont tsnoncont"
    apply (simp add: cont_def)
    sorry
oops

(* <\<surd>, \<surd>> \<down> 2 = <\<surd>, ...> \<down> 2 but <\<surd>> \<down> 2 \<noteq> <\<surd>, \<surd>> \<down> 2 *)
lemma non_tsweak_tsnoncont: "\<not>tsWeakCausal tsnoncont"
proof -
  have h1: "tsnoncont (tsinftimes (Abs_tstream (\<up>\<surd>))) = Abs_tstream (<[\<surd>, \<surd>]>)"
    by (metis (no_types, lifting) ln_less neq_iff slen_scons tick_msg tsconc_rep_eq
        tsinftimes_unfold tsnoncont_def)
  have h2: "tsnoncont (Abs_tstream (<[\<surd>, \<surd>]>)) = Abs_tstream (\<up>\<surd>)"
    by (simp add: tsnoncont_def)
  have h3: "(tsinftimes (Abs_tstream (\<up>\<surd>))) \<down> 2 = Abs_tstream (<[\<surd>, \<surd>]>) \<down> 2"
    by (metis tstake2of2_tick tstake2ofinf_tick)
  thus "\<not>tsWeakCausal tsnoncont"
    apply (simp add: tsWeakCausal_def)
    by (smt Rep_Abs Suc_1 h1 h2 h3 list.distinct(1) list.inject list2s.simps(2) list2s_0 list2s_inj
        lscons_conv sup'_def tick_msg tsSucTake tsconc_rep_eq tsinftimes_unfold 
        tstake1of1_tick tstake2of1_tick tstake_tick)
qed

(* spfw *)

(* Set of weak causal functions *)
definition "spfw = {f ::'a tstream => 'b tstream. tsWeakCausal f}"

lemma bottom_spfw: "\<bottom> \<in> spfw"
by (simp add: spfw_def tsWeakCausal_def)

(* adm P = (\<forall>Y. chain Y \<longrightarrow> (\<forall>i. P (Y i)) \<longrightarrow> P (\<Squnion>i. Y i)) *)
lemma adm_spfw: "adm (\<lambda>x. x \<in> spfw)"
by (simp add: spfw_def tsWeakCausal_def)

pcpodef ('a, 'b) spfw ("(_ \<leadsto>w/ _)" [1, 0] 0) = "spfw :: ('a tstream => 'b tstream) set"
apply (simp add: bottom_spfw)
by (simp add: adm_spfw)

lemmas Rep_spfw_strict =
  typedef_Rep_strict [OF type_definition_spfw below_spfw_def bottom_spfw]

lemmas Abs_spfw_strict =
  typedef_Abs_strict [OF type_definition_spfw below_spfw_def bottom_spfw]

lemma Abs_spfw_inverse2: "tsWeakCausal f \<Longrightarrow> Rep_spfw (Abs_spfw f) = f"
by (simp add: Abs_spfw_inverse spfw_def)

(* Examples for pcpodef spfw *)

setup_lifting type_definition_spfw

(* Abbreviated form for CONST Abs_spfw does not exist *)
definition tsnonmono_tsweak1 :: "'a \<leadsto>w 'a" where
"tsnonmono_tsweak1 \<equiv> CONST Abs_spfw (\<lambda>ts. if ts=\<bottom> then Abs_tstream (\<up>\<surd>) else \<bottom>)"

lemma tsweak_tsnonmono_tsweak1: "tsWeakCausal (\<lambda>ts. if ts = \<bottom> then Abs_tstream (\<up>\<surd>) else \<bottom>)"
apply (rule tsWeakCausalI)
apply (simp add: tsnonmono_def, auto)
using tstakeBot apply blast
using tstakeBot by blast

lemma non_mono_tsnonmono_tsweak1: "\<not>monofun (Rep_spfw (tsnonmono_tsweak1))"
apply (simp add: monofun_def tsnonmono_tsweak1_def)
by (simp add: Abs_spfw_inverse2 tsweak_tsnonmono_tsweak1)

lift_definition tsnonmono_tsweak2 :: "'a \<leadsto>w 'a" is
"\<lambda>ts. if ts=\<bottom> then Abs_tstream (\<up>\<surd>) else \<bottom>"
apply (simp add: spfw_def)
apply (rule tsWeakCausalI)
apply (simp add: tsnonmono_def, auto)
using tstakeBot apply blast
using tstakeBot by blast

(* Duplicated proof for tsWeakCausal required (definition, lemma) *)
lemma non_mono_tsnonmono_tsweak2: "\<not>monofun (Rep_spfw (tsnonmono_tsweak2))"
apply (simp add: monofun_def tsnonmono_tsweak2_def)
by (simp add: Abs_spfw_inverse2 tsweak_tsnonmono_tsweak1)       

end