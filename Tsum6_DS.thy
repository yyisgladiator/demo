(*  Title:  Tsum6_DS.thy
    Author: Dennis Slotboom
    e-mail: dennis.slotboom@rwth-aachen.de

    Description:  Definitons and lemmas for tsum6 
*)

theory Tsum6_DS
imports TStream StreamCase_Study Tsum5_HK
begin

definition tsum6 :: "nat tstream \<rightarrow> nat tstream" where
"tsum6 \<equiv> tsscanl plus 0"

lemma tsum6_h2tsum5_h: "Fin n < #(tsscanl_h op + 0\<cdot>s) \<longrightarrow> snth n (tsscanl_h op + 0\<cdot>s) = snth n (tsum5_helper 0\<cdot>s)"
sledgehammer
apply (induction n arbitrary: s)
apply (smt Fin_02bot bot_is_0 fair_tsscanl lnless_def shd1 slen_empty_eq snth_shd surj_scons tsscanl_h_scons tsscanl_h_scons_tick tsum5_helper_scons_2 tsum5_helper_scons_tick)
sorry

lemma tsum62tsum5: "tsscanl_h plus 0\<cdot>s = tsum5_helper 0\<cdot>s"
apply (rule snths_eq)
apply (simp)
by (simp add: tsum6_h2tsum5_h)

lemma "tsum6=tsum5"
by (simp add: tsscanl_def tsum5_def tsum6_def tsum62tsum5)

end