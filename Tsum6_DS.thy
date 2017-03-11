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

lemma tsum6_h2tsum5_h: "Fin n < #(tsscanl_h op + 0\<cdot>s) \<longrightarrow> snth n (tsscanl_h op + 0\<cdot>s) = snth n (tsum5_h 0\<cdot>s)"
apply (induction n arbitrary: s)
apply (smt shd1 snth_shd surj_scons tsscanl_h_empty tsscanl_h_scons_tick tsscanl_h_shd tsum5_h_shd_2 tsum5_shd)
sorry

lemma tsum62tsum5: "tsscanl_h plus 0\<cdot>s = tsum5_h 0\<cdot>s"
apply (rule snths_eq)
apply (simp)
by (simp add: tsum6_h2tsum5_h)

lemma "tsum6=tsum5"
by (simp add: tsscanl_def tsum5_def tsum6_def tsum62tsum5)

end