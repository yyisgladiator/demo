(*  Title:        TStreamCase_Study.thy
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Tests with tStreams, mostly a few function definitions
                  and definition of Strong/Weak Causality on TStream functions
*)

chapter {* Timed Streams *} 

theory TStreamCase_Study

imports (* Streams *) TStream
begin
default_sort countable


lemma tsTick1_take [simp]:"Abs_tstream (\<up>\<surd>) \<down> 1 = Abs_tstream (\<up>\<surd>)"
  by(simp add: tsTake_def2 One_nat_def)


lemma tsTick1_take2 [simp]:"Abs_tstream (\<up>\<surd>) \<down> 2 = Abs_tstream (\<up>\<surd>)"
using tsTick1_take tstake_fin2 by fastforce



lemma tsTick2_take [simp]: "Abs_tstream (<[\<surd>, \<surd>]>) \<down> 1 = Abs_tstream (\<up>\<surd>)"
  apply(simp add: tsTake_def2 One_nat_def)
  apply(subst tstakefirst_insert_rep_eq)
   apply(simp)
  by (metis stwbl_f)

lemma tsTick2_take2 [simp]: "Abs_tstream (<[\<surd>, \<surd>]>) \<down> 2 = Abs_tstream (<[\<surd>, \<surd>]>)"
  apply(simp add: tsTake_def2)
  by (metis Rep_tstream_inverse Suc_1 tick_msg tsTick1_take tsconc_rep_eq1 tstake_tick)

lemma tsTick1_takeSuc [simp]: "Abs_tstream (\<up>\<surd>) \<down> Suc i  \<noteq> \<bottom>"
by(simp add: tsTake_def2)






(* A few example functions *)


(* Definiere eine Function, welche schwach Kausal ist, aber nicht monoton oder stark Causal *)
definition tsTest:: "'a tstream \<Rightarrow> 'a tstream" where
"tsTest ts \<equiv> if (ts=\<bottom>) then (Abs_tstream (\<up>\<surd>)) else \<bottom>"

lemma "\<not>monofun tsTest"
  by (auto simp add: monofun_def tsTest_def)

lemma "tsWeakCausal tsTest"
  apply(rule tsWeakCausalI)
  apply(rename_tac x y)
  apply(case_tac "x=\<bottom>\<or>y=\<bottom>")
   apply (auto simp add: tsTest_def)
   using tstakeBot apply blast
  using tstakeBot apply blast
done

lemma "\<not>tsStrongCausal tsTest"
apply(auto simp add: tsStrongCausal_def tsTest_def)
by (metis Rep_cfun_strict1 tsTake.simps(1) tsTick1_takeSuc)






(* Eine nicht schwach Kausale function, welche aber monoton/cont ist *)
lemma "\<not>tsWeakCausal (\<lambda>ts. tsDropFirst\<cdot>ts)"
proof -
  have f1: "tsDropFirst\<cdot>(Abs_tstream (<[\<surd>, \<surd>]>)) = Abs_tstream (\<up>\<surd>)"
    by (smt Abs_tstream_cases Abs_tstream_inverse append_Cons append_Nil list2s_0 list2s_Suc slistl5 stwbl_f sup'_def tick_msg tsConc_notEq tsTakeDropFirst tsconc_rep_eq1 tstakefirst_insert tstakefirst_len)
  have f2: "tsDropFirst\<cdot>(Abs_tstream (\<up>\<surd>)) = \<bottom>"
    by (smt Abs_tstream_inverse Rep_tstream_strict lscons_conv mem_Collect_eq stwbl_f sup'_def tick_msg tsConc_notEq tsTakeDropFirst tsconc_insert tstakefirst_insert_rep_eq tstakefirst_len)
  have "Abs_tstream (<[\<surd>, \<surd>]>) \<down> 1 = Abs_tstream (\<up>\<surd>) \<down> 1"
    by (smt Abs_tstream_inverse One_nat_def Rep_cfun_strict1 list2s_0 list2s_Suc lscons_conv mem_Collect_eq stwbl_f sup'_def tick_msg tsTake.simps(1) tsTake_def2 ts_well_conc tstakefirst_insert)
  thus " ?thesis"
    by (smt Fin_02bot One_nat_def Rep_tstream_strict f2 less2nat lnat.con_rews lnzero_def local.f1 min_def tsWeak_eq sinftimes_unfold slen_scons strict_sfilter strict_slen stwbl_f tsInfTick.rep_eq ts_0ticks tstake_bot tstake_len tstakefirst_bot tstakefirst_insert tstickcount_insert zero_le_one) 
qed


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
(*apply (metis Fin_0 Zero_not_Suc lsconc_suc2 stream.con_rews(2) strict_slen)
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





