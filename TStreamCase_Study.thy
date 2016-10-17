(*  Title:        TStreamCase_Study.thy
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Tests with tStreams, mostly a few function definitions
                  and definition of Strong/Weak Causality on TStream functions
*)

chapter {* Timed Streams *} 

theory TStreamCase_Study

imports (* Streams *) TStreamTheorie
begin
default_sort countable







(* the tStream with just time *)
lift_definition tsInfTick :: "'m tstream" is "\<up>\<surd> \<infinity>"
by(simp add: ts_well_def)


lemma [simp]: "tsInfTick \<noteq> \<bottom>"
by(simp add: tsInfTick.rep_eq)

lemma [simp]: "tsAbs\<cdot>tsInfTick = \<epsilon>"
by(simp add: tsabs_insert tsInfTick.rep_eq sfilter_sdom_eps)

(* no message is transmitted *)
lemma [simp]: "tsDom\<cdot>tsInfTick = {}"
by(simp add: tsdom_insert tsInfTick.rep_eq)

lemma [simp]:  "tsDom\<cdot>(ts \<bullet> tsInfTick) = tsDom\<cdot>ts"
apply(cases "#\<surd>ts = \<infinity>")
apply simp
by(simp add: tsdom_tsconc less_le)

lemma [simp]: "#\<surd>tsInfTick = \<infinity>"
by(simp add: tstickcount_insert tsInfTick.rep_eq)

lemma [simp]: "#\<surd> (ts \<bullet> tsInfTick) = \<infinity>"
  apply(simp add: tstickcount_insert)
  apply(simp add: tsconc_insert)
  apply(cases "#\<surd> ts = \<infinity>")
   apply (simp add: tstickcount_insert)
  by (metis Abs_tstream_inverse mem_Collect_eq slen_sconc_snd_inf slen_sinftimes stream.con_rews(2) sup'_def tsInfTick.rep_eq tsInfTicks ts_well_conc tstickcount_insert up_defined)

lemma "tsInfTick \<down> 1 = (Abs_tstream ((\<up>\<surd>)))"
  apply (simp add: tsTake_def One_nat_def)
  apply(simp add: tstakefirst_insert tsInfTick.rep_eq)
  apply(subst sinftimes_unfold)
  by simp

lemma [simp]: "tsTakeFirst\<cdot>tsInfTick = Abs_tstream ((\<up>\<surd>))"
  apply(simp add: tstakefirst_insert tsInfTick.rep_eq)
  apply(subst sinftimes_unfold)
  by simp

lemma [simp]: "tsDropFirst\<cdot>tsInfTick = tsInfTick"
  apply(simp add: tsDropFirst_def "tsInfTick.rep_eq")
  apply(subst sinftimes_unfold)
  by (metis eq_onp_same_args sdrops_sinf sinftimes_unfold srtdw2drop tsInfTick.rsp tsInfTick_def)

lemma [simp]:"ts_well (n\<star>\<up>\<surd>)"
  by(induction n, simp_all)

lemma tsInfTick_take: "tsInfTick \<down> n = (Abs_tstream ((sntimes n (\<up>\<surd>))))"
  apply(induction n)
   apply simp
  by (simp add: tsConc_def tsTake.simps)

lemma tsInfTick_tsNth:  "tsNth n\<cdot>tsInfTick = Abs_tstream (\<up>\<surd>)"
  apply(induction n)
   apply (simp add: tsNth_def)
  by(simp add: tsNth_Suc)







(* Test with strong/weak Causality definition *)

definition tsWeakCausal:: "('m tstream \<Rightarrow> 'm tstream) \<Rightarrow> bool" where
"tsWeakCausal \<equiv> \<lambda>f .  \<forall>i ts1 ts2. (ts1 \<down>i = ts2 \<down> i) \<longrightarrow> (f ts1) \<down> i = (f ts2) \<down> i"

definition tsStrongCausal:: "('m tstream \<Rightarrow> 'm tstream) \<Rightarrow> bool" where
"tsStrongCausal \<equiv> \<lambda>f .  \<forall>i ts1 ts2. (ts1 \<down>i = ts2 \<down> i) \<longrightarrow> (f ts1) \<down> (Suc i) = (f ts2) \<down> (Suc i)"



lemma tsWeakCausalI: fixes f::"('m tstream \<Rightarrow> 'm tstream)"
  assumes "\<And>i ts1 ts2. (ts1 \<down>i = ts2 \<down> i) \<Longrightarrow> (f ts1) \<down>  i = (f ts2) \<down> i"
  shows "tsWeakCausal f"
by (metis assms tsWeakCausal_def)

lemma tsStrongCausalI: fixes f::"('m tstream \<Rightarrow> 'm tstream)"
  assumes "\<And>i ts1 ts2. (ts1 \<down>i = ts2 \<down> i) \<Longrightarrow> (f ts1) \<down> (Suc i) = (f ts2) \<down> (Suc i)"
  shows "tsStrongCausal f"
by (meson assms tsStrongCausal_def)




lemma tsStrong2Weak: "tsStrongCausal f \<Longrightarrow> tsWeakCausal f"
by (meson tsStrongCausal_def tsWeakCausalI tsSucTake)


lemma tsWeak_eq: assumes "tsWeakCausal f" and "x\<down>i = y\<down>i"
  shows "(f x)\<down>i = (f y) \<down>i"
by (meson assms(1) assms(2) tsWeakCausal_def)

lemma tsWeak2Mono: assumes "tsWeakCausal f" and "\<And>x. #\<surd>f x \<le> #\<surd> x"
  shows "monofun f"
  apply(rule monofunI)
  apply(rule ts_below)
  using assms(1) assms(2) tsWeak_eq trans_lnle tstake_less_below by blast

lemma tsMono2Weak: assumes "monofun f" and "\<And>x. #\<surd> x \<le> #\<surd> f x"
  shows "x \<down> i  = y \<down> i  \<Longrightarrow> (f x) \<down> i  = (f y) \<down> i"
  apply(induction i arbitrary: x y)
   apply simp
  apply(subst tstake_tsnth)
  apply(subst tstake_tsnth)
  by (smt assms(1) assms(2) min_def monofun_def tsTake_prefix tstake_below_eq tstake_len tstake_less_below tstake_tsnth)

lemma tsMono2Weak2: assumes "monofun f" and "\<And>x. #\<surd> x \<le> #\<surd> f x"
  shows "tsWeakCausal f"
using assms(1) assms(2) tsMono2Weak tsWeakCausalI by blast


lemma tsMonoEqWeak: "(\<And>x. #\<surd> x = #\<surd> f x) \<Longrightarrow> monofun f \<longleftrightarrow> tsWeakCausal f"
by (metis (mono_tags, lifting) order_refl tsMono2Weak tsWeak2Mono tsWeakCausal_def)


lemma [simp]: "tsWeakCausal f \<Longrightarrow> (\<And>x. #\<surd>f x \<le> #\<surd> x) \<Longrightarrow> chain Y \<Longrightarrow> chain (\<lambda>i. f (Y i))"
using ch2ch_monofun tsWeak2Mono by blast

lemma tsWeak_lub: assumes "tsWeakCausal f" and "\<And>x. #\<surd>f x = #\<surd> x" and "chain Y"
  shows "f (\<Squnion>i. Y i) = (\<Squnion>i. f (Y i))"
proof (cases "finite_chain Y")
  case True 
  have "\<And>x. #\<surd>f x \<le> #\<surd> x" by (simp add: assms(2)) 
  thus ?thesis by (metis assms(1) assms(2) assms(3) finite_chain_lub tsWeak2Mono True)  
next
  case False
  hence "#\<surd>(\<Squnion>i. Y i) = \<infinity>" using assms(3) ts_infinite_lub by blast
  have assms2: "\<And>x. #\<surd>f x \<le> #\<surd> x" by (simp add: assms(2)) 
  show ?thesis
  proof (rule ts_take_eq)
    fix n
    obtain i where "Fin n < #\<surd>Y i" by (meson False Suc_n_not_le_n assms(3) exist_tslen less2nat less_le_trans not_less)
    hence eq1: "(f (\<Squnion>i. Y i)) \<down> n = (f (Y i)) \<down> n"
      by (metis assms(1) assms(3) is_ub_thelub less_le tsWeak_eq tstake_less_below)
    have eq2: "(\<Squnion>i. f (Y i)) \<down> n =  (f (Y i)) \<down> n"
      by (metis \<open>Fin n < #\<surd> Y i\<close> assms(1) assms2 assms(2) assms(3) is_ub_thelub less_le monofun_def po_class.chain_def tsWeak2Mono tstake_less_below)
    show "(f (\<Squnion>i. Y i)) \<down> n  = (\<Squnion>i. f (Y i)) \<down> n " by (simp add: eq1 eq2) 
  qed
qed

lemma tsWeak2cont:assumes "tsWeakCausal f" and "\<And>x. #\<surd>f x = #\<surd> x"
  shows "cont f"
apply(rule contI2)
apply (simp add: assms(1) assms(2) tsWeak2Mono)
by (simp add: assms(1) assms(2) tsWeak_lub)

lemma tsWeak2cont2:assumes "\<And>x. #\<surd>f x = #\<surd> x"
  shows "tsWeakCausal f \<longleftrightarrow> cont f"
apply rule
using assms tsWeak2cont apply blast
by (simp add: assms cont2mono tsMono2Weak2)








lemma tsTick1_take [simp]:"Abs_tstream (\<up>\<surd>) \<down> 1 = Abs_tstream (\<up>\<surd>)"
  apply(simp add: tsTake_def2 One_nat_def)
  apply(subst tstakefirst_insert_rep_eq)
   apply(simp)
  by (metis sconc_snd_empty stwbl_f)

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
apply(simp add: tsTake_def2)
apply(simp add: tstakefirst_insert_rep_eq tsdropfirst_rep_eq)
by (metis (full_types) Abs_tstream_bottom_iff lscons_conv mem_Collect_eq stream.con_rews(2) stwbl_f sup'_def tick_msg up_defined)





(* A few example functions *)



(* the identity function is monotonic & weak causal, but not strong Causal *)

lemma "monofun (\<lambda>ts :: 'a tstream. ts)"
apply(rule monofunI)
by simp

lemma "tsWeakCausal (\<lambda>ts :: 'a tstream. ts)"
by (simp add: tsWeakCausalI)

lemma "\<not>tsStrongCausal (\<lambda>ts :: 'a tstream. ts)"
apply(auto simp add: tsStrongCausal_def)
by (metis Rep_cfun_strict1 tsTake.simps(1) ts_existsNBot tstake_bot tstake_fin2)





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







(* eine stark Causale, stetige function *)
setup_lifting type_definition_cfun
lift_definition delayFun :: "'m tstream \<rightarrow> 'm tstream" is
"\<lambda>ts . (Abs_tstream (\<up>\<surd>)) \<bullet> ts"
  by (simp add: Cfun.cfun.Rep_cfun)

lemma delayFun_dropFirst[simp]: "tsDropFirst\<cdot>(delayFun\<cdot>ts) = ts"
  apply(simp add: tsdropfirst_insert "delayFun.rep_eq")
  by(subst tsconc_rep_eq, auto)

lemma delayFun_takeFirst [simp]: "tsTakeFirst\<cdot>(delayFun\<cdot>ts) = Abs_tstream (\<up>\<surd>)"
  by (simp add: delayFun.abs_eq tsconc_rep_eq tstakefirst_insert)

lemma delayFun_takeN: "(delayFun\<cdot>ts1) \<down> (Suc n) = delayFun\<cdot>(ts1 \<down> n)"
  apply(subst tsTake.simps,auto)
    apply (metis below_bottom_iff delayFun_dropFirst strictI tsTake_prefix)
  by(simp add: delayFun_def)

lemma delayFun_sCausal: "(ts1 \<down> n) = (ts2 \<down> n) \<Longrightarrow> (delayFun\<cdot>ts1) \<down> (Suc n) = (delayFun\<cdot>ts2) \<down> (Suc n)"
by (simp add: delayFun_takeN)

lemma "tsStrongCausal (Rep_cfun delayFun)"
apply(rule tsStrongCausalI)
using delayFun_sCausal by blast


lemma delayFun_dom [simp]: "tsDom\<cdot>(delayFun\<cdot>ts) = tsDom\<cdot>ts"
by(simp add: delayFun_def tsdom_insert tsconc_rep_eq)

lemma delay_infTick [simp]: "#\<surd>ts = \<infinity> \<Longrightarrow> #\<surd> (delayFun\<cdot>ts) = \<infinity>"
apply(simp add: delayFun_def)
by (metis Abs_tstream_inverse mem_Collect_eq slen_sconc_snd_inf tsInfTicks ts_well_conc tsconc_insert)

lemma [simp]: "delayFun\<cdot>tsInfTick = tsInfTick"
apply(simp add: delayFun_def tsInfTick_def)
by (metis (no_types) Abs_tstream_inverse mem_Collect_eq sinftimes_unfold tick_msg tsInfTick.abs_eq tsInfTick.rep_eq tsconc_insert)


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





