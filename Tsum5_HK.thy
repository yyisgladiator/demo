(*  Title:  Tsum5_HK.thy
    Author: Hendrik Kausch
    e-mail: hendrik.kausch@rwth-aachen.de

    Description:  Definitons and lemmas for tsum5 
*)

theory Tsum5_HK
imports TStream StreamCase_Study
begin

(*Helper like h for sum5 but over nat event streams*)
primrec tsh :: "nat \<Rightarrow> nat \<Rightarrow> nat event stream \<Rightarrow> nat event stream" where
"tsh 0 p ts =  \<epsilon>" | (*maximal one non-variable argument required, so \<epsilon>-case must be encoded in the line below.*)
"tsh (Suc n) p ts = (if ts = \<epsilon> then \<epsilon> 
                        else(if shd ts= \<surd> then (\<up>\<surd> \<bullet> (tsh n p (srt\<cdot>ts)))
                                else (\<up>(Msg (p + (\<M>\<inverse> (shd ts))))) \<bullet> (tsh n (p +(\<M>\<inverse> (shd ts))) (srt\<cdot> ts))))"

(*Helper for tsum5 like sum5_helper for sum5 but over nat event streams*)
definition tsum5_helper :: " nat \<Rightarrow> nat event stream \<rightarrow> nat event stream" where
"tsum5_helper p \<equiv> \<Lambda> ts. (\<Squnion>i. tsh i p ts)"

(*Definition of sum5 over timed streams*)
definition tsum5:: "nat tstream \<Rightarrow> nat tstream" where
"tsum5 ts \<equiv> Abs_tstream (tsum5_helper 0\<cdot>(Rep_tstream ts))"



(*\<bottom> contains no natural message *)
lemma tsAbs_bot[simp]: "tsAbs\<cdot>\<bottom> = \<epsilon>"
by(simp add: tsAbs_def)

(*tsh of the empty stream is the empty stream*)
lemma tsh_bot: "tsh n p \<epsilon> = \<epsilon>"
by(induct_tac n,auto)

(*tsAbs of \<surd> and a timed stream is tsAbs of the timed stream*)
lemma AbsStsAbs_tick[simp]: "ts_well as \<Longrightarrow> tsAbs\<cdot> (Abs_tstream (\<up>(\<surd>)\<bullet>as)) = tsAbs\<cdot>(Abs_tstream as)"
by(simp add: tsabs_insert)

(*tsh returns \<surd>s immediately *)
lemma tsh_tick: "tsh (Suc n) p ((\<up>\<surd>)\<bullet>as) = (\<up>\<surd>)\<bullet> tsh n p as"
by(simp add: tsh_def)

(*tsAbs of \<surd> timed stream is the empty stream*)
lemma tsabs_abs_tick[simp]:"tsAbs\<cdot>(Abs_tstream (\<up>\<surd>)) = \<epsilon>"
by(simp add: tsAbs_def)

(*the vent stream with infinitely many \<surd> is well formed*)
lemma tswellinftick: "ts_well ((\<up>\<surd>)\<infinity>)"
by (simp add: ts_well_def)

(*Implies that tsh of (\<up>\<surd>)\<infinity> equals (\<up>\<surd>)\<infinity>*)
lemma tssum5_helpersinf: "tsh (Suc n) p (sinftimes(\<up>\<surd>)) = (\<up>\<surd>) \<bullet> tsh n p (sinftimes (\<up>\<surd>))"
by auto

(*tsh i works at most with the first i elements of the input*)
lemma contlub_tsh:
  "\<forall>s p. tsh i p (stake i\<cdot>s) = tsh i p s"
apply (induct_tac i, auto)
apply (rule_tac x=s in scases)
apply auto
apply (metis (no_types, lifting) inject_scons stake_Suc surj_scons)
apply (metis shd1 stake_Suc surj_scons)
apply (metis shd1 stake_Suc surj_scons)
apply (rule_tac x=s in scases)
by auto

(*helper for chain_tsh*)
lemma chain_tsh_helper: "xa\<noteq>\<epsilon> \<and> shd xa \<noteq>\<surd> \<Longrightarrow> tsh (Suc n) x (xa) = \<up>(\<M> (x + (\<M>\<inverse> (shd xa)))) \<bullet> tsh n (x + (\<M>\<inverse> (shd xa))) (srt\<cdot>xa)"
by simp

(*tsh i \<sqsubseteq> tsh (Suc i)*)
lemma chain_tsh: "chain tsh"
apply (rule chainI)
apply (subst fun_below_iff)+
apply (induct_tac i, auto)
apply(simp add: tsh_bot)+
apply (rule monofun_cfun_arg)
apply (erule_tac x="x" in allE)
apply presburger
apply (smt monofun_cfun_arg)
apply(simp add: tsh_bot)+
by (smt monofun_cfun_arg)+

(*helper for mono_tsh*)
lemma mono_tsh_helper: "x \<sqsubseteq> y \<and> x \<noteq> \<epsilon> \<Longrightarrow> shd x = shd y"
using lessD by fastforce

(* monotonicity of tsh *)
lemma mono_tsh: 
  "\<forall> x y q. x \<sqsubseteq> y \<longrightarrow> tsh n q x \<sqsubseteq> tsh n q y"
apply (induct_tac n, auto)
apply (drule lessD, erule disjE, simp)
apply (erule exE)+
apply (erule conjE)+
apply (simp, rule monofun_cfun_arg, simp)
using lessD apply fastforce
using lessD apply fastforce
using mono_tsh_helper
proof -
  fix na :: nat and x :: "nat event stream" and y :: "nat event stream" and q :: nat
  assume a1: "x \<sqsubseteq> y"
  assume a2: "x \<noteq> \<epsilon>"
  assume "\<forall>x y. x \<sqsubseteq> y \<longrightarrow> (\<forall>q. tsh na q x \<sqsubseteq> tsh na q y)"
  then show "\<up>(\<M> (q + (\<M>\<inverse> shd x))) \<bullet> tsh na (q + (\<M>\<inverse> shd x)) (srt\<cdot>x) \<sqsubseteq> \<up>(\<M> (q + (\<M>\<inverse> shd y))) \<bullet> tsh na (q + (\<M>\<inverse> shd y)) (srt\<cdot>y)"
    using a2 a1 by (simp add: mono_tsh_helper monofun_cfun)
qed

(*#(tsh n p s) = min(n, #s)*)
lemma cont_lub_tsum5_helper2:
  "\<forall>s p. stake n\<cdot> (tsh n p s) = tsh n p s "
by(induct_tac n,auto)

(* tsum5_helper is a continuous function *)
lemma cont_lub_tsum5_helper: "cont (\<lambda> s. \<Squnion>i. tsh i p s)" 
apply (rule cont2cont_lub)
apply (rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "p"])
apply (rule chainE)
apply (metis (no_types, lifting) chain_tsh)
apply (rule pr_contI)
apply (rule monofunI)
apply (rule mono_tsh [rule_format], assumption)
apply (rule allI)
apply (rule_tac x="i" in exI)
by (simp add: contlub_tsh)

(*Describes the unfolding of tsum5_helper if the first element of the stream is a natural message*)
lemma tsum5_helper_scons:"a\<noteq>\<surd> \<Longrightarrow> tsum5_helper n \<cdot>(\<up>a\<bullet>s) = (\<up>(\<M>(n+(\<M>\<inverse> a)))) \<bullet> (tsum5_helper (n+ (\<M>\<inverse> a))\<cdot>s)"  
apply (simp add: tsum5_helper_def)
apply (subst beta_cfun, rule cont_lub_tsum5_helper)+
apply (subst contlub_cfun_arg)
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "a"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
apply (subst lub_range_shift [where j="Suc 0", THEN sym])
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "a"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
by (simp add: chain_tsh_helper)

(*Describes the unfolding of tsum5_helper if the first element of the stream is a \<surd>*)
lemma tsum5_helper_scons_tick:"tsum5_helper n \<cdot>(\<up>\<surd>\<bullet>s) = \<up>\<surd> \<bullet> (tsum5_helper n \<cdot>s)"
apply (simp add: tsum5_helper_def)
apply (subst beta_cfun, rule cont_lub_tsum5_helper)+
apply (subst contlub_cfun_arg)
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "n"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
apply (subst lub_range_shift [where j="Suc 0", THEN sym])
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "n"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
by (simp add: chain_tsh_helper)

(*Other lemma with the same meaning as tsum5_helper_scons_tick*)
lemma tsum5_helper_scons_tick_2: "s=\<up>\<surd>\<bullet>as \<Longrightarrow> tsum5_helper n\<cdot>s = (\<up>\<surd>)\<bullet>(tsum5_helper n\<cdot> as)"
by (simp add: tsum5_helper_scons_tick)

(*Other lemma with the same meaning as tsum5_helper_scons*)
lemma tsum5_helper_scons_2:"shd s\<noteq>\<surd> \<and> s\<noteq>\<epsilon>\<Longrightarrow> tsum5_helper n \<cdot>s = (\<up>(\<M>(n+(\<M>\<inverse> shd s)))) \<bullet> (tsum5_helper (n+ (\<M>\<inverse> shd s))\<cdot>(srt\<cdot>s))"
using tsum5_helper_scons
by (metis surj_scons)

lemma tsum5_helper_scons_tick_alternative:"a=\<surd> \<Longrightarrow> tsum5_helper n \<cdot>(\<up>a\<bullet>s) = \<up>a \<bullet> (tsum5_helper n \<cdot>s)"
by(simp add: tsum5_helper_scons_tick)

(*tsum5_helper of an empty stream is an empty stream*)
lemma tsum5_empty[simp]: "tsum5_helper p\<cdot>\<epsilon> = \<epsilon>"
by (simp add: cont_lub_tsum5_helper tsh_bot tsum5_helper_def)

(*unfolding tsum5_helper with the definition*)
lemma tsum5_helper_unfold_tsh: "tsum5_helper n \<cdot>input = (\<Squnion>i. tsh i n input)"
apply (simp add:tsum5_helper_def)
by (simp add: cont_lub_tsum5_helper)

(*Shows that the message of a natural number of an nat event plus 0 is the nat event*)
lemma msg_plus0[simp]:fixes a::"nat event" shows" a\<noteq>\<surd> \<Longrightarrow>\<M> (0+(\<M>\<inverse> a)) = a"
by (metis add.left_neutral event.exhaust event.simps(4))

(*shd of tsum5_helper if the head is not \<surd>*)
lemma tsum5_helper_shd [simp]: "a\<noteq>\<surd> \<Longrightarrow> shd (tsum5_helper n \<cdot>(\<up>a \<bullet> as)) = \<M> (n+(\<M>\<inverse> a))"
by (simp add: tsum5_helper_scons)

(*shd of tsum5_helper if the head is not \<surd>*)
lemma tsum5_helper_shd_2 [simp]: "shd s\<noteq>\<surd> \<and> s\<noteq>\<epsilon> \<Longrightarrow> shd (tsum5_helper n \<cdot>s) = \<M> (n+(\<M>\<inverse> shd s))"
by (simp add: tsum5_helper_scons_2)

(*The head of tsum5_helper is the head of the input*)
lemma tsum5_shd: "shd (tsum5_helper 0\<cdot>ts) = shd ts"
apply(cases "ts= \<epsilon>")
apply simp
apply(cases "shd ts= \<surd>")
apply (metis shd1 surj_scons tsum5_helper_scons_tick)
by (metis msg_plus0 surj_scons tsum5_helper_shd)

(*unfolding of tsum5 with the definition*)
lemma tsum5_unfold: "tsum5 ts = Abs_tstream (tsum5_helper 0\<cdot> (Rep_tstream ts))"
by(simp add: tsum5_def)

(*A stream filtered by \<surd>s only contains \<surd>*)
lemma "#({\<surd>} \<ominus> s) = Fin (Suc n) \<Longrightarrow> ({\<surd>} \<ominus> s)= (\<up>\<surd>)\<bullet>(srt\<cdot>({\<surd>} \<ominus> s))"
by (metis Fin_02bot inject_Fin lnzero_def nat.simps(3) sfilter_resl2 singletonD slen_empty_eq surj_scons)

(*#(tsum5_helper s)is at least the length of s*)
lemma tsum5_helper_slen2: "#s \<le> #(tsum5_helper a\<cdot>s)"
apply (rule spec [where x = a])
apply (rule ind [of _ s], auto)
apply(subst lnle_def, simp del: lnle_conv)
by (smt lnsuc_lnle_emb slen_scons tsum5_helper_scons tsum5_helper_scons_tick)

(*The rest of tsum5_helper s is tsum5_helper (srt s) if the head of s is a \<surd>*)
lemma tsum5_helper_srt_tick: "shd s=\<surd> \<Longrightarrow>srt\<cdot>(tsum5_helper n \<cdot>s) = tsum5_helper n\<cdot> (srt\<cdot>s)"
by (metis (no_types, lifting) inject_scons lshd_updis stream.sel_rews(2) stream.sel_rews(3) surj_scons tsum5_empty tsum5_helper_scons_tick)

(*Unfolding the rest of tsum5_helper if the head is not a \<surd>*)
lemma tsum5_helper_srt: "shd s\<noteq>\<surd> \<Longrightarrow>srt\<cdot>(tsum5_helper n \<cdot>s) = tsum5_helper (n+(\<M>\<inverse> shd s))\<cdot> (srt\<cdot>s)"
apply(cases "s=\<epsilon>")
apply simp
using tsum5_helper_scons
proof -
  assume a1: "s \<noteq> \<epsilon>"
  assume a2: "shd s \<noteq> \<surd>"
  have f3: "\<up>(shd s) \<bullet> srt\<cdot>s = s"
    using a1 by (metis surj_scons)
  have "\<And>e s. updis (e::nat event) \<noteq> \<bottom> \<or> (\<epsilon>::nat event stream) = s"
    by simp
  then show ?thesis
    using f3 a2 a1 by (metis lscons_conv stream.sel_rews(5) tsum5_helper_scons)
qed

(*tsum5_helper has the length of the input*)
lemma tsum5_helper_slen[simp]: "#(tsum5_helper n\<cdot>s) = #s"
apply (rule spec [where x = n])
apply (rule ind [of _ s], auto)
using tsum5_helper_scons
by (metis slen_scons tsum5_helper_scons_tick)

(*Unfolds tsum5_helper with a \<up>(Msg m) as the input*)
lemma [simp]: "a\<noteq>\<surd> \<Longrightarrow> tsum5_helper n\<cdot>(\<up>a) = (\<up>(\<M>(n+(\<M>\<inverse> a))))"
by (metis lscons_conv sup'_def tsum5_empty tsum5_helper_scons)


(*Test of tsum5*)

(*the test nat event stream is well formed*)
lemma tswell_test: "ts_well ((<[n1,\<surd>,n2,\<surd>,\<surd>,n3]>) \<bullet> (sinftimes(\<up>\<surd>)))"
by(simp add: ts_well_def)

(*Result of the first part of the teststream with tsum5_helper 0*)
lemma tsum5_helper_test_helper1: "tsum5_helper 0\<cdot>(<[\<M> 1,\<surd>,\<M> 2,\<surd>,\<surd>,\<M> 4]>) =(<[\<M> 1,\<surd>,\<M> 3,\<surd>,\<surd>,\<M> 7]>)"
by (simp add: tsum5_helper_scons tsum5_helper_scons_tick)

(*result of the last part of the teststream with tsum5_helper n*)
lemma tsum5_helper_test_helper2: "tsum5_helper n \<cdot>(sinftimes(\<up>\<surd>)) = sinftimes(\<up>\<surd>)"
by (metis s2sinftimes sinftimes_unfold tsum5_helper_scons_tick)

(*result of the teststream with tsum5_helper 0*)
lemma tsum5_helper_test: "tsum5_helper 0 \<cdot>((<[\<M> 1,\<surd>,\<M> 2,\<surd>,\<surd>,\<M> 4]>) \<bullet> (sinftimes(\<up>\<surd>))) = ((<[\<M> 1,\<surd>,\<M> 3,\<surd>,\<surd>,\<M> 7]>) \<bullet> (sinftimes(\<up>\<surd>)))"
using tsum5_helper_test_helper1 tsum5_helper_test_helper2
by (simp add: tsum5_helper_scons tsum5_helper_scons_tick)

(*Tests the output of tsum5*)
lemma tssum5_test:"tsum5 (Abs_tstream ((<[\<M> 1, \<surd>, \<M> 2, \<surd>, \<surd>, \<M> 4]>) \<bullet> (sinftimes(\<up>\<surd>))))
 =(Abs_tstream ((<[\<M> 1,\<surd>,\<M> 3,\<surd>,\<surd>,\<M> 7]>) \<bullet> (sinftimes(\<up>\<surd>))))"
apply(simp add: tsum5_unfold)
apply (subst Rep_Abs)
using tswell_test apply auto
using tsum5_helper_test_helper2
by (simp add: tsum5_helper_scons tsum5_helper_scons_tick)


(*tsAbs(tsum5 ts) = sum5(tsAbs ts)*)


(*tsum5_helper of a ts_well \<up>a is \<up>a*)
lemma tsum5_helper_one[simp]: "ts_well (\<up>a) \<Longrightarrow> tsum5_helper n\<cdot>(\<up>a) = \<up>(a)"
apply(cases "a\<noteq>\<surd>")
apply (simp add: tsOneTick)
apply auto
apply(insert tsum5_helper_scons_tick [of n \<epsilon>])
by simp

(*Length of tsAbs ts of a timedstream ts*)
lemma tsAbs_len[simp]: "ts_well s \<Longrightarrow> #(tsAbs\<cdot>(Abs_tstream s)) = #({e. e\<noteq>\<surd>}\<ominus> s)"
by(subst tsabs_insert, simp)

(*Length of tsum5_helper of a event stream without ticks is eqaul to the length of sum5 of tsAbs*)
lemma tsum5_helper_sfilter_len: "ts_well s \<Longrightarrow> #(tsum5_helper n\<cdot>({e. e\<noteq>\<surd>}\<ominus>s)) = #(sum5\<cdot>(tsAbs\<cdot>(Abs_tstream s)))"
by simp

(*sum5_helper unfolding when the head of the stream is 0 is the parameter concatenated to sum5_helper with the rest of the stream*)
lemma tsum5_unfold_tsum5: "tsum5_helper n\<cdot>(\<up>(\<M> 0) \<bullet> s) =\<up>(\<M> (0+n)) \<bullet> tsum5_helper n \<cdot>(s)"
apply(subst tsum5_helper_scons)
apply simp
by simp

(*the (Suc nth) element of sum5_helper when the head of the stream is 0 is the nth element of sum5_helper with the rest stream*)
lemma test2_tsum5_helper_help: "Fin n < #s \<longrightarrow> snth (Suc n) (tsum5_helper m \<cdot>(\<up>(\<M> 0) \<bullet>s)) = snth n (tsum5_helper m \<cdot>s)"
apply(induction n)
apply(subst tsum5_unfold_tsum5)
apply simp
by (simp add: tsum5_unfold_tsum5)

(*the (Suc nth) element of tsum5_helper when the head of the stream is \<surd> is the nth element of tsum5_helper with the rest stream*)
lemma tsum5_suc_snth_tick:"Fin n < #s \<and> shd s =\<surd> \<Longrightarrow> snth (Suc n) (tsum5_helper m\<cdot>s) = snth n (tsum5_helper m\<cdot>(srt\<cdot>s))"
apply(subst tsum5_helper_scons_tick_2)
apply auto
by (metis Fin_0 less_le lnle_Fin_0 strict_slen surj_scons)

(**the (Suc nth) element of tsum5_helper m s when the head of the stream is not \<surd> is the nth element of tsum5_helper (m + shd s)  with the rest stream**)
lemma tsum5_suc_snth:"Fin n < #s \<and> shd s \<noteq>\<surd> \<and> s\<noteq>\<epsilon> \<Longrightarrow> snth (Suc n) (tsum5_helper m\<cdot>s) = snth n (tsum5_helper (m+ \<M>\<inverse> shd s)\<cdot>(srt\<cdot>s))"
apply(subst tsum5_helper_scons_2)
by auto

(*\<M>\<inverse> of \<M> a is a*)
lemma[simp]:"\<M>\<inverse> (\<M> a) = a "
by simp

(*the (Suc nth) element of tsum5_helper m s of a stream without \<surd>s is the nth element of tsum5_helper (m+ shd s) with the rest stream*)
lemma tsum5_sfilter_snth_helper:"Fin n < #({e. e\<noteq>\<surd>}\<ominus> s) \<and> ({e. e\<noteq>\<surd>}\<ominus> s)\<noteq>\<epsilon> \<Longrightarrow> snth (Suc n) (tsum5_helper m\<cdot>({e. e\<noteq>\<surd>}\<ominus> s)) = snth n (tsum5_helper (m+ \<M>\<inverse> shd ({e. e\<noteq>\<surd>}\<ominus> s))\<cdot>(srt\<cdot>({e. e\<noteq>\<surd>}\<ominus> s)))"
apply(subst tsum5_helper_scons_2)
using sfilter_ne_resup apply auto[1]
by auto

(*sfilter_lemmas*)
lemma sfilter_filtered: "({a} \<ominus> ({e. e \<noteq> a} \<ominus> s)) = \<epsilon>"
using ex_snth_in_sfilter_nempty by auto

lemma sfilter_length_srt: "#({a}\<ominus> (srt\<cdot>s)) \<le> #({a}\<ominus> s)"
by (metis (no_types, lifting) eq_iff less_lnsuc sfilter_in sfilter_nin slen_scons stream.sel_rews(2) surj_scons)

(*helper for tsum5_helper_sfilter_snth*)
lemma sfilter_filtered_len_srt: "({a} \<ominus> (srt\<cdot>({e. e \<noteq> a} \<ominus> s))) = \<epsilon>"
by (metis (mono_tags, lifting) mem_Collect_eq sdom_sfilter1 sfilter2dom sfilter_srtdwl3)

(*The nat of snth nat event of tsum5_helper m s is the snth of tsum5_helper 0 s + m*)
lemma tsum5_sfilter_snth_unfold:"Fin n < #s \<and> #({\<surd>}\<ominus> s) = 0 \<Longrightarrow> \<M>\<inverse> snth n (tsum5_helper m\<cdot>s) = \<M>\<inverse> snth n (tsum5_helper 0\<cdot>s) + m"
apply(induction n arbitrary: m s, simp)
apply(subst tsum5_helper_scons_2)
apply (metis lnsuc_neq_0_rev sfilter_in singletonI slen_empty_eq slen_scons surj_scons)
apply (subst tsum5_helper_shd_2)
apply (metis lnsuc_neq_0_rev sfilter_in singletonI slen_empty_eq slen_scons surj_scons)
apply simp
apply simp
apply(simp add: snth_rt)
apply(insert tsum5_helper_srt, auto)
by (smt Fin_Suc add.commute add.left_commute insert_iff less_imp_not_less lnle_Fin_0 lnsuc_lnle_emb lscons_conv not_less old.nat.distinct(2) ord_eq_less_trans sfilter_in sfilter_nin slen_empty_eq slen_scons stream.con_rews(2) surj_scons)


(*without \<surd>s in stream tsum5_helper unfolding the snth+1 element *)
lemma tsum5_helper_sfilter_snth:"Fin (Suc n) < #({e. e\<noteq>\<surd>}\<ominus> s) \<and> ({e. e\<noteq>\<surd>}\<ominus> s)\<noteq>\<epsilon> \<Longrightarrow> 
\<M>\<inverse> snth (Suc n) (tsum5_helper m\<cdot>({e. e\<noteq>\<surd>}\<ominus> s)) = \<M>\<inverse> snth n (tsum5_helper 0\<cdot>(srt\<cdot>({e. e\<noteq>\<surd>}\<ominus> s))) +(m+ \<M>\<inverse> shd ({e. e\<noteq>\<surd>}\<ominus> s))"
apply(subst tsum5_sfilter_snth_helper)
apply simp
apply (metis Fin_leq_Suc_leq Suc_n_not_le_n less2nat_lemma less_le)
apply(subst tsum5_sfilter_snth_unfold)
apply(subst sfilter_filtered_len_srt, simp)
apply (metis Fin_Suc lnsuc_lnle_emb not_less slen_scons surj_scons)
by simp

lemma tsum5_sfilter_snth:"Fin (Suc n) < #({e. e\<noteq>\<surd>}\<ominus> s) \<and> ({e. e\<noteq>\<surd>}\<ominus> s)\<noteq>\<epsilon> \<Longrightarrow> 
\<M>\<inverse> snth (Suc n) (tsum5_helper 0\<cdot>({e. e\<noteq>\<surd>}\<ominus> s)) = \<M>\<inverse> snth n (tsum5_helper 0\<cdot>(srt\<cdot>({e. e\<noteq>\<surd>}\<ominus> s))) +\<M>\<inverse> shd ({e. e\<noteq>\<surd>}\<ominus> s)"
by(insert tsum5_helper_sfilter_snth [of n s 0], simp)

lemma sum3_snth_2:"Fin (Suc n) < #s \<Longrightarrow> snth (Suc n) (sum3\<cdot>s) = snth n (sum3\<cdot>(srt\<cdot>s)) + shd s"
apply(insert sum3_snth[of n s 0], simp)
by (metis less_le lnle_Fin_0 nat.distinct(1) not_less slen_rt_ile_eq strict_slen sum4_snth sum52sum3 sum52sum4 surj_scons)

(*special case for snth 0 (smap f\<cdot>s)*)
lemma [simp]:"s\<noteq> \<epsilon> \<Longrightarrow> shd (smap f\<cdot>s) = f (shd s)"
apply(insert smap_snth_lemma [of 0], simp)
by (smt shd1 smap_scons surj_scons)

(*another variant of sum4_snth*)
lemma sum4_snth_2:"Fin (Suc n) < #s \<Longrightarrow> snth (Suc n) (sum4\<cdot>s) = snth n (sum4\<cdot>(srt\<cdot>s)) + shd s"
using sum4_snth
by (metis less_le lnle_Fin_0 nat.distinct(1) not_less slen_rt_ile_eq strict_slen surj_scons)

lemma sfilter_sfilter[simp]: "{a}\<ominus>{a}\<ominus>s = {a}\<ominus>s"
by simp

lemma tsum5_helper_snth2sum3_snth:"Fin n < #({e. e\<noteq>\<surd>}\<ominus> s) \<and> ({e. e\<noteq>\<surd>}\<ominus> s)\<noteq>\<epsilon> \<Longrightarrow>
 \<M>\<inverse> snth n (tsum5_helper 0\<cdot>({e. e\<noteq>\<surd>}\<ominus> s)) = snth n (sum3\<cdot>(smap (\<lambda>e. \<M>\<inverse> e)\<cdot>({e. e\<noteq>\<surd>}\<ominus> s)))"
apply(induction n arbitrary: s, simp+)
apply(subst tsum5_helper_shd_2, simp)
using sfilter_ne_resup apply auto[1]
apply simp
apply(subst tsum5_sfilter_snth)
apply linarith
apply(subst sum3_snth_2)
apply simp
apply simp
by (smt inject_scons less2lnleD lnle_Fin_0 nat.distinct(1) not_less sfilter_srtdwl3 slen_rt_ile_eq slen_smap smap1 smap_split strict_slen surj_scons)

(*
(*Describes the snth element of tum5_helper with the snth element of the stream*)
lemma tsum5_test2:"Fin (Suc n) < #({e. e \<noteq> \<surd>} \<ominus> s) \<Longrightarrow> \<M>\<inverse> snth (Suc n) (tsum5_helper 0\<cdot>({e. e \<noteq> \<surd>} \<ominus> s)) = \<M>\<inverse> snth (Suc n) ({e. e \<noteq> \<surd>} \<ominus> s) + \<M>\<inverse> snth n (tsum5_helper 0\<cdot>({e. e \<noteq> \<surd>} \<ominus> s))"
apply(simp add: snth_rt)
apply(subst tsum5_helper_srt)
apply (metis (mono_tags, lifting) less_le lnle_Fin_0 mem_Collect_eq nat.distinct(1) sfilter_ne_resup strict_slen)
apply simp
apply(induction n, simp+)
apply (smt Fin_02bot Fin_Suc Inf'_def Inf'_neq_0_rev add.commute add.left_neutral event.distinct(1) event.inject fix_strict lnzero_def lscons_conv mem_Collect_eq msg_plus0 not_less_iff_gr_or_eq sfilter_ne_resup sfilter_sinftimes_in sfilter_srtdwl3 shd1 sinftimes_unfold slen_scons smono_slen_rt_lemma stream.con_rews(2) stream.sel_rews(2) stream.sel_rews(5) strict_icycle strict_slen sup'_def tsum5_helper_shd_2 tsum5_shd)
apply(insert tsum5_helper_srt[of s])
apply (simp add: snth_rt)
sorry

(*without \<surd>s in stream tsum5_helper 0 behaves like sum4*)
lemma tsum5_helper_snth2sum4_snth:"Fin n < #({e. e\<noteq>\<surd>}\<ominus> s) \<and> ({e. e\<noteq>\<surd>}\<ominus> s)\<noteq>\<epsilon> \<Longrightarrow>
 \<M>\<inverse> snth n (tsum5_helper 0\<cdot>({e. e\<noteq>\<surd>}\<ominus> s)) = snth n (sum4\<cdot>(smap (\<lambda>e. \<M>\<inverse> e)\<cdot>({e. e\<noteq>\<surd>}\<ominus> s)))"
apply(induction n, simp+)
apply(subst tsum5_helper_shd_2, simp)
using sfilter_ne_resup apply auto[1]
apply simp
apply(subst tsum5_test2)
apply linarith
apply(subst test2)
apply (metis slen_smap)
apply(subst smap_snth_lemma, blast)
by (metis Fin_leq_Suc_leq Suc_n_not_le_n less2nat_lemma less_le snth_scons)
*)

(*helper for tsum52sum4_helper*)
lemma tsum5_helper2sum3:"smap (\<lambda>e. \<M>\<inverse> e)\<cdot> (tsum5_helper 0\<cdot>({e. e\<noteq>\<surd>}\<ominus> s)) = sum3\<cdot>(smap (\<lambda>e. \<M>\<inverse> e)\<cdot>({e. e\<noteq>\<surd>}\<ominus> s))"
apply(rule snths_eq, simp)
apply auto
apply(subst smap_snth_lemma)
apply simp
apply(rule tsum5_helper_snth2sum3_snth, auto)
by (metis Fin_0 less_le lnle_Fin_0)



(*taking only \<surd>s of tsum5_helper is the same as taking \<surd>s of the input*)
lemma tsum5_ticknum_helper[simp]: "({\<surd>} \<ominus> tsum5_helper n\<cdot>ts) =({\<surd>} \<ominus> ts) "
apply(cases "ts=\<epsilon>", simp)
apply(induction ts arbitrary: n,auto)
proof -
  fix u :: "nat event discr\<^sub>\<bottom>" and ts :: "nat event stream" and n:: nat
  assume a1: "u\<noteq>\<bottom>"
  assume a2: "(\<And>n. ts \<noteq> \<epsilon> \<Longrightarrow> {\<surd>} \<ominus> tsum5_helper n\<cdot>ts = {\<surd>} \<ominus> ts)"
  then show "{\<surd>} \<ominus> tsum5_helper n\<cdot>(u && ts) = {\<surd>} \<ominus> u && ts"
  apply(insert a1 a2)
  apply(cases "u=updis \<surd>")
  apply(insert lscons_conv[of \<surd> ts])
  apply(subst tsum5_helper_scons_tick_2, auto)
  using a2 apply force
  apply(subst tsum5_helper_scons_2)
  apply (metis stream.con_rews(2) stream.injects stream.sel_rews(5) surj_scons)
  apply simp
  using a2
  by (metis (no_types, lifting) sfilter_nin singletonD stream.con_rews(2) stream.sel_rews(4) stream.sel_rews(5) surj_scons tsum5_empty)
qed

(*There are as much \<surd>s in the output as there are in the Input*)
lemma tsum5_ticknum[simp]:"#({\<surd>} \<ominus> tsum5_helper 0\<cdot>ts) =#({\<surd>} \<ominus> ts)"
by simp

(*
lemma sfoot_tsum5: "sfoot (tsum5_helper n\<cdot>(s \<bullet> \<up>\<surd>)) = \<surd>"
apply(simp add: sfoot_def)
sorry
*)

lemma helper3:"(\<exists>x. srt\<cdot>(tsum5_helper 0\<cdot>s) = tsum5_helper x\<cdot>(srt\<cdot>s))"
apply(cases "s=\<epsilon>", simp)
apply(cases "shd s=\<surd>")
apply(subst tsum5_helper_scons_tick_2, auto)
using surj_scons apply fastforce
by(subst tsum5_helper_scons_2, auto)

lemma helper4:"(\<exists>x. sdrop (Suc n)\<cdot>(tsum5_helper 0\<cdot>s) = sdrop n\<cdot> (tsum5_helper x\<cdot>(srt\<cdot>s)))"
apply(subst sdrop_forw_rt)
using helper3
by metis

lemma helper2:"(\<exists>x. sdrop n\<cdot>(tsum5_helper 0\<cdot>s) = tsum5_helper x\<cdot>(sdrop n\<cdot>s))"
apply(induction n arbitrary: s, auto)
using helper4
by (smt iterate_Suc lscons_conv sdrop_def stream.sel_rews(2) stream.sel_rews(5) surj_scons tsum5_empty tsum5_helper_scons tsum5_helper_srt_tick up_defined)


lemma helper132:" (\<exists>x. snth n (tsum5_helper 0\<cdot>s) = shd (tsum5_helper x\<cdot> (sdrop n\<cdot> s)))"
apply(simp add: snth_def)
using helper2 by metis

lemma balala:" snth n s=\<surd> \<Longrightarrow> snth n (tsum5_helper 0\<cdot>s) =\<surd>"
apply(simp add: snth_def)
apply(insert helper132[of n s])
apply auto
by (metis shd1 snth_def surj_scons tsum5_empty tsum5_helper_scons_tick)


(*if the input has a \<surd> at the end so does the output*)
lemma tsum5_sfoot_helper:"#s<\<infinity> \<Longrightarrow> sfoot (tsum5_helper 0\<cdot>(s \<bullet> \<up>\<surd>)) = \<surd>"
apply(simp add: sfoot_def)
apply(subst balala, auto)
by(insert sfoot12[of s \<surd>],simp add: sfoot_def)

(*if the input of tsum5_helper is well formed so is the output*)
lemma tswell_tsum5:"ts_well ts \<Longrightarrow> ts_well (tsum5_helper 0\<cdot>ts)"
apply(cases "#ts=\<infinity>")
apply(simp add: ts_well_def, auto)+
using tsum5_sfoot_helper
by (metis inf_ub less_le sconc_fst_inf sfoot2)

(*If you filter out \<surd>s the length of the input stream is equal to the length of the output stream*)
lemma sfilter_in_tsum_helper_len[simp]: " #({e. e \<noteq> \<surd>} \<ominus> tsum5_helper n\<cdot>ts) = #({e. e \<noteq> \<surd>} \<ominus> ts)"
apply(induction ts arbitrary: n, auto)
proof -
  fix u :: "nat event discr\<^sub>\<bottom>" and ts :: "nat event stream" and n:: nat
  assume a1: "u\<noteq>\<bottom>"
  assume a2: "(\<And>n. #({e. e \<noteq> \<surd>} \<ominus> tsum5_helper n\<cdot>ts) = #({e. e \<noteq> \<surd>} \<ominus> ts))"
  then show "#({e. e \<noteq> \<surd>} \<ominus> tsum5_helper n\<cdot>(u && ts)) = #({e. e \<noteq> \<surd>} \<ominus> u && ts)"
  apply(insert a1 a2)
  apply(cases "u=updis \<surd>")
  apply(insert lscons_conv[of \<surd> ts])
  apply(subst tsum5_helper_scons_tick_2, auto)
  apply(subst tsum5_helper_scons_2)
  apply (metis stream.con_rews(2) stream.injects stream.sel_rews(5) surj_scons)
  apply simp
by (smt lshd_updis mem_Collect_eq sfilter_in slen_scons stream.con_rews(2) stream.sel_rews(4) stream.sel_rews(5) surj_scons)
qed

(*it does not matter if i filter out the \<surd>s in at the input or the output*)
lemma sfilter_in_tsum5:"{e. e \<noteq> \<surd>} \<ominus> tsum5_helper n\<cdot>ts = tsum5_helper n\<cdot>({e. e \<noteq> \<surd>} \<ominus> ts)"
apply(cases "ts=\<epsilon>",simp)
apply(induction ts arbitrary: n, auto)
proof -
  fix u :: "nat event discr\<^sub>\<bottom>" and ts :: "nat event stream" and n:: nat
  assume a1: "u\<noteq>\<bottom>"
  assume a2: "(\<And>n. ts \<noteq> \<epsilon> \<Longrightarrow> {e. e \<noteq> \<surd>} \<ominus> tsum5_helper n\<cdot>ts = tsum5_helper n\<cdot>({e. e \<noteq> \<surd>} \<ominus> ts))"
  then show "{e. e \<noteq> \<surd>} \<ominus> tsum5_helper n\<cdot>(u && ts) = tsum5_helper n\<cdot>({e. e \<noteq> \<surd>} \<ominus> u && ts)"
  apply(insert a1 a2)
  apply(cases "u=updis \<surd>")
  apply(insert lscons_conv[of \<surd> ts])
  apply(subst tsum5_helper_scons_tick_2, auto)
  apply fastforce
  apply(subst tsum5_helper_scons_2)
  apply (metis stream.con_rews(2) stream.injects stream.sel_rews(5) surj_scons)
  apply simp
  by (smt mem_Collect_eq sfilter_in stream.con_rews(2) stream.injects stream.sel_rews(5) strict_sfilter surj_scons tsum5_empty tsum5_helper_scons)
qed

(*helper for tsum52sum4*)
lemma tsum52sum3_helper:"smap (\<lambda>e. \<M>\<inverse> e)\<cdot> ({e. e\<noteq>\<surd>}\<ominus> (Rep_tstream (tsum5 ts))) = sum3\<cdot>(smap (\<lambda>e. \<M>\<inverse> e)\<cdot>({e. e\<noteq>\<surd>}\<ominus> (Rep_tstream ts)))"
apply(subst tsum5_unfold)
apply(subst Rep_Abs)
using tswell_tsum5 apply auto
apply(subst sfilter_in_tsum5)
apply(subst tsum5_helper2sum3)
by simp

(*tsum5 and sum4 work the same way over naturals*)
lemma tsum52sum3:"tsAbs\<cdot>(tsum5 ts) = sum3\<cdot>(tsAbs\<cdot>ts)"
apply(simp add: tsabs_insert)
by(rule tsum52sum3_helper)


(*definition tsum_nth like sum_nth*)
primrec tsum_nth:: "nat \<Rightarrow> nat event stream \<Rightarrow> nat" where
"tsum_nth 0 s = (if shd s=\<surd> then 0 else \<M>\<inverse> shd s)" |
"tsum_nth (Suc n) s = (if shd s=\<surd> then 0 + tsum_nth n (srt\<cdot>s) else (\<M>\<inverse>(shd s)) + tsum_nth n (srt\<cdot>s))"

(**)
lemma tsum5_helper2tsum_nth:"Fin n< #s \<Longrightarrow> snth n (tsum5_helper 0\<cdot> s) = (case (snth n s) of Msg a \<Rightarrow> \<M> tsum_nth n s | \<surd> \<Rightarrow> \<surd>)"
apply(cases "snth n s =\<surd>")
apply(induction n arbitrary: s, simp add: tsum5_shd)
apply (simp add: snth_rt)
sorry

lemma "Fin n< #(Rep_tstream ts) \<Longrightarrow> snth n (Rep_tstream(tsum5 ts)) = (case (snth n (Rep_tstream ts)) of Msg a \<Rightarrow> \<M> tsum_nth n (Rep_tstream ts) | \<surd> \<Rightarrow> \<surd>) "
apply(simp add: tsum5_unfold)
apply(subst Rep_Abs)
using tswell_tsum5 apply simp
by(subst tsum5_helper2tsum_nth, simp+)


end
