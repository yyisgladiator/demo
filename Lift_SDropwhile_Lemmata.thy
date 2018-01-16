theory Lift_SDropwhile_Lemmata
  imports TStream
begin

(************************************************)
      text {*first lemma *}   
(************************************************)

(*the elements removed by tsDropWhile are a subset of the elements removed by tsFilter*)
lemma tsfilter_dwl1[simp]: "m \<notin> M \<Longrightarrow> (tsFilter M\<cdot>(tsDropWhile\<cdot>(Discr m)\<cdot>ts) = tsFilter M\<cdot>ts)"
  apply (induction ts)
  apply(simp_all)
  apply(simp add: tsdropwhile_delayfun tsfilter_delayfun)
  by (metis tsdropwhile_f tsdropwhile_t tsfilter_mlscons_nin)

(************************************************)
      text {*second lemma *}   
(************************************************)

(*the elements kept by tsFilter are a subset of the elements kept by tsDropWhile*)
lemma tsfilter_dwl2: "m \<notin> M \<Longrightarrow> (tsAbs\<cdot>(tsFilter M\<cdot>ts) \<noteq> \<bottom> \<Longrightarrow> tsAbs\<cdot>(tsDropWhile\<cdot>(Discr m)\<cdot>ts) \<noteq> \<bottom>)"
  by (metis tsabs_bot tsfilter_dwl1 tsfilter_strict tsfilter_tsabs)

(************************************************)
      text {* third lemma *}   
(************************************************)

(*tsDropWhile is idempotent *)
lemma tsdropwhile_idem: "tsDropWhile\<cdot>a\<cdot>(tsDropWhile\<cdot>a\<cdot>ts) = tsDropWhile\<cdot>a\<cdot>ts"
  apply(induction ts, simp_all)
  apply(simp add: tsdropwhile_delayfun)
  by (simp add: tsmlscons_lscons)

(*if the only message in a TStream with an arbitrary number of ticks is the argument of tsDropWhile,
then tsDropWhile produces a TStream containing only ticks*)
lemma [simp]: "tsAbs\<cdot>ts = (\<up>a) \<Longrightarrow> tsAbs\<cdot>(tsDropWhile\<cdot>(Discr a)\<cdot>ts)  = \<epsilon>"
  by (metis (full_types) lscons_conv sdropwhile_t sup'_def tsabs_bot tsdropwhile_strict tsdropwhile_tsabs)

(************************************************)
      text {*fourth lemma *}   
(************************************************)

(*Admissibility*)

(*Some propertys that may (or may not) be useful*)
lemma adm_help1: "tsAbs\<cdot>(ts1) = \<up>a \<Longrightarrow> (#\<^sub>tts1) = \<infinity> \<Longrightarrow> (#\<surd>ts1) = \<infinity>"
  by (simp add: tsInfTicks tslen_insert)

lemma adm_help6: "ts1 \<sqsubseteq> ts2 \<Longrightarrow> (#\<surd>ts2) = \<infinity> \<Longrightarrow> \<exists>ts3. ts2 = (ts1 \<bullet>\<surd> ts3 \<bullet>\<surd> tsInfTick)"
  by (metis ts_approxl3 tsconc_id)

lemma adm_help9: "tsAbs\<cdot>(ts1) = \<up>a \<Longrightarrow> (#\<^sub>tts1) < \<infinity> \<Longrightarrow> tsAbs\<cdot>(ts1 \<bullet>\<surd> ts2) = \<up>a \<Longrightarrow> tsAbs\<cdot>(ts2) = \<epsilon>"
  by (metis inject_scons sconc_snd_empty tsabs_conc tslen_insert)

lemma adm_help7: "ts1 \<sqsubseteq> ts2 \<Longrightarrow>(#\<^sub>tts1) < \<infinity> \<Longrightarrow> (#\<surd>ts2) = \<infinity> \<Longrightarrow> tsAbs\<cdot>(ts1) = \<up>a \<Longrightarrow> tsAbs\<cdot>(ts2) = \<up>a 
         \<Longrightarrow> ts2 = (ts1  \<bullet>\<surd> tsInfTick)"
  sorry

(*The lub of every infinite chain that has the same time abstraction as every element of the chain
is the first (or any) element concatenated with infinite ticks*)
lemma adm_help3: "chain Y \<Longrightarrow> \<not> finite_chain Y \<Longrightarrow> tsAbs\<cdot>(Y 0) = \<up>a \<Longrightarrow> tsAbs\<cdot>(\<Squnion>i. Y i) = \<up>a
         \<Longrightarrow> (\<Squnion>i. Y i) = ((Y 0)  \<bullet>\<surd> tsInfTick)"
  by (metis adm_help1 adm_help7 inf_ub is_ub_thelub order_less_le ts_infinite_fin ts_infinite_lub)

(*How to get from this to lemma adm_help15?*)
lemma adm_help16:"chain Y \<longrightarrow> \<not>finite_chain Y \<longrightarrow>
         (\<forall>i. tsAbs\<cdot>(Y i) = \<up>a) \<longrightarrow> (\<Squnion>i. Y i) = ((Y 0)  \<bullet>\<surd> tsInfTick)"
  by (smt adm_help3 contlub_cfun_arg lub_const lub_eq)

lemma adm_help8: "tsDropWhile\<cdot>(Discr x)\<cdot>ts1 = ts1 
        \<Longrightarrow> tsDropWhile\<cdot>(Discr x)\<cdot>(ts1 \<bullet>\<surd> Abs_tstream (\<up>\<surd>)) = (ts1 \<bullet>\<surd>  Abs_tstream (\<up>\<surd>))"
  sorry

lemma adm_help2: "tsDropWhile\<cdot>(Discr x)\<cdot>ts1 = ts1 
        \<Longrightarrow> tsDropWhile\<cdot>(Discr x)\<cdot>(ts1 \<bullet>\<surd> tsInfTick) = (ts1 \<bullet>\<surd> tsInfTick)" 
  sorry

(*Assume the chain is infinite*)
lemma adm_help15: "chain Y \<longrightarrow> \<not>finite_chain Y \<longrightarrow>
        (x \<noteq> a \<longrightarrow> (\<forall>i. tsAbs\<cdot>(Y i) = \<up>a \<longrightarrow> tsDropWhile\<cdot>(Discr x)\<cdot>(Y i) = Y i)) \<longrightarrow>
        x \<noteq> a \<longrightarrow> tsAbs\<cdot>(\<Squnion>i. Y i) = \<up>a \<longrightarrow> tsDropWhile\<cdot>(Discr x)\<cdot>(\<Squnion>i. Y i) = (\<Squnion>i. Y i)"
  sorry

(*Assume the chain is finite - trivial*)
lemma adm_help13: "chain Y \<longrightarrow> finite_chain Y \<longrightarrow>
        (x \<noteq> a \<longrightarrow> (\<forall>i. tsAbs\<cdot>(Y i) = \<up>a \<longrightarrow> tsDropWhile\<cdot>(Discr x)\<cdot>(Y i) = Y i)) \<longrightarrow>
        x \<noteq> a \<longrightarrow> tsAbs\<cdot>(\<Squnion>i. Y i) = \<up>a \<longrightarrow> tsDropWhile\<cdot>(Discr x)\<cdot>(\<Squnion>i. Y i) = (\<Squnion>i. Y i)"
  using l42 by fastforce     

(*Finally the Admissibility*)
lemma adm_help: "adm (\<lambda>b. x \<noteq> a \<longrightarrow> tsAbs\<cdot>b = \<up>a \<longrightarrow> tsDropWhile\<cdot>(Discr x)\<cdot>b = b)"
  apply(simp add: adm_def)
  using adm_help13 adm_help15 by blast

(*Final Lemma*)

lemma [simp]: "x \<noteq> a \<Longrightarrow> (tsAbs\<cdot>ts = \<up>a) \<Longrightarrow> tsDropWhile\<cdot>(Discr x)\<cdot>ts = ts"
  apply(induction ts, simp_all)
  using adm_def adm_help15 l42 apply fastforce
   apply (simp add: tsdropwhile_delayfun)
  by (metis inject_scons lscons_conv sup'_def tsabs_mlscons tsdropwhile_f)

end