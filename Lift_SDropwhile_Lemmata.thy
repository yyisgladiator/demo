theory Lift_SDropwhile_Lemmata
  imports TStream
begin

(************************************************)
      text {*first lemma *}   
(************************************************)

(*the elements removed by tsDropWhile are a subset of the elements removed by tsFilter*)
lemma tsfilter_dwl1[simp]: "m \<notin> M \<Longrightarrow> tsFilter M\<cdot>(tsDropWhile\<cdot>(Discr m)\<cdot>ts) = tsFilter M\<cdot>ts"
  apply (induction ts)
  apply(simp_all)
  apply(simp add: tsdropwhile_delayfun tsfilter_delayfun)
  by (metis tsdropwhile_f tsdropwhile_t tsfilter_mlscons_nin)

(************************************************)
      text {*second lemma *}   
(************************************************)

(*the elements kept by tsFilter are a subset of the elements kept by tsDropWhile*)
lemma tsfilter_dwl2: "m \<notin> M \<Longrightarrow> tsAbs\<cdot>(tsFilter M\<cdot>ts) \<noteq> \<bottom> \<Longrightarrow> tsAbs\<cdot>(tsDropWhile\<cdot>(Discr m)\<cdot>ts) \<noteq> \<bottom>"
  by (metis tsabs_bot tsfilter_dwl1 tsfilter_strict tsfilter_tsabs)

(************************************************)
      text {* third lemma *}   
(************************************************)

(*tsDropWhile is idempotent *)
lemma tsdropwhile_idem: "tsDropWhile\<cdot>a\<cdot>(tsDropWhile\<cdot>a\<cdot>ts) = tsDropWhile\<cdot>a\<cdot>ts"
  apply(induction ts, simp_all)
  apply(simp add: tsdropwhile_delayfun)
  by (simp add: tsmlscons_lscons)

(************************************************)
      text {*fourth lemma *}   
(************************************************)

(*if the only message in a TStream with an arbitrary number of ticks is the argument of tsDropWhile,
then tsDropWhile produces a TStream containing only ticks*)
lemma [simp]: "tsAbs\<cdot>ts = (\<up>a) \<Longrightarrow> tsAbs\<cdot>(tsDropWhile\<cdot>(Discr a)\<cdot>ts) = \<epsilon>"
  by (metis (full_types) lscons_conv sdropwhile_t sup'_def tsabs_bot tsdropwhile_strict tsdropwhile_tsabs)

lemma adm_tsdom_neq [simp]: "\<And>x. adm (\<lambda>xa. tsDom\<cdot>xa \<noteq> {x})"
  apply (rule admI)
  apply (simp add: contlub_cfun_fun contlub_cfun_arg lub_eq_Union)
  apply (simp add: tsdom_insert sdom_def)
  by (smt Collect_cong Sup_set_def imageE insertI1 mem_Collect_eq mem_simps(9) singletonD)

lemma[simp]: "tsDom\<cdot>ts = {a} \<Longrightarrow> tsAbs\<cdot>(tsDropWhile\<cdot>(Discr a)\<cdot>ts) = \<epsilon>"
  apply (induction ts arbitrary: a, simp_all)
  sorry

(************************************************)
      text {*fifth lemma *}   
(************************************************)

lemma adm_help1: "#(tsAbs\<cdot>ts) \<noteq> \<infinity> \<Longrightarrow> (#\<^sub>t ts) = \<infinity> \<Longrightarrow> (#\<surd> ts) = \<infinity>"
  by (simp add: tsInfTicks tslen_insert)

lemma [simp]: "x \<noteq> a \<Longrightarrow> (tsAbs\<cdot>ts = \<up>a) \<Longrightarrow> tsDropWhile\<cdot>(Discr x)\<cdot>ts = ts"
  apply (induction ts arbitrary: a x, simp_all)
  apply (rule adm_all)+
  apply (rule adm_imp, simp_all)+
  apply (rule admI)
  apply (metis (mono_tags, lifting) Fin_02bot Fin_Suc Fin_neq_inf bot_is_0 ch2ch_Rep_cfunR 
         contlub_cfun_arg inf_chainl4 l42 lscons_conv slen_scons strict_slen sup'_def)
  apply (simp add: tsdropwhile_delayfun)
  by (metis inject_scons lscons_conv sup'_def tsabs_mlscons tsdropwhile_f)

lemma [simp]: "x \<noteq> a \<Longrightarrow> tsDom\<cdot>ts = {a} \<Longrightarrow> tsDropWhile\<cdot>(Discr x)\<cdot>ts = ts"
  apply (induction ts arbitrary: a x, simp_all)
  sorry

end