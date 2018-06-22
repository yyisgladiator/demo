(*  Title:        tsynBundle.thy
    Author:       Dennis Slotboom
    E-Mail:       dennis.slotboom@rwth-aachen.de

    Description:  Time-synchronous stream bundles.
*)

chapter {* Time-Synchronous Stream Bundles *}

theory tsynBundle
imports tsynStream "../untimed/SB" "../UFun_Templates"

begin

default_sort message

(* ----------------------------------------------------------------------- *)
  section {* tsynbNull - Automaton *}
(* ----------------------------------------------------------------------- *)

(* ToDo: add descriptions. *)

lift_definition tsynbNull :: "channel \<Rightarrow> 'm tsyn SB" is
  "\<lambda>c. [c \<mapsto> \<up>null]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def)
    
lemma tsynbnull_ubdom [simp]: "ubDom\<cdot>(tsynbNull c) = {c}"
  by (simp add:tsynbNull.rep_eq ubdom_insert)

lemma tsynbnull_ubgetch [simp]: "tsynbNull c  .  c = \<up>null"
  by (simp add: tsynbNull.rep_eq ubgetch_insert)

lemma tsynbnull_ubconc [simp]:
  assumes "c \<in> ubDom\<cdot>sb"
  shows "ubConc (tsynbNull c)\<cdot>sb  .  c = \<up>null \<bullet> (sb  .  c)"
  by (simp add: assms ubConc_usclConc_eq usclConc_stream_def)
    
lemma tsynbnull_ubconc_sbrt [simp]:
  assumes "ubDom\<cdot>sb = {c}"
  shows "sbRt\<cdot>(ubConc (tsynbNull c)\<cdot>sb) = sb"
  apply (rule ub_eq)
  by (simp add: assms sbRt_def)+

(* ----------------------------------------------------------------------- *)
  section {* Definitions on Time-Synchronous Stream Bundles *}
(* ----------------------------------------------------------------------- *)

definition tsynbAbs :: "'a tsyn stream ubundle \<rightarrow> 'a stream ubundle option" where 
  "tsynbAbs \<equiv> \<Lambda> sb. (ubDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(sb  .  c1)]"

(* ----------------------------------------------------------------------- *)
  section {* Definitions of Time-Synchronous Test Bundles *}
(* ----------------------------------------------------------------------- *)

instantiation nat :: message
begin
  fun ctype_nat :: "channel \<Rightarrow> nat set" where 
  "ctype_nat c = range nat" 
  instance
    by (intro_classes)
end
 
lift_definition tsynbabsTestInput :: "nat tsyn stream ubundle " is 
  "[c1 \<mapsto> <[Msg (1 :: nat), null, Msg 2, Msg 1]>]"
  apply (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def)
  by (metis image_eqI nat_1 nat_2 numeral_2_eq_2 range_eqI)

lift_definition tsynbabsTestOutput :: "nat stream ubundle " is 
  "[c2 \<mapsto> <[(1 :: nat), 2, 1]>]"
  apply (simp add: ubWell_def usclOkay_stream_def)
  by (metis nat_1 nat_2 numeral_2_eq_2 range_eqI)

lemma tsynbabstestinput_ubdom: "ubDom\<cdot>tsynbabsTestInput = {c1}"
  by (simp add: ubDom_def tsynbabsTestInput.rep_eq)

(* ----------------------------------------------------------------------- *)
  section {* Lemmata on Time-Synchronous Stream Bundles *}
(* ----------------------------------------------------------------------- *)

lemma tsynbabs_ubwell [simp]:
  assumes "usclOkay c1 (s :: 'a tsyn stream)"
    and "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynAbs\<cdot>s)"
  shows "ubWell [c2 \<mapsto> tsynAbs\<cdot>s]"
  using assms
  by (simp add: ubWell_def domIff usclOkay_stream_def)

lemma tsynbabs_ubwell2 [simp]: 
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynAbs\<cdot>s)"  
    and "c1 \<in> ubDom\<cdot>sb"
  shows "ubWell [c2 \<mapsto> tsynAbs\<cdot>((sb :: 'a tsyn stream\<^sup>\<Omega>)  .  c1)]"
  by (metis assms tsynbabs_ubwell ubdom_channel_usokay ubgetch_insert)

lemma tsynbabs_ubdom:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynAbs\<cdot>s)"
    and "c1 \<in> ubDom\<cdot>sb"
  shows "ubDom\<cdot>(Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((sb :: 'a tsyn stream ubundle)  .  c1)]) = {c2}"
  using assms
  by (simp add: ubdom_insert)

lemma tsynbabs_mono [simp]:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynAbs\<cdot>s)"
  shows "monofun (\<lambda>sb :: 'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) 
                    \<leadsto> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(sb  .  c1)])"
  apply (fold ubclDom_ubundle_def)
  apply (rule monofunI)
  apply (case_tac "ubclDom\<cdot>x \<noteq> {c1}")
  apply (simp_all add: ubcldom_fix)
  apply (rule some_below)
  apply (rule ub_below)
  apply (simp add: ubdom_insert)
  apply (simp_all add: assms ubclDom_ubundle_def ubdom_below)
  by (simp add: assms fun_upd_same monofun_cfun_arg ubdom_below ubgetch_ubrep_eq)

(* ToDo: Improve *)

lemma tsynbabs_chain1[simp]: 
  assumes "\<forall> x::'a tsyn stream. usclOkay c1 x = usclOkay c2 (tsynAbs\<cdot>x)"
    shows "chain (Y:: nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>) \<Longrightarrow> ubDom\<cdot>(Y 0) = {c1} \<Longrightarrow> chain (\<lambda> i. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i . c1)])"
  apply(rule chainI)
  apply(rule ub_below)
  apply (simp add: assms  ubdom_ubrep_eq)
  apply (simp add: ubdom_ubrep_eq)
  apply (simp add: assms  ubdom_ubrep_eq)
  by (simp add: assms monofun_cfun_arg po_class.chainE ubgetch_ubrep_eq)

lemma tsynbabs_chain_lub[simp]: 
  assumes "\<forall> x::'a tsyn stream. usclOkay c1 x = usclOkay c2 (tsynAbs\<cdot>x)"
    shows "chain (Y:: nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>) \<Longrightarrow> ubDom\<cdot>(Lub Y) = {c1} \<Longrightarrow> chain (\<lambda> i. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((Y i) . c1)])"
  by (simp add: assms)
    
lemma tsynbabs_chain2: 
  assumes "\<forall> x::'a tsyn stream. usclOkay c1 x = usclOkay c2 (tsynAbs\<cdot>x)"
    shows "chain (Y:: nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>) \<Longrightarrow> chain(\<lambda> i. (ubDom\<cdot>(Y i) = {c1}) \<leadsto> (Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((Y i) . c1)]))"
  apply(rule chainI, simp)
  apply(rule impI, rule some_below, rule ub_below)
  apply (simp add: assms ubdom_ubrep_eq)
  by (simp add: assms monofun_cfun_arg po_class.chainE ubgetch_ubrep_eq)
    
lemma tsynbabs_lub[simp]: 
  assumes "map_io_well usclOkay f ch1 ch2"
    shows "chain Y \<Longrightarrow> ubDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow>  (\<Squnion>i. f\<cdot>(Y i . c1)) = f\<cdot>((Lub Y) . c1)"
  by (metis ch2ch_Rep_cfunR contlub_cfun_arg)

lemma tsynbabs_cont [simp]: 
  assumes "\<forall> x::'a tsyn stream. usclOkay c1 x = usclOkay c2 (tsynAbs\<cdot>x)"
    shows "cont (\<lambda>sb::'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) \<leadsto> (Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(sb . c1)]))"
proof- 
  have f1: " \<And>(x::'a tsyn stream\<^sup>\<Omega>) y::'a tsyn stream\<^sup>\<Omega>. ubclDom\<cdot>x = {c1} \<Longrightarrow> x \<sqsubseteq> y 
      \<Longrightarrow> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(x  .  c1)] \<sqsubseteq> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(y  .  c1)]"
    apply (simp_all add: ubclDom_ubundle_def)
    apply (rule ub_below)
    apply (simp add: assms ubdom_below ubdom_ubrep_eq) +
    apply (simp add: ubgetch_ubrep_eq assms ubdom_below)
    by (simp add: monofun_cfun_arg)
  have f2: "\<And>(Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>).
       chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i::nat. Y i) = {c1} \<Longrightarrow> chain (\<lambda>i::nat. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((Y i)  .  c1)])"
    by (simp add: assms ubclDom_ubundle_def)    
  have f3: "\<And> (Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>). chain Y \<Longrightarrow>
       ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {c1} \<Longrightarrow>
       ubDom\<cdot>(Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((\<Squnion>i::nat. Y i)  .  c1)]) = {c2}"
    by (simp add: assms ubclDom_ubundle_def ubdom_ubrep_eq)
  have f31: "\<And> (Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>). chain Y \<Longrightarrow>
       ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {c1} \<Longrightarrow>
       (\<Squnion>i::nat. ubDom\<cdot>(Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i  .  c1)])) = {c2}"
    apply (simp add: ubdom_insert)
    by (simp add: assms ubclDom_ubundle_def)
  have f5: "\<And>(Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>). chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i::nat. Y i) = {c1} \<Longrightarrow>
       Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((\<Squnion>i::nat. Y i)  .  c1)]  .  c2 = tsynAbs\<cdot>((\<Squnion>i::nat. Y i)  .  c1)"
    by (simp add: assms ubgetch_ubrep_eq)
  have f6: "\<And>(Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>). chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i::nat. Y i) = {c1} \<Longrightarrow>
       (\<Squnion>i::nat. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i  .  c1)])  .  c2 = (\<Squnion>i::nat. tsynAbs\<cdot>(Y i  .  c1))"
    apply (subst ubgetch_lub, simp add: f2)
    apply (metis (mono_tags) contlub_cfun_arg f2 f31 insertI1 ubclDom_ubundle_def)
    by (simp add: assms ubgetch_ubrep_eq)
  show ?thesis
    apply (fold ubclDom_ubundle_def)
    apply (rule ufun_contI)
    apply (simp add: f1)
    apply (rule ub_below)
    apply (subst contlub_cfun_arg, simp) +
    apply (subst contlub_cfun_arg)
    apply (simp add:f2 ubclDom_ubundle_def)
    apply (simp add: ubdom_insert)
    apply (subst ubrep_ubabs)
    apply (metis assms ch2ch_Rep_cfunR contlub_cfun_arg insertI1 tsynbabs_ubwell2 ubclDom_ubundle_def)
    apply (simp add: assms ubclDom_ubundle_def)
    apply (simp add: f3 ubclDom_ubundle_def)
    apply (simp add: f5 f6)
    by (metis below_refl ch2ch_Rep_cfunR contlub_cfun_arg)
qed    

lemma tsynbabs_insert:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynAbs\<cdot>s)"
  shows "tsynbAbs\<cdot>(sb ::'a tsyn stream\<^sup>\<Omega>) 
           = (ubDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(sb  .  c1)]"
  by (simp add: assms tsynbAbs_def)

lemma tsynbabs_test_finstream:
  "tsynbAbs\<cdot>(tsynbabsTestInput) = Some (tsynbabsTestOutput)"
  apply (subst tsynbabs_insert)
  defer
  apply (simp only: tsynbabsTestInput_def tsynbabsTestOutput_def)
  apply (subst ubgetch_ubrep_eq)
  apply (metis tsynbabsTestInput.rep_eq ubrep_well)
  oops
 
end