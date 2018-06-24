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
  "tsynbAbs  \<equiv> \<Lambda> sb. (ubclDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle [c1 \<mapsto> tsynAbs\<cdot>(sb  .  c1)]"

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
 
lift_definition tsynbabs_test_input :: "nat tsyn stream ubundle " is 
  "[c1 \<mapsto> <[Msg (1 :: nat), null, Msg 2, Msg 1]>]"
  apply (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def)
  by (metis image_eqI nat_1 nat_2 numeral_2_eq_2 range_eqI)

lift_definition tsynbabs_test_output :: "nat stream ubundle " is 
  "[c2 \<mapsto> <[(1 :: nat), 2, 1]>]"
  apply (simp add: ubWell_def usclOkay_stream_def)
  by (metis nat_1 nat_2 numeral_2_eq_2 range_eqI)

lemma tsynbabs_test_input_ubdom: "ubDom\<cdot>tsynbabs_test_input = {c1}"
proof-
  have h1:"tsynbabs_test_input = Abs_ubundle [c1 \<mapsto> \<up>(\<M> Suc (0::nat)) \<bullet> \<up>- \<bullet> \<up>(\<M> 2::nat) \<bullet> \<up>(\<M> Suc (0::nat))]"
    by(simp add: tsynbabs_test_input_def)
  have h0:"ubWell([c1 \<mapsto> \<up>(\<M> Suc (0::nat)) \<bullet> \<up>- \<bullet> \<up>(\<M> 2::nat) \<bullet> \<up>(\<M> Suc (0::nat))])"
    apply (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def)
    by (metis image_eqI nat_1 nat_2 numeral_2_eq_2 range_eqI)
  then show ?thesis
    by (simp add: h1 ubdom_ubrep_eq)
qed

(* ----------------------------------------------------------------------- *)
  section {* Lemmata on Time-Synchronous Stream Bundles *}
(* ----------------------------------------------------------------------- *)    
    
lemma sdom_tsynabs1:" - \<in> sdom\<cdot>x \<Longrightarrow>  sdom\<cdot>x = (insert - (Msg ` (sdom\<cdot>(tsynAbs\<cdot>x)))) "
  sorry
    
lemma sdom_tsynabs2:"- \<notin> sdom\<cdot>x \<Longrightarrow> (sdom\<cdot>x = (Msg ` (sdom\<cdot>(tsynAbs\<cdot>x))))"
  sorry
    
lemma usclokay_tsynabs:"ctype c1 = ctype c2 \<Longrightarrow> usclOkay c1 x = usclOkay c2 (tsynAbs\<cdot>x)"
  apply(simp add: usclOkay_stream_def ctype_tsyn_def)
    proof(cases "- \<in> sdom\<cdot>x")
      case True
      assume a0:"- \<in> sdom\<cdot>x"
      assume a1:"ctype c1 = ctype c2"
      have h0:"ctype c1 = ctype c2"
        sorry
      have h1:"sdom\<cdot>x = (insert - (Msg ` (sdom\<cdot>(tsynAbs\<cdot>x))))"
        by(simp add: a0 sdom_tsynabs1)
      have h2:"(insert - (Msg ` (sdom\<cdot>(tsynAbs\<cdot>x)))) \<subseteq> insert - (Msg ` ctype c1) = (sdom\<cdot>(tsynAbs\<cdot>x) \<subseteq> ctype c2)"
        using h0 by auto
      then show "(sdom\<cdot>x \<subseteq> insert - (Msg ` ctype c1)) = (sdom\<cdot>(tsynAbs\<cdot>x) \<subseteq> ctype c2)"
        by(simp add: h1)  
    next
      case False
      assume a0:"- \<notin> sdom\<cdot>x" 
      assume a1:"ctype c1 = ctype c2"
      have h0:"ctype c1 = ctype c2"
        sorry
      have h1:"sdom\<cdot>x = (Msg ` (sdom\<cdot>(tsynAbs\<cdot>x)))"
        using a0 sdom_tsynabs2 by blast
      have h2:"(insert - (Msg ` (sdom\<cdot>(tsynAbs\<cdot>x)))) \<subseteq> insert - (Msg ` ctype c1) = (sdom\<cdot>(tsynAbs\<cdot>x) \<subseteq> ctype c2)"
        using h0 by auto
      then show "(sdom\<cdot>x \<subseteq> insert - (Msg ` ctype c1)) = (sdom\<cdot>(tsynAbs\<cdot>x) \<subseteq> ctype c2)"
        by (simp add: h1)
    qed
  
lemma tsynbabs_ubwell3: assumes"\<forall> x::'a tsyn stream. usclOkay ch1 x = usclOkay ch2 (tsynAbs\<cdot>x) " 
                            and   "usclOkay ch1 (a::'a tsyn stream) " 
                            shows " usclOkay ch2 (tsynAbs\<cdot>a)"
  using assms(1) assms(2) by blast
   
lemma tsynbabs_ubwell: assumes"\<forall> x::'a tsyn stream. usclOkay ch1 x = usclOkay ch2 (tsynAbs\<cdot>x)"  
                               and "usclOkay ch1 (x::'a tsyn stream)"
                             shows "ubWell [ch2 \<mapsto> tsynAbs\<cdot>x]"
  apply (rule ubwellI)
  apply (simp add: domIff)
  using assms(1) assms(2) tsynbabs_ubwell3 by blast

lemma tsynbabs_ubwell2: assumes"\<forall> x::'a tsyn stream. usclOkay ch1 x = usclOkay ch2 (tsynAbs\<cdot>x)"  
                                and "ch1 \<in> ubDom\<cdot>ub"
                              shows "ubWell [ch2 \<mapsto> tsynAbs\<cdot>((ub :: 'a tsyn stream\<^sup>\<Omega>) . ch1)]"
  by (metis assms(1) assms(2) tsynbabs_ubwell ubdom_channel_usokay ubgetch_insert)
 
lemma tsynbabs_ubwell6:assumes"usclOkay c2 (x . c1)"
                       shows"ubWell([c2 \<mapsto> tsynAbs\<cdot>(x  .  c1)])"
  apply(simp add:ubWell_def)
  oops    
    
lemma tsynbabs_ubwell5:"ubWell([c1 \<mapsto> tsynAbs\<cdot>((x:: nat tsyn stream\<^sup>\<Omega>)  .  c1)])"
  apply(simp add:ubWell_def usclOkay_stream_def ctype_tsyn_def ubgetch_insert)
  by (metis subset_UNIV subset_image_iff transfer_int_nat_set_return_embed)
    
lemma tsynbabs_mono:"monofun (\<lambda> sb:: nat tsyn stream\<^sup>\<Omega> . (ubclDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(sb  .  c1)])"
  apply (rule ufun_monoI2)
  apply (simp add: ubclDom_ubundle_def)
  apply (rule ub_below)
  apply (simp add: ubdom_ubrep_eq tsynbabs_ubwell5)
  by (simp add: tsynbabs_ubwell5 ubgetch_ubrep_eq monofun_cfun_arg monofun_cfun_fun)

lemma jnn: assumes "chain Y " and "ubDom\<cdot>(Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i  .  c1)]) = {c2}"
            shows" ubDom\<cdot>(\<Squnion>i::nat. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i  .  c1)]) = {c2}"
  apply(simp add: ubdom_insert tsynbabs_ubwell5)
  oops
    
lemma tsynbabs_cont2: "cont (\<lambda>sb::nat tsyn stream\<^sup>\<Omega>. (ubclDom\<cdot>sb = {c1}) \<leadsto> (Abs_ubundle [c1 \<mapsto> tsynAbs\<cdot>(sb . c1)]))"  
  apply (rule ufun_contI)
  apply (simp add: ubclDom_ubundle_def)
  apply (rule ub_below)
  apply (simp add: ubdom_ubrep_eq tsynbabs_ubwell5)
  apply (simp add: tsynbabs_ubwell5 ubgetch_ubrep_eq monofun_cfun_arg monofun_cfun_fun)
  apply (simp add: ubclDom_ubundle_def)
  apply (rule ub_below)
  apply (simp add: tsynbabs_ubwell5 ubdom_ubrep_eq)
  sorry
    
lemma tsynbabs_mono2: assumes"\<forall> x::'a tsyn stream. usclOkay c1 x = usclOkay c2 (tsynAbs\<cdot>x)" shows
  "monofun (\<lambda> sb::'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(sb  .  c1)])"
  apply (fold ubclDom_ubundle_def)
  apply (rule monofunI)
  apply (case_tac "ubclDom\<cdot>x \<noteq> {c1}")
  apply (simp_all add: ubcldom_fix)
  apply (rule some_below)
  apply (rule ub_below)
  apply (simp add: ubdom_insert)
  apply(simp_all add:ubclDom_ubundle_def)
  apply (simp_all add: assms tsynbabs_ubwell2 ubclDom_ubundle_def)
  apply (simp add: assms tsynbabs_ubwell2 ubdom_below)
  by (simp add: assms fun_upd_same tsynbabs_ubwell2 monofun_cfun_arg ubdom_below ubgetch_ubrep_eq) 
  
lemma tsynbabs_chain1[simp]: 
  assumes "\<forall> x::'a tsyn stream. usclOkay c1 x = usclOkay c2 (tsynAbs\<cdot>x)"
    shows "chain (Y:: nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>) \<Longrightarrow> ubDom\<cdot>(Y 0) = {c1} \<Longrightarrow> chain (\<lambda> i. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i . c1)])"
  apply(rule chainI)
  apply(rule ub_below)
  apply (simp add: assms tsynbabs_ubwell2 ubdom_ubrep_eq)
  apply (simp add: ubdom_ubrep_eq)
  apply (simp add: assms tsynbabs_ubwell2 ubdom_ubrep_eq)
  by (simp add: assms tsynbabs_ubwell2 monofun_cfun_arg po_class.chainE ubgetch_ubrep_eq)

lemma tsynbabs_chain_lub[simp]: 
  assumes "\<forall> x::'a tsyn stream. usclOkay c1 x = usclOkay c2 (tsynAbs\<cdot>x)"
    shows "chain (Y:: nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>) \<Longrightarrow> ubDom\<cdot>(Lub Y) = {c1} \<Longrightarrow> chain (\<lambda> i. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((Y i) . c1)])"
  by (simp add: assms)
    
lemma tsynbabs_chain2: 
  assumes "\<forall> x::'a tsyn stream. usclOkay c1 x = usclOkay c2 (tsynAbs\<cdot>x)"
    shows "chain (Y:: nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>) \<Longrightarrow> chain(\<lambda> i. (ubDom\<cdot>(Y i) = {c1}) \<leadsto> (Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((Y i) . c1)]))"
  apply(rule chainI, simp)
  apply(rule impI, rule some_below, rule ub_below)
  apply (simp add: assms tsynbabs_ubwell2 ubdom_ubrep_eq)
  by (simp add: assms tsynbabs_ubwell2 monofun_cfun_arg po_class.chainE ubgetch_ubrep_eq)
    
lemma tsynbabs_lub[simp]: 
  assumes "map_io_well usclOkay f ch1 ch2"
    shows "chain Y \<Longrightarrow> ubDom\<cdot>(Lub Y) = {ch1} \<Longrightarrow>  (\<Squnion>i. f\<cdot>(Y i . c1)) = f\<cdot>((Lub Y) . c1)"
  by (metis ch2ch_Rep_cfunR contlub_cfun_arg)

lemma tsynbabs_cont3: 
  assumes "\<forall> x::'a tsyn stream. usclOkay c1 x = usclOkay c2 (tsynAbs\<cdot>x)"
    shows "cont (\<lambda>sb::'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) \<leadsto> (Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(sb . c1)]))"
proof- 
  have f1: " \<And>(x::'a tsyn stream\<^sup>\<Omega>) y::'a tsyn stream\<^sup>\<Omega>. ubclDom\<cdot>x = {c1} \<Longrightarrow> x \<sqsubseteq> y 
      \<Longrightarrow> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(x  .  c1)] \<sqsubseteq> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(y  .  c1)]"
    apply (simp_all add: ubclDom_ubundle_def)
    apply (rule ub_below)
    apply (simp add: assms tsynbabs_ubwell2 ubdom_below ubdom_ubrep_eq) +
    apply (simp add: ubgetch_ubrep_eq assms tsynbabs_ubwell2 ubdom_below)
    by (simp add: monofun_cfun_arg)
  have f2: "\<And>(Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>).
       chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i::nat. Y i) = {c1} \<Longrightarrow> chain (\<lambda>i::nat. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((Y i)  .  c1)])"
    by (simp add: assms ubclDom_ubundle_def)    
  have f3: "\<And> (Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>). chain Y \<Longrightarrow>
       ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {c1} \<Longrightarrow>
       ubDom\<cdot>(Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((\<Squnion>i::nat. Y i)  .  c1)]) = {c2}"
    by (simp add: assms tsynbabs_ubwell2 ubclDom_ubundle_def ubdom_ubrep_eq)
  have f31: "\<And> (Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>). chain Y \<Longrightarrow>
       ubclDom\<cdot>(\<Squnion>i::nat. Y i) = {c1} \<Longrightarrow>
       (\<Squnion>i::nat. ubDom\<cdot>(Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i  .  c1)])) = {c2}"
    apply (simp add: ubdom_insert)
    by (simp add: assms tsynbabs_ubwell2 ubclDom_ubundle_def)
  have f5: "\<And>(Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>). chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i::nat. Y i) = {c1} \<Longrightarrow>
       Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((\<Squnion>i::nat. Y i)  .  c1)]  .  c2 = tsynAbs\<cdot>((\<Squnion>i::nat. Y i)  .  c1)"
    by (simp add: assms tsynbabs_ubwell2 ubgetch_ubrep_eq)
  have f6: "\<And>(Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>). chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i::nat. Y i) = {c1} \<Longrightarrow>
       (\<Squnion>i::nat. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i  .  c1)])  .  c2 = (\<Squnion>i::nat. tsynAbs\<cdot>(Y i  .  c1))"
    apply (subst ubgetch_lub, simp add: f2)
    apply (metis (mono_tags) contlub_cfun_arg f2 f31 insertI1 ubclDom_ubundle_def)
    by (simp add: assms tsynbabs_ubwell2 ubgetch_ubrep_eq)
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
    apply (simp add: assms tsynbabs_ubwell2 ubclDom_ubundle_def)
    apply (simp add: f3 ubclDom_ubundle_def)
    apply (simp add: f5 f6)
    by (metis below_refl ch2ch_Rep_cfunR contlub_cfun_arg)
qed    
    
    
    
    
    

lemma tsynbabs_cont:
  "cont (\<lambda> sb. (ubclDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle [c1 \<mapsto> tsynAbs\<cdot>(sb  .  c1)])"
  
  sorry

lemma tsynbabs_insert: 
  "tsynbAbs\<cdot>sb = (ubclDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle [c1 \<mapsto> tsynAbs\<cdot>(sb  .  c1)]"
  by(simp add: tsynbAbs_def tsynbabs_cont)
    
lemma tsynbabs_test_finstream:
  "tsynbAbs\<cdot>(tsynbabs_test_input) = Some (tsynbabs_test_output)"
  apply (simp add: tsynbabs_insert ubclDom_ubundle_def tsynbabs_test_input_ubdom)
  apply (simp only: tsynbabs_test_input_def tsynbabs_test_output_def)
  apply (subst ubgetch_ubrep_eq)
  apply (metis tsynbabs_test_input.rep_eq ubrep_well)
  by (simp add: tsynbabs_insert tsynabs_insert)
    
end