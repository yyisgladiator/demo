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

text {* @{term tsynAbs} bundle is ubwell. *}    
lemma tsynbabs_ubwell [simp]:
  assumes "usclOkay c1 (s :: 'a tsyn stream)"
    and "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynAbs\<cdot>s)"
  shows "ubWell [c2 \<mapsto> tsynAbs\<cdot>s]"
  using assms
  by (simp add: ubWell_def domIff usclOkay_stream_def)

text {* @{term tsynbAbs} output bundle is ubwell. *}    
lemma tsynbabs_ubwell2 [simp]: 
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynAbs\<cdot>s)"  
    and "c1 \<in> ubDom\<cdot>sb"
  shows "ubWell [c2 \<mapsto> tsynAbs\<cdot>((sb :: 'a tsyn stream\<^sup>\<Omega>)  .  c1)]"
  by (metis assms tsynbabs_ubwell ubdom_channel_usokay ubgetch_insert)

text {* Domain of the @{term tsynbAbs} output bundle is {c2}. *}    
lemma tsynbabs_ubundle_ubdom:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynAbs\<cdot>s)"
    and "c1 \<in> ubDom\<cdot>sb"
  shows "ubDom\<cdot>(Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((sb :: 'a tsyn stream ubundle)  .  c1)]) = {c2}"
  using assms
  by (simp add: ubdom_insert)

text {* @{term tsynbAbs} is monotonic. *}    
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
    
text {* The @{term tsynbAbs} output bundle is a chain. *}     
lemma tsynbabs_chain[simp]: 
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynAbs\<cdot>s)"
  shows "chain (Y:: nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>) \<Longrightarrow> ubDom\<cdot>(Y 0) = {c1} \<Longrightarrow> 
         chain (\<lambda> i. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i . c1)])"
  apply (rule chainI)
  apply (rule ub_below)
  apply (simp add: assms ubdom_ubrep_eq)
  apply (simp add: ubdom_ubrep_eq)
  apply (simp add: assms ubdom_ubrep_eq)
  by (simp add: assms monofun_cfun_arg po_class.chainE ubgetch_ubrep_eq)

text {* @{term tsynbAbs} is continous. *}    
lemma tsynbabs_cont [simp]: 
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynAbs\<cdot>s)"
    shows "cont (\<lambda>sb::'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) \<leadsto> (Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(sb . c1)]))"
  proof(fold ubclDom_ubundle_def, rule ufun_contI)
    have mono2below:"\<And>(s :: 'a tsyn stream) x y::'a tsyn stream\<^sup>\<Omega>. usclOkay c1 s = 
         usclOkay c2 (tsynAbs\<cdot>s) \<Longrightarrow> monofun (\<lambda>sb :: 'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) 
         \<leadsto> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(sb  .  c1)]) \<Longrightarrow>  x \<sqsubseteq> y \<Longrightarrow> 
         (ubclDom\<cdot>x = {c1})\<leadsto>Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(x  .  c1)] \<sqsubseteq> (ubclDom\<cdot>y = {c1})\<leadsto>
         Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(y  .  c1)]"
    by (metis (no_types, lifting)  monofun_def ubclDom_ubundle_def)
    then have tsynbabs_below:"\<And>x y::'a tsyn stream\<^sup>\<Omega>. x \<sqsubseteq> y \<Longrightarrow> 
        (ubclDom\<cdot>x = {c1})\<leadsto>Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(x  .  c1)] \<sqsubseteq> (ubclDom\<cdot>y = {c1})\<leadsto>
         Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(y  .  c1)]"
      by (simp add: assms)
    show"\<And>x y::'a tsyn stream\<^sup>\<Omega>.ubclDom\<cdot>x = {c1} \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> 
          Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(x  .  c1)] \<sqsubseteq> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(y  .  c1)]"
      proof -
        fix x :: "'a tsyn stream\<^sup>\<Omega>" and y :: "'a tsyn stream\<^sup>\<Omega>"
        assume assms_ubcldom: "ubclDom\<cdot>x = {c1}"
        assume assms_below: "x \<sqsubseteq> y"
        then have "ubclDom\<cdot>x = ubclDom\<cdot>y"
          by (metis ubcldom_fix)
        then show "Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(x . c1)] \<sqsubseteq> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(y . c1)]"
          using assms_below assms_ubcldom tsynbabs_below some_below2 by fastforce
      qed
  next
    have tsynbabs_chain: "\<And>(Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>).
       chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i. Y i) = {c1} \<Longrightarrow> chain (\<lambda>i. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((Y i)  .  c1)])"
      by (simp add: assms ubclDom_ubundle_def)    
    have tsynbabs_ubdom_lub: "\<And> (Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>). chain Y \<Longrightarrow>
         ubclDom\<cdot>(\<Squnion>i. Y i) = {c1} \<Longrightarrow>
         ubDom\<cdot>(Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((\<Squnion>i. Y i)  .  c1)]) = {c2}"
      by (simp add: assms ubclDom_ubundle_def ubdom_ubrep_eq)
    have tsynbabs_ubdom_lub2: "\<And> (Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>). chain Y \<Longrightarrow>
         ubclDom\<cdot>(\<Squnion>i. Y i) = {c1} \<Longrightarrow>
         (\<Squnion>i. ubDom\<cdot>(Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i  .  c1)])) = {c2}"
      by (metis (mono_tags, lifting) assms tsynbabs_chain lub_eq singletonI tsynbabs_ubundle_ubdom 
         ubclDom_ubundle_def ubdom_chain_eq2 ubdom_lub2)
    have tsynbabs_ubundle_lub: "\<And>(Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>). chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i. Y i) = {c1} \<Longrightarrow>
         (\<Squnion>i. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i  .  c1)])  .  c2 = (\<Squnion>i. tsynAbs\<cdot>(Y i  .  c1))"
      proof(subst ubgetch_lub)
        show "\<And>Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>. chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i. Y i) = {c1} \<Longrightarrow> 
              chain (\<lambda>i. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i  .  c1)])"
          by(simp add: tsynbabs_chain)
        show "\<And>Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>. chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i. Y i) = {c1} \<Longrightarrow> 
              c2 \<in> ubDom\<cdot>(\<Squnion>i. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i  .  c1)])"
          by(metis (mono_tags) contlub_cfun_arg tsynbabs_chain tsynbabs_ubdom_lub2 
             insertI1 ubclDom_ubundle_def)
        show"\<And>Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>. chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i. Y i) = {c1} \<Longrightarrow>
             (\<Squnion>i. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i  .  c1)]  .  c2) = (\<Squnion>i. tsynAbs\<cdot>(Y i  .  c1))"
          by (simp add: assms ubgetch_ubrep_eq) 
      qed
    have tsynbabs_below_lub:"\<And>(Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>) c. chain Y \<Longrightarrow> ubDom\<cdot>(\<Squnion>i. Y i) = {c1} \<Longrightarrow> 
          c = c2 \<Longrightarrow> tsynAbs\<cdot>((\<Squnion>i. Y i)  .  c1) \<sqsubseteq> (\<Squnion>i. tsynAbs\<cdot>(Y i  .  c1))"
      by (metis below_refl ch2ch_Rep_cfunR contlub_cfun_arg)
    show "\<And>Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>. chain Y \<Longrightarrow> ubclDom\<cdot>(\<Squnion>i. Y i) = {c1} \<Longrightarrow>
    Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((\<Squnion>i. Y i)  .  c1)] \<sqsubseteq> (\<Squnion>i. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i  .  c1)])"
      proof (rule ub_below)
        show"\<And>Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>. chain Y \<Longrightarrow> ubclDom\<cdot>(\<Squnion>i. Y i) = {c1} \<Longrightarrow>
             ubDom\<cdot>(Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((\<Squnion>i. Y i)  .  c1)]) = 
             ubDom\<cdot>(\<Squnion>i. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i  .  c1)])"
          by (metis (mono_tags, lifting) tsynbabs_chain tsynbabs_ubdom_lub tsynbabs_ubdom_lub2 
              image_cong ubclDom_ubundle_def ubdom_lub2)
        show"\<And>(Y::nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>) c. chain Y \<Longrightarrow> ubclDom\<cdot>(\<Squnion>i. Y i) = {c1} \<Longrightarrow>
             c \<in> ubDom\<cdot>(Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((\<Squnion>i. Y i)  .  c1)]) \<Longrightarrow>
             Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>((\<Squnion>i. Y i)  .  c1)]  .  c 
             \<sqsubseteq> (\<Squnion>i. Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(Y i  .  c1)])  .  c"
          by (simp add: tsynbabs_below_lub tsynbabs_ubdom_lub ubclDom_ubundle_def assms 
             ubgetch_ubrep_eq tsynbabs_ubundle_lub)
      qed
  qed
  
text {* @{term tsynbAbs} satisfies well condition for universal functions. *}  
lemma tsynbabs_ufwell[simp]:assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynAbs\<cdot>s)"
  shows "ufWell (tsynbAbs:: 'a tsyn stream\<^sup>\<Omega> \<rightarrow> ('a stream\<^sup>\<Omega>) option)"
  apply(simp add: tsynbAbs_def)
  apply (rule ufun_wellI)
  apply (simp_all add: domIff2 assms)
  apply (simp_all add: ubclDom_ubundle_def)
  apply (simp add: ubdom_insert)
  by (simp add: assms ubdom_insert)  

text {* @{term tsynbAbs} insertion lemma. *}
lemma tsynbabs_insert:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynAbs\<cdot>s)"
  shows "tsynbAbs\<cdot>(sb ::'a tsyn stream\<^sup>\<Omega>) 
           = (ubDom\<cdot>sb = {c1}) \<leadsto> Abs_ubundle [c2 \<mapsto> tsynAbs\<cdot>(sb  .  c1)]"
  by (simp add: assms tsynbAbs_def)
        
lemma tsynabs_sdom:"(sdom\<cdot>s \<subseteq> insert - (Msg ` range a)) = (sdom\<cdot>(tsynAbs\<cdot>s) \<subseteq> range a)"
  proof (induction s rule: tsyn_ind)
    case adm
    then show ?case by(rule admI, simp add: contlub_cfun_arg lub_eq_Union UN_subset_iff)
  next
    case bot
    then show ?case by simp
  next
    case (msg m s)
    then show ?case by (simp only: tsynabs_sconc_msg sdom2un, auto)
  next
    case (null s)
    then show ?case by (simp only: tsynabs_sconc_null sdom2un, auto)
  qed

text {* @{term tsynbAbs} is strict.*}
lemma tsynbabs_strict:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynAbs\<cdot>s)"
  shows "(tsynbAbs:: 'a tsyn stream\<^sup>\<Omega> \<rightarrow> ('a stream\<^sup>\<Omega>) option)\<cdot>(ubLeast {c1}) = Some (ubLeast {c2})"
  apply(simp add: assms tsynbabs_insert)
  apply(simp add: ubLeast_def)
  by (metis (no_types) fun_upd_apply)

text {* test lemma for @{term tsynbAbs}*}    
lemma tsynbabs_test_finstream:
  "tsynbAbs\<cdot>(tsynbabsTestInput) = Some (tsynbabsTestOutput)"
  apply (subst tsynbabs_insert)
  apply (simp add: usclOkay_stream_def ctype_tsyn_def tsynabs_sdom)
  apply (simp only: tsynbabsTestInput_def tsynbabsTestOutput_def)
  apply (subst ubgetch_ubrep_eq)
  apply (metis tsynbabsTestInput.rep_eq ubrep_well)
  apply (simp add: ubdom_insert tsynabs_insert)
  using tsynbabsTestInput.abs_eq tsynbabsTestInput.rep_eq by auto[1]
  
 
end