theory EvenAutomatonProof

imports EvenAutomaton EvenStream

begin

  
section \<open>generated lemmata\<close>
(*createOutput lemmata*)  

lemma c1bundle_dom [simp]: "ubDom\<cdot>(createC1Bundle n) = {c1}"
  by (simp add: ubdom_insert createC1Bundle.rep_eq)

lemma c1bundle_ubgetch[simp]: "(createC1Bundle n) . c1 = \<up>(\<M>(A n))"
  by (metis c1bundle_dom createC1Bundle.rep_eq fun_upd_same insertI1 option.inject ubgetchE)

lemma tsynbonetick_ubconc_msg[simp]: assumes "ubDom\<cdot>sb = {c1}" 
  shows "ubConc (createC1Bundle n)\<cdot>sb  .  c1 = \<up>(\<M>(A n)) \<bullet> (sb. c1)"
  apply (simp only: ubConc_def)
  apply (simp only:  Abs_cfun_inverse2 ubconc_cont)
  apply (simp add: ubgetch_ubrep_eq)
  by (simp add: assms usclConc_stream_def)
     
    
lemma sbrt_ubconc_dom2[simp]:assumes "ubDom\<cdot>sb = {c1}" 
  shows "sbRt\<cdot>(ubConc (createC1Bundle n)\<cdot>sb) = sb"
  apply (rule ub_eq)
  by (simp add: sbRt_def assms) + 


(* useful for proof of h lemmata*)
lemma createc2output_dom:"ubDom\<cdot>(createC2Output a) = {c2}"
  by(simp add: ubDom_def createC2Output.rep_eq) 

    
(*useful for Transition*)
lemma tsynbonetick_hd_inv_convdiscrtup_tick[simp]:assumes "ubDom\<cdot>sb = {c1}" 
  shows "(inv convDiscrUp (sbHdElem\<cdot>(ubConc (tsynbOneTick c1)\<cdot>sb))) = [c1 \<mapsto> \<surd>]"
  apply (rule  convdiscrtup_eqI)
  apply (subst convdiscrup_inv_eq)
   apply (simp add: assms sbHdElem_channel)
  apply (subst fun_eq_iff)
  apply rule
  apply (case_tac "x = c1")
  unfolding sbHdElem_def
   apply (simp_all add: sbHdElem_cont assms)
  unfolding convDiscrUp_def
   apply simp
   apply (simp add: up_def)
  by simp

lemma tsynbonetick_hd_inv_convdiscrtup_msg[simp]:assumes "ubDom\<cdot>sb = {c1}" 
  shows "(inv convDiscrUp (sbHdElem\<cdot>(ubConc (createC1Bundle n)\<cdot>sb))) = [c1 \<mapsto> \<M>(A n)]"
  apply (rule  convdiscrtup_eqI)
  apply (subst convdiscrup_inv_eq)
   apply (simp add: assms sbHdElem_channel)
  apply (subst fun_eq_iff)
  apply rule
  apply (case_tac "x = c1")
  unfolding sbHdElem_def
   apply (simp_all add: sbHdElem_cont assms)
  unfolding convDiscrUp_def
   apply simp
   apply (simp add: up_def)
  by simp
   
(*Transition*)
lemma evenTraTick[simp]:"evenAutomatonTransition (state, [c1 \<mapsto> \<surd>]) = (state,(tsynbOneTick c2) )"
  by (metis (full_types) EvenAutomatonState.exhaust EvenAutomatonSubstate.exhaust evenAutomatonTransition.simps(2) evenAutomatonTransition.simps(4))
        
lemma tran_sum_even[simp]: assumes "Parity.even (summe + m)" shows "evenAutomatonTransition (State ooo summe, [c1 \<mapsto> \<M>(A m)]) = (State Even (summe + m), createC2Output True)"
  apply (cases ooo)
   apply auto
  using assms by presburger  +

    
lemma tran_sum_odd[simp]: assumes "\<not>Parity.even (summe + m)" shows "evenAutomatonTransition (State ooo summe, [c1 \<mapsto> \<M>(A m)]) = (State Odd (summe + m), createC2Output False)"
  apply (cases ooo)
   apply auto
  using assms by presburger  +
   
    
(*step lemmata*)
lemma evenaut_h_even_tick_step: assumes "ubDom\<cdot>sb = {c1}"
  shows "h EvenAutomatonAutomaton (State Even summe) \<rightleftharpoons> (ubConc (tsynbOneTick c1)\<cdot>sb) 
          = ubConc (tsynbOneTick c2)\<cdot> (h EvenAutomatonAutomaton  (State Even summe) \<rightleftharpoons> sb)"
  by(simp_all add: h_final getDom_def EvenAutomatonAutomaton.rep_eq h_out_dom assms getRan_def autGetNextOutput_def autGetNextState_def getTransition_def)


lemma evenaut_h_odd_tick_step: assumes "ubDom\<cdot>sb = {c1}"
  shows "h EvenAutomatonAutomaton (State Odd summe) \<rightleftharpoons> (ubConc (tsynbOneTick c1)\<cdot>sb) 
          = ubConc (tsynbOneTick c2)\<cdot> (h EvenAutomatonAutomaton  (State Odd summe) \<rightleftharpoons> sb)"
  by(simp_all add: h_final getDom_def EvenAutomatonAutomaton.rep_eq h_out_dom assms getRan_def autGetNextOutput_def autGetNextState_def getTransition_def)

lemma evenaut_h_even_even_step: assumes "ubDom\<cdot>sb = {c1}" and "(n+summe) mod 2 = 0"
  shows "h EvenAutomatonAutomaton (State Even summe) \<rightleftharpoons> (ubConc (createC1Bundle n)\<cdot>sb) 
          = ubConc (createC2Output True)\<cdot> (h EvenAutomatonAutomaton  (State Even (n+summe)) \<rightleftharpoons> sb)"
  apply(simp_all add: h_final getDom_def EvenAutomatonAutomaton.rep_eq h_out_dom assms getRan_def autGetNextOutput_def autGetNextState_def getTransition_def add.commute even_iff_mod_2_eq_zero)
  apply(rule ubrestrict_id)
  apply(simp add: h_out_dom assms getDom_def EvenAutomatonAutomaton.rep_eq getRan_def)
  by(subst ubDom_def, simp add: createC2Output.rep_eq)

lemma evenaut_h_odd_even_step: assumes "ubDom\<cdot>sb = {c1}" and "(n+summe) mod 2 = 0"
  shows "h EvenAutomatonAutomaton (State Odd summe) \<rightleftharpoons> (ubConc (createC1Bundle n)\<cdot>sb) 
          = ubConc (createC2Output True)\<cdot> (h EvenAutomatonAutomaton (State Even (n+summe)) \<rightleftharpoons> sb)"
  apply(simp_all add: h_final getDom_def EvenAutomatonAutomaton.rep_eq h_out_dom assms getRan_def autGetNextOutput_def autGetNextState_def getTransition_def add.commute even_iff_mod_2_eq_zero)
  apply(rule ubrestrict_id)
  apply(simp add: h_out_dom assms getDom_def EvenAutomatonAutomaton.rep_eq getRan_def)
  by(subst ubDom_def, simp add: createC2Output.rep_eq)

lemma evenaut_H_step: assumes "ubDom\<cdot>sb={c1}"
  shows "H EvenAutomatonAutomaton \<rightleftharpoons> sb =  ubConc (tsynbOneTick c2)\<cdot>(h EvenAutomatonAutomaton (State Even 0) \<rightleftharpoons> sb)"
  unfolding H_def
  by(simp add: h_out_dom getRan_def getInitialState_def getInitialOutput_def EvenAutomatonAutomaton.rep_eq getDom_def assms)
    
section \<open>Val start\<close>
  
lemma evenStreamBundle_well[simp]:"ubWell ([c1 \<mapsto> (nat2even\<cdot>s)])"
  apply(simp add: ubWell_def usclOkay_stream_def ctype_event_def)
proof(induction rule: tsyn_ind [of _s])
  case 1
  then show ?case
  proof(rule admI)
    fix Y::"nat \<Rightarrow> nat event stream"
    assume a1: "chain Y"
    assume a2: "\<forall>i::nat. sdom\<cdot>(nat2even\<cdot>(Y i)) \<subseteq> insert \<surd> (Msg ` range A)"
    show "sdom\<cdot>(nat2even\<cdot>(\<Squnion>i::nat. Y i)) \<subseteq> insert \<surd> (Msg ` range A)"
        by (metis a1 a2 ch2ch_Rep_cfunR contlub_cfun_arg subset_cont)
    qed
next
  case 2
  then show ?case by simp
next
  case (3 a s)
  then show ?case by simp
next
  case (4 s)
  then show ?case by simp
qed
  
lemma "sdom\<cdot>(nat2even\<cdot>s) \<subseteq> ctype c1"
  unfolding ctype_event_def
  apply (rule tsyn_ind [of _ s])
    apply (rule admI)
    apply (metis ch2ch_Rep_cfunR contlub_cfun_arg l44)
  by simp +


lemma evenStreamBundle_chain:assumes "chain Y" 
  shows"chain (\<lambda>i::nat. Abs_ubundle [c1 \<mapsto> nat2even\<cdot>(Y i)])"
  apply (rule chainI)
  apply (rule ub_below)
  apply (simp add: ubdom_ubrep_eq)
  apply (simp add: ubgetch_ubrep_eq)
  by (simp add: assms cont_pref_eq1I po_class.chainE)

lemma evenStreamBundle_lub: assumes "chain Y" 
  shows"(Abs_ubundle [c1 \<mapsto> nat2even\<cdot>(\<Squnion>i. Y i)]) = (\<Squnion>i. Abs_ubundle [c1 \<mapsto>  nat2even\<cdot>(Y i)])"
  apply (rule ub_eq)
   apply (simp add: evenStreamBundle_chain assms ubdom_lub2)
   apply (simp add: ubdom_ubrep_eq)
  apply (subst ubgetch_lub)
    apply (simp add: evenStreamBundle_chain assms)
   apply (metis (mono_tags) assms dom_eq_singleton_conv evenStreamBundle_chain evenStreamBundle_well ubdom_chain_eq2 ubdom_ubrep_eq)
  apply (simp add: ubgetch_ubrep_eq)
  by (simp add: assms contlub_cfun_arg)

(*New TODo*)
    
(*General and h*)

        
lemma [simp]: "ubWell [c1 \<mapsto> \<up>\<surd> \<bullet> nat2even\<cdot>s]" 
  by (metis evenStreamBundle_well tsynmap_tick)

lemma[simp]:"ubWell [c1 \<mapsto> \<up>(\<M> A m) \<bullet> nat2even\<cdot>xs]"
  by (metis evenStreamBundle_well tsynmap_msg)

lemma[simp]:"ubWell[c2 \<mapsto> \<up>(\<M> B x)]"
  by (metis createC2Output.rep_eq ubrep_well)
    
(*End*)
    
    
 lemma [simp]:"ubDom\<cdot>(ubclLeast cIn) = cIn"
  by (simp add: ubclLeast_ubundle_def)  

lemma ubclLeast_empty: assumes "c\<in>Dom" shows "ubclLeast Dom  .  c = \<epsilon>"
  by (simp add: assms ubclLeast_ubundle_def)

lemma evenGet_c[simp]:assumes "ubWell[c \<mapsto> x]" shows "Abs_ubundle [c \<mapsto> x]  .  c =  x"
  by (simp add: assms ubgetch_ubrep_eq)
    
lemma evenGet_c1[simp]:"Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x]  .  c1 =  nat2even\<cdot>x"
  by (metis evenStreamBundle_well fun_upd_same option.sel ubgetch_ubrep_eq)     

  
definition EvenStream::"EvenAutomatonState \<Rightarrow> nat event stream \<rightarrow> EvenAutomaton event stream" where
"EvenStream state \<equiv> (\<Lambda> s. ((h EvenAutomatonAutomaton state) \<rightleftharpoons> (Abs_ubundle [c1 \<mapsto> (nat2even\<cdot>s)])) . c2)" 

lemma evenstream_cont[simp]: "cont (\<lambda> s. ((h EvenAutomatonAutomaton state) \<rightleftharpoons> (Abs_ubundle [c1 \<mapsto> (nat2even\<cdot>s)])) . c2)"
proof(rule Cont.contI2)
  show"monofun (\<lambda>x::nat event stream. (h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x])  .  c2)"
  proof(rule monofunI)
    fix x y::"nat event stream"
    assume a1:"x \<sqsubseteq> y"
    have f1: " Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x] \<sqsubseteq>  Abs_ubundle [c1 \<mapsto> nat2even\<cdot>y]"
    proof -
      obtain cc :: "EvenAutomaton event stream\<^sup>\<Omega> \<Rightarrow> EvenAutomaton event stream\<^sup>\<Omega> \<Rightarrow> channel" where
        "\<forall>x0 x1. (\<exists>v2. v2 \<in> ubDom\<cdot>x1 \<and> x1 . v2 \<notsqsubseteq> x0 . v2) = (cc x0 x1 \<in> ubDom\<cdot>x1 \<and> x1 . cc x0 x1 \<notsqsubseteq> x0 . cc x0 x1)"
        by moura
      then have f1: "\<forall>u ua. (ubDom\<cdot>u \<noteq> ubDom\<cdot>ua \<or> cc ua u \<in> ubDom\<cdot>u \<and> u . cc ua u \<notsqsubseteq> ua . cc ua u) \<or> u \<sqsubseteq> ua"
        by (meson ub_below)
      have "ubDom\<cdot>(Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x]) = ubDom\<cdot>(Abs_ubundle [c1 \<mapsto> nat2even\<cdot>y])"
        by (simp add: ubdom_ubrep_eq)
      moreover
      { assume "(nat2even\<cdot>x \<sqsubseteq> nat2even\<cdot>y) \<noteq> (Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x] . cc (Abs_ubundle [c1 \<mapsto> nat2even\<cdot>y]) (Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x]) \<sqsubseteq> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>y] . cc (Abs_ubundle [c1 \<mapsto> nat2even\<cdot>y]) (Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x]))"
        then have "cc (Abs_ubundle [c1 \<mapsto> nat2even\<cdot>y]) (Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x]) \<noteq> c1"
          using evenStreamBundle_well fun_upd_def option.sel ubgetch_ubrep_eq by force
        then have "cc (Abs_ubundle [c1 \<mapsto> nat2even\<cdot>y]) (Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x]) \<notin> ubDom\<cdot>(Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x]) \<or> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x] . cc (Abs_ubundle [c1 \<mapsto> nat2even\<cdot>y]) (Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x]) \<sqsubseteq> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>y] . cc (Abs_ubundle [c1 \<mapsto> nat2even\<cdot>y]) (Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x])"
          by (metis (no_types) dom_empty dom_fun_upd evenStreamBundle_well option.simps(3) singletonD ubdom_ubrep_eq) }
      ultimately show ?thesis
        using f1 a1 monofun_cfun_arg by blast
    qed
    show "(h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x])  .  c2 
            \<sqsubseteq> (h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>y])  .  c2"    
      apply (rule ubgetch_below2)                     
      by (metis below_option_def below_refl f1 monofun_cfun_arg)
  qed
next
  fix Y:: "nat \<Rightarrow>nat event stream"
  assume a1: "chain Y"
  assume a2:"chain (\<lambda>i::nat. (h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>(Y i)])  .  c2)"
  have f20: "ubDom\<cdot>(Abs_ubundle [c1 \<mapsto> \<Squnion>i::nat. nat2even\<cdot>(Y i)]) = {c1}"
    by (metis a1 contlub_cfun_arg dom_eq_singleton_conv evenStreamBundle_well ubdom_ubrep_eq)
  have f21: "Abs_ubundle [c1 \<mapsto> \<Squnion>i::nat. nat2even\<cdot>(Y i)] = (\<Squnion>i::nat. Abs_ubundle [c1 \<mapsto> nat2even\<cdot>(Y i)])"
    apply (rule ub_eq)
    apply (simp_all add: f20)
     apply (metis (no_types) a1 dom_eq_singleton_conv evenStreamBundle_lub evenStreamBundle_well ubdom_ubrep_eq)
    by (metis a1 contlub_cfun_arg evenStreamBundle_lub)
  have f22: "(h EvenAutomatonAutomaton state \<rightleftharpoons> (\<Squnion>i::nat. Abs_ubundle [c1 \<mapsto> nat2even\<cdot>(Y i)])) = 
(\<Squnion>i::nat. h EvenAutomatonAutomaton state \<rightleftharpoons> (Abs_ubundle [c1 \<mapsto> nat2even\<cdot>(Y i)]))"
  proof -
    have "\<forall>f c. \<not> chain f \<or> (c\<cdot> (Lub f::EvenAutomaton event stream\<^sup>\<Omega>)::(EvenAutomaton event stream\<^sup>\<Omega>) option) = (\<Squnion>n. c\<cdot>(f n))"
      using contlub_cfun_arg by blast
    then show ?thesis
      by (simp add: a1 evenStreamBundle_chain op_the_lub)
  qed
  have f23:"c2 \<in> ubDom\<cdot>(\<Squnion>i. h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>(Y i)])"
    by (metis (no_types, lifting) EvenAutomatonAutomaton.rep_eq f21 f22 fst_conv getDom_def getRan_def h_dom h_ran local.f20 singletonI snd_conv ubclDom_ubundle_def ufran_2_ubcldom2)
  show "(h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>(\<Squnion>i::nat. Y i)])  .  c2 \<sqsubseteq>
       (\<Squnion>i::nat. (h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>(Y i)])  .  c2)"
    apply (simp add: contlub_cfun_arg a1 f21 f22 )
    by (simp_all add: ubgetch_lub f23 a1 evenStreamBundle_chain op_the_chain)
qed

lemma evenStream_insert:"EvenStream state\<cdot>s = ((h EvenAutomatonAutomaton state) \<rightleftharpoons> (Abs_ubundle [c1 \<mapsto> (nat2even\<cdot>s)])) . c2"
  by(simp add: EvenStream_def)

(* Needed in msg_assms and tick_assms *)
lemma h_apply_dom: "c2 \<in> ubDom\<cdot>(h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>xs])"
  proof -
    have ass1: "ubWell [c1 \<mapsto> nat2even\<cdot>xs]"
      by simp
    have a0: "ubDom\<cdot>(Abs_ubundle [c1 \<mapsto> nat2even\<cdot>xs]) = {c1}"
      by(simp add: ubdom_ubrep_eq)
    have a1: "ufDom\<cdot>(h EvenAutomatonAutomaton state) = {c1}"
      by (simp add: EvenAutomatonAutomaton.rep_eq getDom_def)
    then have a01: "ubDom\<cdot>(Abs_ubundle [c1 \<mapsto> nat2even\<cdot>xs]) = ufDom\<cdot>(h EvenAutomatonAutomaton state)"
      using a0 a1 by auto
    have a2: "ufRan\<cdot>(h EvenAutomatonAutomaton state) = {c2}"
      by (simp add: EvenAutomatonAutomaton.rep_eq getRan_def)
    then show ?thesis
      by (simp add: a01 spf_ubDom)
  qed

lemma  msg_assms: "EvenStream (State ooo summe)\<cdot>(\<up>(Msg m) \<bullet> xs)
                 = \<up>(Msg (B (Parity.even (summe + m)))) \<bullet> (EvenStream (State (evenMakeSubstate (Parity.even (summe + m)))  (summe + m))\<cdot>xs)"
  proof (cases "Parity.even (summe + m)") 
    case True
    have assms: "c2 \<in> ubDom\<cdot>(createC2Output True)"
      by(simp add: createc2output_dom)
    have ubConc_usclConc_eq_apply: "ubConc (createC2Output True)\<cdot>(h EvenAutomatonAutomaton (EvenAutomatonState.State Even (summe + m)) \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>xs]) .c2 
        = \<up>(\<M> EvenAutomaton.B True) \<bullet> (h EvenAutomatonAutomaton (EvenAutomatonState.State Even (summe + m)) \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>xs]) .c2"
      by (metis (no_types, lifting) h_apply_dom assms createC2Output.rep_eq fun_upd_same map_upd_eqD1 ubConc_usclConc_eq ubgetchE usclConc_stream_def)
    show ?thesis
      apply(simp add: evenStream_insert h_final ubdom_ubrep_eq getDom_def h_out_dom 
                      convDiscrUp_sbHdElem_eq autGetNextOutput_def autGetNextState_def
                      getTransition_def getRan_def EvenAutomatonAutomaton.rep_eq)
      using True ubConc_usclConc_eq_apply by auto
  next
    case False
    have assms: "c2 \<in> ubDom\<cdot>(createC2Output False)"
      by(simp add: createc2output_dom)
    have ubConc_usclConc_eq_apply: "ubConc (createC2Output False)\<cdot>(h EvenAutomatonAutomaton (EvenAutomatonState.State Odd (summe + m)) \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>xs]) .c2
        = \<up>(\<M> EvenAutomaton.B False) \<bullet> (h EvenAutomatonAutomaton (EvenAutomatonState.State Odd (summe + m)) \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>xs]) .c2"
      by (metis (no_types, lifting) h_apply_dom assms createC2Output.rep_eq fun_upd_same map_upd_eqD1 ubConc_usclConc_eq ubgetchE usclConc_stream_def)
    show ?thesis
      apply(simp add: evenStream_insert h_final ubdom_ubrep_eq getDom_def h_out_dom 
                      convDiscrUp_sbHdElem_eq autGetNextOutput_def autGetNextState_def
                      getTransition_def getRan_def EvenAutomatonAutomaton.rep_eq)
      using False ubConc_usclConc_eq_apply by auto
  qed
  
lemma [simp]:"nat2even\<cdot>(\<up>\<surd>) \<noteq> \<epsilon>"
  by (metis (mono_tags, lifting) event.simps(3) inject_scons lscons_conv sconc_fst_empty sup'_def tsynmap_bot tsynmap_tick)
  
lemma tick_assms: "EvenStream state\<cdot>(\<up>Tick \<bullet> xs) = \<up>Tick \<bullet> (EvenStream state\<cdot>xs)"
  apply(simp add: evenStream_insert getRan_def tsynbOneTick_def h_final ubdom_ubrep_eq getDom_def
                  EvenAutomatonAutomaton.rep_eq h_out_dom convDiscrUp_sbHdElem_eq
                  autGetNextOutput_def autGetNextState_def getTransition_def)
  by (metis h_apply_dom tsynbOneTick.abs_eq tsynbonetick_ubconc_tick)  

lemma evenStreamBundle_empty_well[simp]:"ubWell ([c1 \<mapsto> \<epsilon>])"
 by(simp add: ubWell_def usclOkay_stream_def ctype_event_def)
  
lemma bot_assms: "EvenStream state\<cdot>\<bottom> = \<bottom>"
  apply(simp add: evenStream_insert)
  apply(subst h_bottom, simp add: getDom_def EvenAutomatonAutomaton.rep_eq ubDom_def)
  apply(simp add: getDom_def EvenAutomatonAutomaton.rep_eq)
  by(simp add: getRan_def EvenAutomatonAutomaton.rep_eq ubclLeast_ubundle_def)
   
lemma EvenStream_final:"EvenStream (State ooo summe)\<cdot>xs = sscanlA evenTransition (State ooo summe)\<cdot>(nat2even\<cdot>xs)"
by(rule rek2evenstream, simp add: msg_assms, simp add: tick_assms, simp add: bot_assms)
  
end
  