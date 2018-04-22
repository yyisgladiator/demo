theory EvenAutomatonProof

imports EvenAutomaton EvenStream

begin
  
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

(*ToDo*)
  
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

       
(*ToDo end*)
    
(*New TODo*)
    
(*General and h*)
 lemma evenHdElem: assumes"x\<noteq>\<epsilon>" and "ubWell[c \<mapsto> x]" shows "inv convDiscrUp (sbHdElem\<cdot>(Abs_ubundle [c \<mapsto> x])) = [c1 \<mapsto> shd(x)]"
   sorry     
 
lemma h_sb_dom[simp]:"ubDom\<cdot>(h automat s \<rightleftharpoons>sb) = getRan automat"
  sorry   
    
lemma [simp]:"(inv convDiscrUp (sbHdElem\<cdot>(ubConc (tsynbOneTick c1)\<cdot>sb))) = [c1 \<mapsto> \<surd>]"
  sorry
    
lemma [simp]:"(inv convDiscrUp (sbHdElem\<cdot>(ubConc (createC1Bundle n)\<cdot>sb))) = [c1 \<mapsto> \<M>(A n)]"
  sorry
    
lemma evenAutoEmpty:"(h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> \<epsilon>]) = ubclLeast {c2}"
  sorry

lemma [simp]:assumes "ubWell [c \<mapsto> x]" shows "sbRt\<cdot>(Abs_ubundle [c \<mapsto> x]) = (Abs_ubundle [c \<mapsto> srt\<cdot>x])"
  sorry 
        
lemma [simp]: "ubWell [c1 \<mapsto> \<up>\<surd> \<bullet> nat2even\<cdot>s]" 
  by (metis evenStreamBundle_well tsynmap_tick)
    
lemma ubConc2stream:"(ubConc sb1 \<cdot> sb2) . c = (sb1. c) \<bullet> (sb2. c)"
  sorry    

(*Test*)
    
lemma test:"ubConc (tsynbOneTick c1)\<cdot>sb  .  c1 = \<up>\<surd> \<bullet> (sb .c1)"
  sorry

lemma test2:"ubConc (createC1Bundle n)\<cdot>sb  .  c1 = \<up>(\<M>(A n)) \<bullet> (sb. c1)"
  sorry
    
lemma sbRt_ubConc_dom[simp]:assumes "ubDom\<cdot>sb = {c1}" shows "sbRt\<cdot>(ubConc (Abs_ubundle [c1 \<mapsto> \<up>\<surd>])\<cdot>sb) = sb"
  sorry
    
lemma sbRt_ubConc_dom2[simp]:assumes "ubDom\<cdot>sb = {c1}" shows "sbRt\<cdot>(ubConc (Abs_ubundle [c1 \<mapsto> \<up>(\<M> (A n))])\<cdot>sb) = sb"
  sorry

lemma[simp]:"ubWell [c1 \<mapsto> \<up>(\<M> A m) \<bullet> nat2even\<cdot>xs]"
  by (metis evenStreamBundle_well tsynmap_msg)

lemma[simp]:"ubWell[c2 \<mapsto> \<up>(\<M> B x)]"
  by (metis createC2Output.rep_eq ubrep_well)

(*Transition function*)
  
lemma evenTraTick:"evenAutomatonTransition (state, [c1 \<mapsto> \<surd>]) = (state,(tsynbOneTick c2) )"
  sorry  
        
lemma tran_sum_even: assumes "Parity.even (summe + m)" shows "evenAutomatonTransition (State ooo summe, [c1 \<mapsto> \<M> A m]) = (State Even (summe + m), createC2Output True)"
  sorry
    
lemma tran_sum_odd: assumes "\<not>Parity.even (summe + m)" shows "evenAutomatonTransition (State ooo summe, [c1 \<mapsto> \<M> A m]) = (State Odd (summe + m), createC2Output False)"
  sorry   

    
    
    
(*Val*)

lemma evenVal:"(spfConc (autGetNextOutput EvenAutomatonAutomaton (State ooo summe) [c1 \<mapsto> \<M> (A m)])\<cdot>
     (spfRt\<cdot>(h EvenAutomatonAutomaton (fst (evenAutomatonTransition (State ooo summe, [c1 \<mapsto> \<M> (A m)]))))) \<rightleftharpoons>
     Abs_ubundle [c1 \<mapsto> \<up>(\<M> A m) \<bullet> nat2even\<cdot>(xs)]) = (ubConc (autGetNextOutput EvenAutomatonAutomaton (State ooo summe) [c1 \<mapsto>\<M> (A m)])\<cdot>
     ((h EvenAutomatonAutomaton (fst (evenAutomatonTransition (State ooo summe, [c1 \<mapsto> \<M> (A m)])))) \<rightleftharpoons>
     Abs_ubundle [c1 \<mapsto> (nat2even\<cdot>(xs))]))"
proof -
  have f1: "ubDom\<cdot>(Abs_ubundle [c1 \<mapsto> \<up>(\<M> A m) \<bullet> nat2even\<cdot>xs]) 
    = ufDom\<cdot>(spfRt\<cdot>(h EvenAutomatonAutomaton (fst (evenAutomatonTransition (EvenAutomatonState.State ooo summe, [c1 \<mapsto> \<M> A m])))))"
    apply (simp add: ubdom_ubrep_eq)
    unfolding EvenAutomatonAutomaton_def
    unfolding getDom_def
    by (metis EvenAutomatonAutomaton.rep_eq Rep_automaton_inverse fst_conv snd_conv)
  have f2: "ubDom\<cdot>(autGetNextOutput EvenAutomatonAutomaton (EvenAutomatonState.State ooo summe) [c1 \<mapsto> \<M> A m]) = {c2}"
    unfolding autGetNextOutput_def
    unfolding getTransition_def
    unfolding EvenAutomatonAutomaton_def
  proof -
    have "automaton_well (evenAutomatonTransition, EvenAutomatonState.State Even 0, tsynbOneTick c2, {c1}, {c2})"
      by (meson EvenAutomatonAutomaton.rsp eq_onp_same_args)
    then show "ubDom\<cdot> (snd (fst (Rep_automaton (Abs_automaton (evenAutomatonTransition, EvenAutomatonState.State Even 0, tsynbOneTick c2, {c1}, {c2}))) (EvenAutomatonState.State ooo summe, [c1 \<mapsto> \<M> A m]))) = {c2}"
      using EvenAutomatonAutomaton.rep_eq EvenAutomatonAutomaton_def by force
  qed
  show ?thesis
    apply (subst spconc_step)
     apply (simp add: f1)
    apply simp 
    apply (rule ubrestrict_id)
    apply (simp add: f2)
    apply (simp add: getRan_def EvenAutomatonAutomaton_def)
    by (metis EvenAutomatonAutomaton.rep_eq Rep_automaton_inverse insertI1 snd_conv)
qed
    
    
lemma evenVal2_ub:assumes "ubDom\<cdot>sb = {c1}" shows"spfConc (autGetNextOutput EvenAutomatonAutomaton state [c1 \<mapsto> \<surd>])\<cdot>
    (spfRt\<cdot>(h EvenAutomatonAutomaton (autGetNextState EvenAutomatonAutomaton state [c1 \<mapsto> \<surd>]))) \<rightleftharpoons>
    ubConc (tsynbOneTick c1)\<cdot>sb
        = ubConcEq (autGetNextOutput EvenAutomatonAutomaton state [c1 \<mapsto> \<surd>])\<cdot>((h EvenAutomatonAutomaton state) \<rightleftharpoons> sbRt\<cdot>(ubConc (tsynbOneTick c1)\<cdot>sb))"
   apply (subst spconc_step)
   apply (simp add: ubdom_ubrep_eq getDom_def EvenAutomatonAutomaton.rep_eq assms)
   by(subst spfrt_step, simp add: autGetNextState_def getTransition_def EvenAutomatonAutomaton.rep_eq evenTraTick)

    
lemma evenVal_ub:assumes "ubDom\<cdot>sb = {c1}" and "(n+summe) mod 2 = 0" shows "spfConc (autGetNextOutput EvenAutomatonAutomaton (State Even summe) [c1 \<mapsto> \<M> A n])\<cdot>
    (spfRt\<cdot>(h EvenAutomatonAutomaton (autGetNextState EvenAutomatonAutomaton (State Even summe) [c1 \<mapsto> \<M> A n]))) \<rightleftharpoons>
    ubConc (createC1Bundle n)\<cdot>sb = (ubConc (autGetNextOutput EvenAutomatonAutomaton (State Even summe) [c1 \<mapsto>\<M> (A n)])\<cdot>
     (h EvenAutomatonAutomaton (State Even (n + summe)) \<rightleftharpoons> sb))"
   apply (subst spconc_step)
   apply (simp add: ubdom_ubrep_eq getDom_def EvenAutomatonAutomaton.rep_eq assms)
   apply(subst spfrt_step, simp add: autGetNextState_def autGetNextOutput_def getTransition_def EvenAutomatonAutomaton.rep_eq add.commute assms(2) even_iff_mod_2_eq_zero tran_sum_even)
  by (simp add: createC1Bundle_def assms ubdom_ubrep_eq createC2Output_def getRan_def EvenAutomatonAutomaton.rep_eq)
    
lemma evenVal_ub_odd:assumes "ubDom\<cdot>sb = {c1}" and "(n+summe) mod 2 = 0" shows "spfConc (autGetNextOutput EvenAutomatonAutomaton (State Odd summe) [c1 \<mapsto> \<M> A n])\<cdot>
    (spfRt\<cdot>(h EvenAutomatonAutomaton (autGetNextState EvenAutomatonAutomaton (State Odd summe) [c1 \<mapsto> \<M> A n]))) \<rightleftharpoons>
    ubConc (createC1Bundle n)\<cdot>sb = (ubConc (autGetNextOutput EvenAutomatonAutomaton (State Odd summe) [c1 \<mapsto>\<M> (A n)])\<cdot>
     (h EvenAutomatonAutomaton (State Even (n + summe)) \<rightleftharpoons> sb))"
   apply (subst spconc_step)
   apply (simp add: ubdom_ubrep_eq getDom_def EvenAutomatonAutomaton.rep_eq assms)
   apply(subst spfrt_step, simp add: autGetNextState_def autGetNextOutput_def getTransition_def EvenAutomatonAutomaton.rep_eq add.commute assms(2) even_iff_mod_2_eq_zero tran_sum_even)
  by (simp add: createC1Bundle_def assms ubdom_ubrep_eq createC2Output_def getRan_def EvenAutomatonAutomaton.rep_eq)

lemma evenVal2:assumes "ubWell[c1 \<mapsto> x]" shows"(spfConc (autGetNextOutput EvenAutomatonAutomaton state [c1 \<mapsto> \<surd>])\<cdot>(spfRt\<cdot>(h EvenAutomatonAutomaton state)) \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> x])
        = ubConcEq (autGetNextOutput EvenAutomatonAutomaton state [c1 \<mapsto> \<surd>])\<cdot>((h EvenAutomatonAutomaton state) \<rightleftharpoons> sbRt\<cdot>(Abs_ubundle [c1 \<mapsto> x]))"
  apply (subst spconc_step)
   apply (simp add: ubdom_ubrep_eq assms)
  unfolding EvenAutomatonAutomaton_def
  unfolding getDom_def
  using EvenAutomatonAutomaton.rep_eq EvenAutomatonAutomaton_def apply auto[1]
  by simp


    
(*End*)
    
    
 lemma [simp]:"ubDom\<cdot>(ubclLeast cIn) = cIn"
  by (simp add: ubclLeast_ubundle_def)  

lemma ubclLeast_empty: assumes "c\<in>Dom" shows "ubclLeast Dom  .  c = \<epsilon>"
  by (simp add: assms ubclLeast_ubundle_def)

lemma evenGet_c[simp]:assumes "ubWell[c \<mapsto> x]" shows "Abs_ubundle [c \<mapsto> x]  .  c =  x"
  by (simp add: assms ubgetch_ubrep_eq)
    
lemma evenGet_c1[simp]:"Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x]  .  c1 =  nat2even\<cdot>x"
  by (metis evenStreamBundle_well fun_upd_same option.sel ubgetch_ubrep_eq)     

    
    
lemma evenaut_h_even_tick_step: assumes "ubDom\<cdot>sb = {c1}"
  shows "h EvenAutomatonAutomaton (State Even summe) \<rightleftharpoons> (ubConc (tsynbOneTick c1)\<cdot>sb) 
          = ubConc (tsynbOneTick c2)\<cdot> (h EvenAutomatonAutomaton  (State Even summe) \<rightleftharpoons> sb)"
  apply(subst h_final, simp_all add: getDom_def EvenAutomatonAutomaton.rep_eq test, simp add: assms)
  apply(simp add: assms evenVal2_ub)
  apply(simp add: autGetNextOutput_def getTransition_def EvenAutomatonAutomaton.rep_eq evenTraTick tsynbOneTick_def evenAutoEmpty)
  apply(simp_all add: assms)
  apply(subst ubrestrict_id, simp add: getRan_def EvenAutomatonAutomaton.rep_eq)
  apply (metis eq_refl tsynbOneTick.abs_eq tsynbonetick_dom)
  by simp

lemma evenaut_h_odd_tick_step: assumes "ubDom\<cdot>sb = {c1}"
  shows "h EvenAutomatonAutomaton (State Odd summe) \<rightleftharpoons> (ubConc (tsynbOneTick c1)\<cdot>sb) 
          = ubConc (tsynbOneTick c2)\<cdot> (h EvenAutomatonAutomaton  (State Odd summe) \<rightleftharpoons> sb)"
  apply(subst h_final, simp_all add: getDom_def EvenAutomatonAutomaton.rep_eq test, simp add: assms)
  apply(simp add: assms evenVal2_ub)
  apply(simp add: autGetNextOutput_def getTransition_def EvenAutomatonAutomaton.rep_eq evenTraTick tsynbOneTick_def evenAutoEmpty)
  apply(simp_all add: assms)
  apply(subst ubrestrict_id, simp add: getRan_def EvenAutomatonAutomaton.rep_eq)
  apply (metis eq_refl tsynbOneTick.abs_eq tsynbonetick_dom)
  by simp

lemma evenaut_h_even_even_step: assumes "ubDom\<cdot>sb = {c1}" and "(n+summe) mod 2 = 0"
  shows "h EvenAutomatonAutomaton (State Even summe) \<rightleftharpoons> (ubConc (createC1Bundle n)\<cdot>sb) 
          = ubConc (createC2Output True)\<cdot> (h EvenAutomatonAutomaton  (State Even (n+summe)) \<rightleftharpoons> sb)"
  apply(subst h_final, simp_all add: getDom_def EvenAutomatonAutomaton.rep_eq test2, simp add: assms)
  apply(subst evenVal_ub, simp_all add: assms)
  apply(simp add:autGetNextOutput_def getTransition_def EvenAutomatonAutomaton.rep_eq evenTraTick tsynbOneTick_def evenAutoEmpty)
  apply(subst tran_sum_even)
  by (simp_all add: add.commute assms(2) even_iff_mod_2_eq_zero ubConc2stream createC2Output_def createC1Bundle_def)

lemma evenaut_h_odd_even_step: assumes "ubDom\<cdot>sb = {c1}" and "(n+summe) mod 2 = 0"
  shows "h EvenAutomatonAutomaton (State Odd summe) \<rightleftharpoons> (ubConc (createC1Bundle n)\<cdot>sb) 
          = ubConc (createC2Output True)\<cdot> (h EvenAutomatonAutomaton (State Even (n+summe)) \<rightleftharpoons> sb)"
  apply(subst h_final, simp_all add: getDom_def EvenAutomatonAutomaton.rep_eq test2, simp add: assms)
  apply(subst evenVal_ub_odd, simp_all add: assms)
  apply(simp add:autGetNextOutput_def getTransition_def EvenAutomatonAutomaton.rep_eq evenTraTick tsynbOneTick_def evenAutoEmpty)
  apply(subst tran_sum_even)
  by (simp_all add: add.commute assms(2) even_iff_mod_2_eq_zero ubConc2stream createC2Output_def createC1Bundle_def)

lemma evenaut_H_step: assumes "ubDom\<cdot>sb={c1}"
  shows "H EvenAutomatonAutomaton \<rightleftharpoons> sb =  ubConc (tsynbOneTick c2)\<cdot>(h EvenAutomatonAutomaton (State Even 0) \<rightleftharpoons> sb)"
  unfolding H_def
  apply(simp add: getInitialState_def getInitialOutput_def EvenAutomatonAutomaton.rep_eq, subst spconc_step, simp add: getDom_def EvenAutomatonAutomaton.rep_eq assms)
  by(simp add: getRan_def EvenAutomatonAutomaton.rep_eq)

  
definition EvenStream::"EvenAutomatonState \<Rightarrow> nat event stream \<rightarrow> EvenAutomaton event stream" where
"EvenStream state \<equiv> (\<Lambda> s. ((h EvenAutomatonAutomaton state) \<rightleftharpoons> (Abs_ubundle [c1 \<mapsto> (nat2even\<cdot>s)])) . c2)" 

lemma evenStream_insert:"EvenStream state\<cdot>s = ((h EvenAutomatonAutomaton state) \<rightleftharpoons> (Abs_ubundle [c1 \<mapsto> (nat2even\<cdot>s)])) . c2"
  apply(simp add: EvenStream_def,rule beta_cfun)
proof(rule Cont.contI2)
  show"monofun (\<lambda>x::nat event stream. (h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x])  .  c2)"
  proof(rule monofunI)
    fix x y::"nat event stream"
    assume a1:"x \<sqsubseteq> y"
    show "(h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x])  .  c2 \<sqsubseteq> (h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>y])  .  c2"
    proof(cases "\<forall>c::channel\<in>getDom EvenAutomatonAutomaton. Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x]  .  c \<noteq> \<epsilon>")
      case True
      then show ?thesis
       (* proof(insert a1, induction arbitrary: state rule: tsyn_ind [of _x])
          case 1
          then show ?case
            apply(rule adm_imp, auto)+
              sorry
        next
          case 2
          then show ?case
            apply(simp add: getDom_def EvenAutomatonAutomaton.rep_eq)
            by (smt domIff evenStreamBundle_well fun_upd_same option.sel tsynmap_bot ubWell_def ubgetch_ubrep_eq)
        next
          case (3 a s)
          then show ?case sorry
        next
          case (4 s)
          then show ?case sorry
        qed*)
       (* apply(subst h_final, simp_all add: getDom_def EvenAutomatonAutomaton.rep_eq ubDom_def autGetNextOutput_def)
        apply(simp add: getTransition_def EvenAutomatonAutomaton.rep_eq)
        apply(subst evenHdElem)
        apply auto[1]
        sorry*)
        sorry
    next
      case False
      then show ?thesis
        apply(subst h_bottom, simp_all add: getDom_def getRan_def ubdom_insert EvenAutomatonAutomaton.rep_eq ubclLeast_empty)
        by (metis dom_eq_singleton_conv evenStreamBundle_well ubrep_ubabs)
    qed    
  qed
next
  fix Y:: "nat \<Rightarrow>nat event stream"
  assume a1: "chain Y"
  assume a2:"chain (\<lambda>i::nat. (h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>(Y i)])  .  c2)"
  show "(h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>(\<Squnion>i::nat. Y i)])  .  c2 \<sqsubseteq>
       (\<Squnion>i::nat. (h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> nat2even\<cdot>(Y i)])  .  c2)"
    apply(simp add: a1 evenStreamBundle_lub, subst contlub_cfun_arg, simp add: a1 evenStreamBundle_chain)
    sorry
qed


lemma  msg_assms: "EvenStream (State ooo summe)\<cdot>(\<up>(Msg m) \<bullet> xs)
                 = \<up>(Msg (B (Parity.even (summe + m)))) \<bullet> (EvenStream (State (evenMakeSubstate (Parity.even (summe + m)))  (summe + m))\<cdot>xs)"
  apply(simp add: evenStream_insert)
  apply(subst h_final, simp add: getDom_def getRan_def ubdom_insert EvenAutomatonAutomaton.rep_eq,simp add: getDom_def getRan_def ubdom_insert EvenAutomatonAutomaton.rep_eq)
  apply(simp add: evenHdElem autGetNextState_def getTransition_def EvenAutomatonAutomaton.rep_eq evenTraTick evenAutoEmpty)
  apply(simp add: evenVal)
  apply(simp add: autGetNextOutput_def getTransition_def EvenAutomatonAutomaton.rep_eq)
  apply(cases "Parity.even (summe + m)")
  by(simp_all add: tran_sum_even tran_sum_odd ubConc2stream createC2Output_def)
     
lemma [simp]:"nat2even\<cdot>(\<up>\<surd>) \<noteq> \<epsilon>"
  by (metis (mono_tags, lifting) event.simps(3) inject_scons lscons_conv sconc_fst_empty sup'_def tsynmap_bot tsynmap_tick)
    
lemma tick_assms: "EvenStream state\<cdot>(\<up>Tick \<bullet> xs) = \<up>Tick \<bullet> (EvenStream state\<cdot>xs)"
  apply(simp add: evenStream_insert)
  apply(subst h_final, simp add: getDom_def getRan_def ubdom_insert EvenAutomatonAutomaton.rep_eq,simp add: getDom_def getRan_def ubdom_insert EvenAutomatonAutomaton.rep_eq)
  apply(simp add: evenHdElem autGetNextState_def getTransition_def EvenAutomatonAutomaton.rep_eq evenTraTick evenAutoEmpty)
  apply(simp add: evenVal2)
  apply(simp add: autGetNextOutput_def getTransition_def EvenAutomatonAutomaton.rep_eq evenTraTick tsynbOneTick_def evenAutoEmpty)
  apply(subst ubrestrict_id, simp add: getRan_def EvenAutomatonAutomaton.rep_eq)
  apply (metis eq_refl tsynbOneTick.abs_eq tsynbonetick_dom)
  by (metis evenGet_c tsynbOneTick.rep_eq ubConc2stream ubrep_well)
   
lemma evenStreamBundle_empty_well[simp]:"ubWell ([c1 \<mapsto> \<epsilon>])"
 by(simp add: ubWell_def usclOkay_stream_def ctype_event_def)
  
lemma bot_assms: "EvenStream state\<cdot>\<bottom> = \<bottom>"
  apply(simp add: evenStream_insert)
  apply(subst h_bottom, simp add: getDom_def EvenAutomatonAutomaton.rep_eq ubDom_def)
  apply(simp add: getDom_def EvenAutomatonAutomaton.rep_eq)
  by(simp add: getRan_def EvenAutomatonAutomaton.rep_eq ubclLeast_ubundle_def)
   
    
end
  