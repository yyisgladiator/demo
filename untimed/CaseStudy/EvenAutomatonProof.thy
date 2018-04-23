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
 lemma evenHdElem: assumes"x\<noteq>\<epsilon>" and "ubWell[c \<mapsto> x]" shows "inv convDiscrUp (sbHdElem\<cdot>(Abs_ubundle [c \<mapsto> x])) = [c1 \<mapsto> shd(x)]"
   sorry     
    

lemma [simp]:assumes "ubWell [c \<mapsto> x]" shows "sbRt\<cdot>(Abs_ubundle [c \<mapsto> x]) = (Abs_ubundle [c \<mapsto> srt\<cdot>x])"
  sorry 
        
lemma [simp]: "ubWell [c1 \<mapsto> \<up>\<surd> \<bullet> nat2even\<cdot>s]" 
  by (metis evenStreamBundle_well tsynmap_tick)
    
lemma ubConc2stream:"(ubConc sb1 \<cdot> sb2) . c = (sb1. c) \<bullet> (sb2. c)"
  sorry    

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
  apply(simp_all add:  evenStream_insert h_final ubdom_ubrep_eq getDom_def EvenAutomatonAutomaton.rep_eq h_out_dom evenHdElem autGetNextOutput_def autGetNextState_def getTransition_def)
  apply(cases "Parity.even (summe + m)")
  by(simp_all add: getRan_def EvenAutomatonAutomaton.rep_eq createC2Output_def ubConc2stream)
  
lemma [simp]:"nat2even\<cdot>(\<up>\<surd>) \<noteq> \<epsilon>"
  by (metis (mono_tags, lifting) event.simps(3) inject_scons lscons_conv sconc_fst_empty sup'_def tsynmap_bot tsynmap_tick)
    
lemma tick_assms: "EvenStream state\<cdot>(\<up>Tick \<bullet> xs) = \<up>Tick \<bullet> (EvenStream state\<cdot>xs)"
  apply(simp_all add: ubConc2stream evenStream_insert getRan_def tsynbOneTick_def h_final ubdom_ubrep_eq getDom_def EvenAutomatonAutomaton.rep_eq h_out_dom evenHdElem autGetNextOutput_def autGetNextState_def getTransition_def)
  by (metis fun_upd_same option.sel tsynbOneTick.abs_eq tsynbOneTick.rep_eq ubgetch_insert)
   
lemma evenStreamBundle_empty_well[simp]:"ubWell ([c1 \<mapsto> \<epsilon>])"
 by(simp add: ubWell_def usclOkay_stream_def ctype_event_def)
  
lemma bot_assms: "EvenStream state\<cdot>\<bottom> = \<bottom>"
  apply(simp add: evenStream_insert)
  apply(subst h_bottom, simp add: getDom_def EvenAutomatonAutomaton.rep_eq ubDom_def)
  apply(simp add: getDom_def EvenAutomatonAutomaton.rep_eq)
  by(simp add: getRan_def EvenAutomatonAutomaton.rep_eq ubclLeast_ubundle_def)
   
    
end
  