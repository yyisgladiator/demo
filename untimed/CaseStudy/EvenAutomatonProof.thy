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
    sorry

lemma evenStreamBundle_lub: assumes "chain Y" shows"(Abs_ubundle [c1 \<mapsto> nat2even\<cdot>(\<Squnion>i. Y i)]) = (\<Squnion>i. Abs_ubundle [c1 \<mapsto>  nat2even\<cdot>(Y i)])"
  sorry

lemma evenStreamBundle_chain:assumes "chain Y" shows"chain (\<lambda>i::nat. Abs_ubundle [c1 \<mapsto> nat2even\<cdot>(Y i)])"
  sorry

lemma evenHdElem: assumes"x\<noteq>\<epsilon>" shows "inv convDiscrUp (sbHdElem\<cdot>(Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x])) = [c1 \<mapsto> shd(nat2even\<cdot>x)]"
  sorry
       
(*ToDo end*)
  
  
definition EvenStream::"EvenAutomatonState \<Rightarrow> nat event stream \<rightarrow> EvenAutomaton event stream" where
"EvenStream state \<equiv> (\<Lambda> s. ((h EvenAutomatonAutomaton state) \<rightleftharpoons> (Abs_ubundle [c1 \<mapsto> (nat2even\<cdot>s)])) . c2)"


lemma ubclLeast_empty: assumes "c\<in>Dom" shows "ubclLeast Dom  .  c = \<epsilon>"
  by (simp add: assms ubclLeast_ubundle_def)

lemma evenGet_c1[simp]:"Abs_ubundle [c1 \<mapsto> nat2even\<cdot>x]  .  c1 =  nat2even\<cdot>x"
  by (metis evenStreamBundle_well fun_upd_same option.sel ubgetch_ubrep_eq)   

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
proof(induction arbitrary: ooo summe rule: tsyn_ind [of _xs])
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case sorry
  next
    case (3 a s)
    then show ?case sorry
  next
    case (4 s)
    then show ?case sorry
  qed
     
lemma [simp]:"nat2even\<cdot>(\<up>\<surd>) \<noteq> \<epsilon>"
  by (metis (mono_tags, lifting) event.simps(3) inject_scons lscons_conv sconc_fst_empty sup'_def tsynmap_bot tsynmap_tick)
    
lemma tick_assms: "EvenStream state\<cdot>(\<up>Tick \<bullet> xs) = \<up>Tick \<bullet> (EvenStream state\<cdot>xs)"
proof(induction rule: tsyn_ind [of _xs])
  case 1
  then show ?case by simp
next
  case 2
  then show ?case
    apply(simp add: evenStream_insert)
    apply(subst h_final, simp_all add: getDom_def getRan_def ubdom_insert EvenAutomatonAutomaton.rep_eq)
    apply(simp add: ubgetch_ubrep_eq)
    sorry
next
  case (3 a s)
  then show ?case sorry
next
  case (4 s)
  then show ?case sorry
qed
 
lemma evenStreamBundle_empty_well[simp]:"ubWell ([c1 \<mapsto> \<epsilon>])"
 by(simp add: ubWell_def usclOkay_stream_def ctype_event_def)
  
lemma bot_assms: "EvenStream state\<cdot>\<bottom> = \<bottom>"
  apply(simp add: evenStream_insert)
  apply(subst h_bottom, simp add: getDom_def EvenAutomatonAutomaton.rep_eq ubDom_def)
  apply(simp add: getDom_def EvenAutomatonAutomaton.rep_eq)
  apply(subst ubgetch_ubrep_eq, auto)
  by(simp add: getRan_def EvenAutomatonAutomaton.rep_eq ubclLeast_ubundle_def)
   
    
end
  