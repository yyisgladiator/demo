theory EvenAutomatonProof

imports EvenAutomaton EvenStream

begin
lemma evenStreamBundle_well[simp]:assumes "sdom\<cdot>s \<subseteq> ctype c" shows "ubWell ([c \<mapsto> s::EvenAutomaton event stream])"
by(simp add: ubWell_def usclOkay_stream_def assms)


definition EvenStream::"EvenAutomatonState \<Rightarrow> nat event stream \<rightarrow> EvenAutomaton event stream" where
"EvenStream state \<equiv> (\<Lambda> s. ((h EvenAutomatonAutomaton state) \<rightleftharpoons> (Abs_ubundle [c1 \<mapsto> nat2even s])) . c2)"

fun evenMakeSubstate :: "bool \<Rightarrow> EvenAutomatonSubstate" where
"evenMakeSubstate True = Even" | 
"evenMakeSubstate False = Odd"

lemma evenStream_insert:"EvenStream state\<cdot>s = ((h EvenAutomatonAutomaton state) \<rightleftharpoons> (Abs_ubundle [c1 \<mapsto> s])) . c2"
  apply(simp add: EvenStream_def,rule beta_cfun)
proof(rule Cont.contI2)
  show"monofun (\<lambda>x::EvenAutomaton event stream. (h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> x])  .  c2)"
   apply(rule monofunI)
    sorry
next
  fix Y:: "nat \<Rightarrow>EvenAutomaton event stream"
  assume a1: "chain Y"
  assume a2:"chain (\<lambda>i::nat. (h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> Y i])  .  c2)"
  have "\<And>i. sdom\<cdot>(Y i) \<subseteq> ctype c1"
    sorry
  have h1:"(Abs_ubundle [c1 \<mapsto> \<Squnion>i. Y i]) = (\<Squnion>i. Abs_ubundle [c1 \<mapsto>  Y i])"
    sorry
  have h2:"chain (\<lambda>i::nat. Abs_ubundle [c1 \<mapsto> Y i])"
    sorry
  show "(h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> \<Squnion>i::nat. Y i])  .  c2 \<sqsubseteq> 
          (\<Squnion>i::nat. (h EvenAutomatonAutomaton state \<rightleftharpoons> Abs_ubundle [c1 \<mapsto> Y i])  .  c2)"
    apply(simp add: h1, subst contlub_cfun_arg, simp add: h2)
    sorry
qed
  

lemma  msg_assms: "EvenStream (State ooo summe)\<cdot>(\<up>(Msg (A m)) \<bullet> xs)
                 = \<up>(Msg (B (Parity.even (summe + m)))) \<bullet> (EvenStream (State (evenMakeSubstate (Parity.even (summe + m)))  (summe + m))\<cdot>xs)"
  sorry
(*  proof(induction arbitrary: ooo summe rule: tsyn_ind [of _xs])
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
  qed*)

lemma tick_assms: "EvenStream state\<cdot>(\<up>Tick \<bullet> xs) = \<up>Tick \<bullet> (f state\<cdot>xs)"
  sorry
(*proof(induction rule: tsyn_ind [of _xs])
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
qed*)
      
lemma bot_assms: "EvenStream state\<cdot>\<bottom> = \<bottom>"
  apply(simp add: evenStream_insert)
  apply(subst h_bottom, simp add: getDom_def EvenAutomatonAutomaton.rep_eq ubDom_def)
  apply(simp add: getDom_def EvenAutomatonAutomaton.rep_eq)
  apply(subst ubgetch_ubrep_eq, auto)
  by(simp add: getRan_def EvenAutomatonAutomaton.rep_eq ubclLeast_ubundle_def)
    
end
  