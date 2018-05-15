(*  Title:  EvenStream
    Author: Sebastian Stüber
    e-mail: sebastian.stueber@rwth-aachen.de

    Description: Part of a case Study for a generated Automaton. 
      This part only deals with (event) streams, bundles are somewhere else
*)


theory EvenStream

imports EvenAutomaton 

begin

(********************************)
    section \<open>Datentypen\<close>
(********************************)


instance EvenAutomatonSubstate :: countable
  apply(intro_classes)
  by(countable_datatype)

instance EvenAutomatonState :: countable
  apply(intro_classes)
  by(countable_datatype)

fun getSubState :: "EvenAutomatonState \<Rightarrow> EvenAutomatonSubstate" where
"getSubState (State automaton_s automaton_sum) = automaton_s"

fun getSum :: "EvenAutomatonState \<Rightarrow> nat" where
"getSum (State automaton_s automaton_sum) = automaton_sum"


(********************************)
    section \<open>Even Function\<close>
(********************************)

(* Helper function to make the transition a one-liner *)
fun evenMakeSubstate :: "bool \<Rightarrow> EvenAutomatonSubstate" where
"evenMakeSubstate True = Even" | 
"evenMakeSubstate False = Odd"

(* transition function for evenAutomaton on event streams *)
fun evenTransition :: "EvenAutomatonState \<Rightarrow> EvenAutomaton event \<Rightarrow> (EvenAutomaton event \<times> EvenAutomatonState)" where
"evenTransition s Tick = (Tick, s)" |

"evenTransition (State _ summe) (Msg (A input)) = (Msg (B (Parity.even (summe + input))), State (evenMakeSubstate (Parity.even (summe + input))) (summe+input)) " 



definition evenInitialState where
"evenInitialState = State Even 0"

abbreviation evenStream:: "EvenAutomaton event stream \<rightarrow> EvenAutomaton event stream" where
"evenStream \<equiv> sscanlA evenTransition evenInitialState"


lemma evenstream_bot: "sscanlA evenTransition state\<cdot>\<bottom> = \<bottom>"
  by simp

lemma evenstream_tick: "sscanlA evenTransition state\<cdot>(\<up>Tick \<bullet> xs) = \<up>Tick \<bullet> (sscanlA evenTransition state\<cdot>xs)"
  by simp

lemma evenstream_msg:  "sscanlA evenTransition (State ooo summe) \<cdot>(\<up>(Msg (A m)) \<bullet> xs) 
    = \<up>(Msg (B (Parity.even (summe + m)))) \<bullet> (sscanlA evenTransition (State (evenMakeSubstate (Parity.even (summe + m)))  (summe + m))\<cdot>xs)"
  by simp


(* convert the datatypes *)
abbreviation nat2even:: "nat event stream \<rightarrow> EvenAutomaton event stream" where
"nat2even \<equiv> tsynMap A"

(* convert the datatypes *)
abbreviation bool2even:: "bool event stream \<rightarrow> EvenAutomaton event stream" where
"bool2even \<equiv> tsynMap B"



(********************************)
    section \<open>Lemma\<close>
(********************************)

subsection \<open>evenStream\<close>

lemma "#(evenStream\<cdot>s) = #s"
  by simp

lemma evenstream_final_h: "sscanlA evenTransition (State ooo n)\<cdot>(nat2even\<cdot>s) = bool2even\<cdot>(tsynMap Parity.even\<cdot>(tsynScanl plus n\<cdot>s))"
  apply(induction arbitrary: n ooo rule: ind [of _ s])
    apply auto
  apply(rename_tac a s n ooo)
  apply(case_tac a)
  by auto

lemma evenstream_final: "evenStream\<cdot>(nat2even\<cdot>s) = bool2even\<cdot>(tsynMap Parity.even\<cdot>(tsynSum\<cdot>s))"
  by (simp add: evenInitialState_def tsynSum_def evenstream_final_h)

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

lemma evenStreamBundle_tick_well[simp]: "ubWell [c1 \<mapsto> \<up>\<surd> \<bullet> nat2even\<cdot>s]" 
  by (metis evenStreamBundle_well tsynmap_tick)

lemma evenStreamBundle_msg_well[simp]:"ubWell [c1 \<mapsto> \<up>(\<M> A m) \<bullet> nat2even\<cdot>xs]"
  by (metis evenStreamBundle_well tsynmap_msg)


subsection \<open>Rek2evenStream\<close>

(*fourth assumption for Rek2evenStream*)  
lemma type_assms:"tsynDom\<cdot>(nat2even\<cdot>xs) \<subseteq> range A"
proof(induction rule: tsyn_ind [of _xs])
  case 1
  then show ?case
      proof(rule admI)
    fix Y::"nat \<Rightarrow> nat event stream"
    assume a1: "chain Y"
    assume a2: "\<forall>i::nat. tsynDom\<cdot>(nat2even\<cdot>(Y i)) \<subseteq> range A"
    show "tsynDom\<cdot>(nat2even\<cdot>(\<Squnion>i::nat. Y i)) \<subseteq> range A"
      by (metis a1 a2 ch2ch_Rep_cfunR contlub_cfun_arg subset_cont)
  qed
next
  case 2
  then show ?case
    by(simp add: tsyndom_insert)
next
  case (3 a s)
  then show ?case
    by (simp add: tsyndom_conc_sub)
next
  case (4 s)
  then show ?case 
    by simp
qed
  
(* convert the rekursive definition of the automaton in our nice evenStream function *)
lemma rek2evenstream: assumes msg: "\<And> ooo summe m xs. f (State ooo summe)\<cdot>(\<up>(Msg m) \<bullet> (xs::nat event stream))
                 = \<up>(Msg (B (Parity.even (summe + m)))) \<bullet> (f (State (evenMakeSubstate (Parity.even (summe + m)))  (summe + m))\<cdot>xs)"
      and tick: "\<And> state xs. f state\<cdot>(\<up>Tick \<bullet> xs) = \<up>Tick \<bullet> (f state\<cdot>xs)"
      and bot: "\<And>state. f state\<cdot>\<bottom> = \<bottom>"
    shows "f (State ooo summe)\<cdot>xs = sscanlA evenTransition (State ooo summe)\<cdot>(nat2even\<cdot>xs)"
  proof(induction arbitrary: ooo summe rule: tsyn_ind [of _xs])
  case 1
  then show ?case by simp
next
  case 2
  then show ?case using bot by simp
next
  case (3 a s)
  have h1: "tsynDom\<cdot>(nat2even\<cdot>s) \<subseteq> range A"
    using "3.prems" tsyndom_sub type_assms by fastforce
  then show ?case by(simp add: msg h1 "3.IH")
next
case (4 s)
then show ?case
  by (simp add: tick)
qed

end