(*  Title:  EvenStream
    Author: Sebastian Stüber
    e-mail: sebastian.stueber@rwth-aachen.de

    Description: Part of a case Study for a generated Automaton. 
      This part only deals with (tsyn) streams, bundles are somewhere else
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

(* transition function for evenAutomaton on tsyn streams *)
fun evenTransition :: "EvenAutomatonState \<Rightarrow> EvenAutomaton tsyn \<Rightarrow> (EvenAutomaton tsyn \<times> EvenAutomatonState)" where
"evenTransition s null = (null, s)" |

"evenTransition (State _ summe) (Msg (A input)) = (Msg (B (Parity.even (summe + input))), State (evenMakeSubstate (Parity.even (summe + input))) (summe+input)) " 



definition evenInitialState where
"evenInitialState = State Even 0"

abbreviation evenStream:: "EvenAutomaton tsyn stream \<rightarrow> EvenAutomaton tsyn stream" where
"evenStream \<equiv> sscanlA evenTransition evenInitialState"


lemma evenstream_bot: "sscanlA evenTransition state\<cdot>\<bottom> = \<bottom>"
  by simp

lemma evenstream_tick: "sscanlA evenTransition state\<cdot>(\<up>null \<bullet> xs) = \<up>null \<bullet> (sscanlA evenTransition state\<cdot>xs)"
  by simp

lemma evenstream_msg:  "sscanlA evenTransition (State ooo summe) \<cdot>(\<up>(Msg (A m)) \<bullet> xs) 
    = \<up>(Msg (B (Parity.even (summe + m)))) \<bullet> (sscanlA evenTransition (State (evenMakeSubstate (Parity.even (summe + m)))  (summe + m))\<cdot>xs)"
  by simp


(* convert the datatypes *)
abbreviation nat2even:: "nat tsyn stream \<rightarrow> EvenAutomaton tsyn stream" where
"nat2even \<equiv> tsynMap A"

(* convert the datatypes *)
abbreviation bool2even:: "bool tsyn stream \<rightarrow> EvenAutomaton tsyn stream" where
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
   apply (simp add: tsynmap_sconc_msg tsynscanl_sconc_msg)
  by (simp add: tsynmap_sconc_null tsynscanl_sconc_null)

lemma evenstream_final: "evenStream\<cdot>(nat2even\<cdot>s) = bool2even\<cdot>(tsynMap Parity.even\<cdot>(tsynSum\<cdot>s))"
  by (simp add: evenInitialState_def tsynSum_def evenstream_final_h)

lemma evenStreamBundle_well[simp]:"ubWell ([c1 \<mapsto> (nat2even\<cdot>s)])"
  apply(simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def)
proof(induction rule: tsyn_ind [of _s])
  case adm
  then show ?case
  proof(rule admI)
    fix Y::"nat \<Rightarrow> nat tsyn stream"
    assume a1: "chain Y"
    assume a2: "\<forall>i::nat. sdom\<cdot>(nat2even\<cdot>(Y i)) \<subseteq> insert null (Msg ` range A)"
    show "sdom\<cdot>(nat2even\<cdot>(\<Squnion>i::nat. Y i)) \<subseteq> insert null (Msg ` range A)"
        by (metis a1 a2 ch2ch_Rep_cfunR contlub_cfun_arg subset_cont)
    qed
next
  case bot
  then show ?case by simp
next
  case (msg a s)
  then show ?case 
    by (simp add: msg.IH tsynmap_sconc_msg)
next
  case (null s)
  then show ?case
    by (simp add: null.IH tsynmap_sconc_null)
qed

lemma evenStreamBundle_tick_well[simp]: "ubWell [c1 \<mapsto> \<up>null \<bullet> nat2even\<cdot>s]" 
  by (metis evenStreamBundle_well tsynmap_sconc_null)

lemma evenStreamBundle_msg_well[simp]:"ubWell [c1 \<mapsto> \<up>(\<M> A m) \<bullet> nat2even\<cdot>xs]"
  by (metis evenStreamBundle_well tsynmap_sconc_msg)


subsection \<open>Rek2evenStream\<close>

(*fourth assumption for Rek2evenStream*)  
lemma type_assms:"tsynDom\<cdot>(nat2even\<cdot>xs) \<subseteq> range A"
proof(induction rule: tsyn_ind [of _xs])
  case adm
  then show ?case
      proof(rule admI)
    fix Y::"nat \<Rightarrow> nat tsyn stream"
    assume a1: "chain Y"
    assume a2: "\<forall>i::nat. tsynDom\<cdot>(nat2even\<cdot>(Y i)) \<subseteq> range A"
    show "tsynDom\<cdot>(nat2even\<cdot>(\<Squnion>i::nat. Y i)) \<subseteq> range A"
      by (metis a1 a2 ch2ch_Rep_cfunR contlub_cfun_arg subset_cont)
  qed
next
  case bot
  then show ?case
    by(simp add: tsyndom_insert)
next
  case (msg a s)
  then show ?case
    by (simp add: tsyndom_sconc_msg_sub2 tsynmap_sconc_msg)
next
  case (null s)
  then show ?case
    by (simp add: tsyndom_sconc_null tsynmap_sconc_null)
qed
  
(* convert the rekursive definition of the automaton in our nice evenStream function *)
lemma rek2evenstream: assumes msg: "\<And> ooo summe m xs. f (State ooo summe)\<cdot>(\<up>(Msg m) \<bullet> (xs::nat tsyn stream))
                 = \<up>(Msg (B (Parity.even (summe + m)))) \<bullet> (f (State (evenMakeSubstate (Parity.even (summe + m)))  (summe + m))\<cdot>xs)"
      and a_tick: "\<And> state xs. f state\<cdot>(\<up>null \<bullet> xs) = \<up>null \<bullet> (f state\<cdot>xs)"
      and a_bot: "\<And>state. f state\<cdot>\<bottom> = \<bottom>"
    shows "f (State ooo summe)\<cdot>xs = sscanlA evenTransition (State ooo summe)\<cdot>(nat2even\<cdot>xs)"
  proof(induction arbitrary: ooo summe rule: tsyn_ind [of _xs])
  case adm
  then show ?case by simp
next
  case bot
  then show ?case using a_bot by simp
next
  case (msg a s)
  have h1: "tsynDom\<cdot>(nat2even\<cdot>s) \<subseteq> range A"
    by (simp add: type_assms)
  then show ?case
    by (simp add: assms(1) msg.IH tsynmap_sconc_msg)
next
case (null s)
then show ?case
  by (simp add: a_tick tsynmap_sconc_null)
qed
  
    
lemma SteGre1:"Parity.even n \<longrightarrow> tsynDom\<cdot>ts \<subseteq> { n | n. (Parity.even n)} \<longrightarrow> 
              sscanlA evenTransition (State Even n)\<cdot>(nat2even\<cdot>ts) = bool2even\<cdot>(tsynMap (\<lambda> e. True)\<cdot>ts)"
proof(induction arbitrary: n rule: tsyn_ind [of _ts])
  case adm
  then show ?case 
    by simp
next
  case bot
  then show ?case 
    by simp
next
  case (msg m s)
  have h1:" semiring_parity_class.even n \<longrightarrow>tsynDom\<cdot>(\<up>(\<M> m) \<bullet> s) \<subseteq> {n |n::nat. semiring_parity_class.even n} \<longrightarrow> 
            sscanlA evenTransition (EvenAutomatonState.State Even n)\<cdot>(nat2even\<cdot>(\<up>(\<M> m) \<bullet> s)) = 
            bool2even\<cdot>(\<up>(\<M> True)) \<bullet> sscanlA evenTransition (EvenAutomatonState.State Even (n + m))\<cdot>(nat2even\<cdot>s)"
  proof(auto)
    assume a1:" semiring_parity_class.even n"
    assume a2:"tsynDom\<cdot>(\<up>(\<M> m) \<bullet> s) \<subseteq> Collect semiring_parity_class.even"
    then have "semiring_parity_class.even m"
      by(simp add: tsyndom_insert, auto)
    then show "sscanlA evenTransition (EvenAutomatonState.State Even n)\<cdot>(nat2even\<cdot>(\<up>(\<M> m) \<bullet> s)) =
               bool2even\<cdot>(\<up>(\<M> True)) \<bullet> sscanlA evenTransition (EvenAutomatonState.State Even (n + m))\<cdot>(nat2even\<cdot>s)"
      by(simp add: tsynMap_def a1)
  qed
  then show ?case
  proof(auto,subst msg.IH,simp)
    assume a1:"tsynDom\<cdot>(\<up>(\<M> m) \<bullet> s) \<subseteq> Collect semiring_parity_class.even"
    then show "semiring_parity_class.even m"
      by(simp add: tsyndom_insert, auto)
  next
    assume a1:"tsynDom\<cdot>(\<up>(\<M> m) \<bullet> s) \<subseteq> Collect semiring_parity_class.even"
    then show "tsynDom\<cdot>s \<subseteq> {n |n::nat. semiring_parity_class.even n}"
      by (meson tsyndom_sconc_msg_sub)
  next
    show "bool2even\<cdot>(\<up>(\<M> True)) \<bullet> bool2even\<cdot>(tsynMap (\<lambda>e::nat. True)\<cdot>s) = bool2even\<cdot>(tsynMap (\<lambda>e::nat. True)\<cdot>(\<up>(\<M> m) \<bullet> s))"
      by (metis tsynmap_sconc tsynmap_sconc_msg)
  qed    
next
  case (null s)
  then show ?case
    by (simp add: tsyndom_sconc_null tsynmap_sconc_null) 
qed

end