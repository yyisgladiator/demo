theory eventAutomaton

imports ndAutomaton

begin

default_sort type

(* An event Automaton saves the previous events in a buffer. Hence we need to change the state *)
datatype ('s,'m) eventState = EventState 's "channel \<Rightarrow> 'm list"


fun eventStepChannel :: "('m  \<Rightarrow> 'o set) \<Rightarrow> 'm::countable tsyn \<Rightarrow> 'm list \<Rightarrow> (('m list \<times> 'o) set)" where
"eventStepChannel f   -    (x#xs)  = ((\<lambda>Out. (xs, Out))   ` f x)"   |
"eventStepChannel f   -      []    =  {}" |   (* Kann keinen Schritt machen *)
"eventStepChannel f (Msg m)(x#xs)  = ((\<lambda>Out. (xs @ [m], Out))   ` f x) " | (* ? Should every message be processed?*)
"eventStepChannel f (Msg m)  []    =((\<lambda>Out. ([], Out))          ` f m)"



fun eventAutomatTransition:: "channel set \<Rightarrow> (channel \<Rightarrow> 's \<Rightarrow> 'm  \<Rightarrow> ('s \<times> 'm::message tsyn SB) set) 
  \<Rightarrow> (('s, 'm) eventState \<times> 'm tsyn sbElem) \<Rightarrow> (('s, 'm) eventState \<times> 'm tsyn SB) set" where
"eventAutomatTransition Dom eventTrans ((EventState s buffers) , input) = (if (sbeDom input) = Dom then 
    (( { (EventState nextS (\<lambda> cc. if (c = cc) then nextList else buffers c), nextOut) 
    | c nextS nextList nextOut. c\<in>Dom \<and>(nextList, nextS, nextOut)\<in>(eventStepChannel (eventTrans c s) ((Rep_sbElem input)\<rightharpoonup> c) (buffers c))})) 
  else undefined) "

definition eventAutomatonInitial :: "('s \<times> 'm::message tsyn SB) set \<Rightarrow> (('s, 'm) eventState \<times> 'm::message tsyn SB) set" where
"eventAutomatonInitial initial = (\<lambda> (s,ausgabe). (EventState s (\<lambda>c. []), ausgabe)) ` initial"

definition eventAut :: "channel set \<Rightarrow> channel set \<Rightarrow>  (channel \<Rightarrow> 's \<Rightarrow> 'm::message  \<Rightarrow> ('s \<times> 'm tsyn SB) set) => ('s \<times> 'm::message tsyn SB) set 
    \<Rightarrow> (('s, 'm) eventState ,'m tsyn) ndAutomaton" where
"eventAut Dom Ran transition initial = 
  Abs_ndAutomaton ((eventAutomatTransition Dom transition), (eventAutomatonInitial initial), Discr Dom, Discr Ran)"





section \<open>Example \<close>

definition sendMessageAway:: "'m \<Rightarrow> 'm SB" where
"sendMessageAway = undefined" (* Funktion wird autogeneriert *)


subsection \<open>Fair Medium\<close>

fun eventMediumFairTransition :: "channel \<Rightarrow> nat \<Rightarrow> 'm::message  \<Rightarrow> (nat \<times> 'm tsyn SB) set" where
"eventMediumFairTransition c    0     m  = { (n,sendMessageAway (Msg m)) | n. True}" |
"eventMediumFairTransition c (Suc n)  m  = { (n, sendMessageAway -)}"


definition "eventMediumFair = eventAut {c1} {c2} eventMediumFairTransition { (n,sendMessageAway -) | n. True}"







subsection \<open>Merge\<close>



fun eventMergeTransition :: "channel \<Rightarrow> 's \<Rightarrow> 'm::message  \<Rightarrow> ('s \<times> 'm tsyn SB) set" where
"eventMergeTransition _ s m  = { (s,sendMessageAway (Msg m))}"


definition "eventMerge = eventAut {c1, c2} {c3} eventMergeTransition { (n,sendMessageAway -) | n. True}"


end