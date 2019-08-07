theory eventAutomat

imports ndAutomaton

begin

(* An event Automaton saves the previous events in a buffer. Hence we need to change the state *)
datatype ('state::type,'csIn) eventState = EventState 'state "'csIn \<Rightarrow> M_pure list"


(* Move to "Channel" *)
fun getMessages :: "M \<Rightarrow> M_pure list" where
"getMessages (Untimed msg) = [msg]" |

"getMessages (Timed msgs) = msgs" |

"getMessages (Tsyn (Some msg)) = [msg]" |
"getMessages (Tsyn None) = []"




(*
  first parameter : eventAutomat transitions function
 second parameter : buffer
  
  result = set of possible transitions
*)
fun eventProcessOne:: "('cs \<Rightarrow>  'msg::type  \<Rightarrow> 'o::type set) \<Rightarrow> ('cs \<Rightarrow> 'msg list)  \<Rightarrow> (('cs \<Rightarrow> 'msg list) \<times> 'o) set" where
"eventProcessOne eventTrans buffers = 
    (let possibleActions = { c | c. buffers c \<noteq> []}
    in
    (if (\<forall>c. buffers c = []) then {(buffers, undefined)} else \<comment> \<open>TODO: undefined = tick... oder dummy message\<close>
  ({ ((\<lambda>cc. if(c=cc) then tl (buffers cc) else buffers cc), userNext) | c userNext. buffers c \<noteq> [] \<and> userNext \<in> eventTrans c (hd (buffers c))})))"


(* TODO: copy to sbElem *)
definition sbeGetMsgs:: "'cs sbElem \<Rightarrow> 'cs \<Rightarrow> M_pure list" where
"sbeGetMsgs sbe c \<equiv> if(chDom (TYPE ('cs)) = {}) then [] else getMessages (the (Rep_sbElem sbe) c)"

(* As a first step append all messages to the buffer. Hence we later have less if-else cases *)
definition eventAddToBuf::"'cs sbElem \<Rightarrow> ('cs \<Rightarrow> M_pure list) \<Rightarrow> 'cs \<Rightarrow> M_pure list" where
"eventAddToBuf sbe buf c = (buf c) @ (sbeGetMsgs sbe c)"  


(*
  \<^item> "'in \<Rightarrow> M" kann in einen eigene Datentyp zusammengefasst werden
  \<^item> "M" soll EINE Nachricht sein! keine "null" (bei tsyn) oder eine liste bei gezeitet!
  \<^item> das Gesamtsystem soll mit verschiedenenen Zeiten gleichzeitig umgehen können!
     \<^item> also nicht "M = M_gen tsyn"
*)
fun eventAutomatTransition:: "('state \<Rightarrow> 'in \<Rightarrow> M_pure \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) set) 
  \<Rightarrow> (('state::type,'in) eventState \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> (((('state::type,'in) eventState) \<times> 'out\<^sup>\<Omega>) set))" where
"eventAutomatTransition eventTrans (EventState s buffers) input = 
   {(EventState nextS nextList, nextOut) | nextS nextList nextOut. 
        (nextList, nextS, nextOut)\<in>(eventProcessOne (eventTrans s) (eventAddToBuf input buffers))
      } "

fun eventAutomatInitConfig::"('state \<times> 'out\<^sup>\<Omega>)set \<Rightarrow>  (('state::type,'in) eventState \<times> 'out\<^sup>\<Omega>) set"where
"eventAutomatInitConfig  S = {(EventState Sub (\<lambda>c. []),out) | Sub out. (Sub,out)\<in>S}"


setup_lifting type_definition_ndAutomaton

(* TODO: initiale konfiguration *)
lift_definition eventAut :: "('state \<Rightarrow> 'in \<Rightarrow> M_pure \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>) set) \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>)set \<Rightarrow>
  (('state::type,'in) eventState, 'in::{chan, finite}, 'out::chan) ndAutomaton" is
"\<lambda> eventTrans eventInit. (eventAutomatTransition eventTrans,eventAutomatInitConfig eventInit)"
  sorry




(*

(* Begin Framework: *)
datatype timeType = TUntimed | TTimed | TTsyn
(* End Framework *)


(* Begin Generated *)
datatype channel = c1 | c2 | c3

datatype M_pure = \<N> nat | \<B> bool


fun cMsg :: "channel \<Rightarrow> M_pure set" where
"cMsg c1 = range \<N>"

fun cTime :: "channel \<Rightarrow> timeType" where
"cTime c1 = TUntimed" |
"cTime c3 = TTimed"
(* End Generated *)


(* Begin Framework eg Channel/sbElem/SB *)

datatype M_timed = Untimed "M_pure" | Timed "M_pure list" | Tsyn "M_pure option"  (* option = tsyn *)

definition ctype::"channel \<Rightarrow> M_timed set" where
"ctype c \<equiv> if (cMsg c) = {} then {} else 
  case (cTime c) of TUntimed   \<Rightarrow> Untimed ` (cMsg c) | 
                   TTimed     \<Rightarrow>  Timed ` {ls. set ls \<subseteq> (cMsg c)} |
                   TTsyn      \<Rightarrow> Tsyn ` (insert None (Some ` cMsg c))"

lemma ctype_empty_gdw: "ctype c = {} \<longleftrightarrow> cMsg c = {}"
  apply(cases "(cTime c)")
  apply (auto simp add: ctype_def)
  by (metis bot.extremum empty_set)

type_synonym inAnd = bool

fun inAndChan::"('nat::type \<Rightarrow> 'a::type) \<Rightarrow> ('bool::type \<Rightarrow> 'a) \<Rightarrow>('nat\<times>'bool) \<Rightarrow> inAnd \<Rightarrow> 'a" where
"inAndChan Cc1 Cc2 (port_c1, port_c2) True = Cc1 port_c1" |
"inAndChan Cc1 Cc2 (port_c1, port_c2) False = Cc2 port_c2"

abbreviation "buildAndinSBE \<equiv> inAndChan (Timed o map \<B>) (Untimed o \<N>)" 

abbreviation "buildAndinSBs \<equiv> inAndChan (Tsyn o (map_option \<B>)) (Untimed o \<N>)"

interpretation andInSBE: sbeGen "buildAndinSBE"
  oops



subsection \<open>Merge\<close>

fun eventMT :: "state \<Rightarrow> inMerge \<Rightarrow> ('m\<times>'m)  \<Rightarrow> (state \<times> 'cs\<^sup>\<Omega>) set" where
"eventMT (True, _) cin2 m  = { (s,sendMessageAway (Msg m))}"


definition "eventMerge = eventAut eventMergeTransition"
*)
end