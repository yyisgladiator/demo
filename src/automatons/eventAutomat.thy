theory eventAutomat

imports ndAutomaton

begin

(* An event Automaton saves the previous events in a buffer. Hence we need to change the state *)
datatype ('state::type,'csIn) eventState = EventState 'state "'csIn \<Rightarrow> M list"




fun appendMsg :: "'m::countable tsyn \<Rightarrow> 'm list \<Rightarrow> 'm list" where
"appendMsg (Msg m) xs = xs @ [m]" | 
"appendMsg    -    xs = xs"


(* As a first step append all messages to the buffer. Hence we later have less if-else cases *)
definition eventAddToBuf::"'m::message tsyn sbElem \<Rightarrow> (channel \<Rightarrow> 'm list) \<Rightarrow> channel \<Rightarrow> 'm list" where
"eventAddToBuf sbe buf c = (if(c\<in>sbeDom sbe) then appendMsg ((Rep_sbElem sbe)\<rightharpoonup> c) (buf c) else buf c)"



(*
  \<^item> "'in \<Rightarrow> M" kann in einen eigene Datentyp zusammengefasst werden
  \<^item> "M" soll EINE Nachricht sein! keine "null" (bei tsyn) oder eine liste bei gezeitet!
  \<^item> das Gesamtsystem soll mit verschiedenenen Zeiten gleichzeitig umgehen können!
     \<^item> also nicht "M = M_gen tsyn"
*)
fun eventAutomatTransition:: "('state \<Rightarrow> 'in \<Rightarrow> M \<Rightarrow> 'out\<^sup>\<Omega>) 
  \<Rightarrow> (('state::type,'in) eventState \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> (('state \<times> 'out\<^sup>\<Omega>) set))" where
"eventAutomatTransition eventTrans (EventState s buffers) input = undefined "

(* TODO: initiale konfiguration *)
definition eventAut :: "('state \<Rightarrow> 'in \<Rightarrow> M \<Rightarrow> 'out\<^sup>\<Omega>) \<Rightarrow>
  (('state::type,'in) eventState, 'in::{chan, finite}, 'out::chan) ndAutomaton" where
"eventAut = undefined"






(* Begin Framework: *)
datatype timeType = TUntimed | TTimed | TTsyn
(* End Framework *)


(* Begin Generated *)
datatype channel = c1 | c2 | c3

datatype M_help = \<N> nat | \<B> bool


fun cMsg :: "channel \<Rightarrow> M_help set" where
"cMsg c1 = range \<N>"

fun cTime :: "channel \<Rightarrow> timeType" where
"cTime c1 = TUntimed" |
"cTime c3 = TTimed"
(* End Generated *)


(* Begin Framework eg Channel/sbElem/SB *)

datatype M_timed = Untimed "M_help" | Timed "M_help list" | Tsyn "M_help option"  (* option = tsyn *)

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

(* Garantiert nicht "M" verwenden! ! ! *)
fun eventMergeTransition :: "'state \<Rightarrow> 'cs \<Rightarrow> (M\<times>M)  \<Rightarrow> ('state \<times> 'cs\<^sup>\<Omega>) set" where
"eventMergeTransition s _ m  = { (s,sendMessageAway (Msg m))}"


definition "eventMerge = eventAut {c1, c2} {c3} eventMergeTransition { (n,sendMessageAway -) | n. True}"

end