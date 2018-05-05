theory NDAExample

imports NDA "../../timesyn/tsynBundle"

begin



(* END: tsynBundle *)



(* This are the actual states from MAA *)
datatype EvenAutomatonSubstate = TheOneAndOnly

(* And these have also the variables *)
datatype EvenAutomatonState = State EvenAutomatonSubstate nat

fun getSubState :: "EvenAutomatonState \<Rightarrow> EvenAutomatonSubstate" where
"getSubState (State automaton_s automaton_sum) = automaton_s"

fun getSum :: "EvenAutomatonState \<Rightarrow> nat" where
"getSum (State automaton_s automaton_sum) = automaton_sum"


datatype EvenAutomaton = A  nat | B  bool
instance EvenAutomaton :: countable
apply(intro_classes)
by(countable_datatype)


instantiation EvenAutomaton :: message
begin
    fun ctype_EvenAutomaton :: "channel \<Rightarrow> EvenAutomaton set" where
        "ctype_EvenAutomaton c1 = range A" | 
        "ctype_EvenAutomaton c2 = range B" 
instance
by(intro_classes)
end

lift_definition createC2Output :: "bool \<Rightarrow> EvenAutomaton event SB" is
  "\<lambda>b. [ c2 \<mapsto> \<up>(Msg (B b))]"
unfolding ubWell_def
unfolding usclOkay_stream_def
unfolding ctype_event_def
by simp


function evenAutomatonTransition :: "(EvenAutomatonState \<times> (channel \<rightharpoonup> EvenAutomaton event)) \<Rightarrow> ((EvenAutomatonState \<times> EvenAutomaton event SB) set rev)" where
  "evenAutomatonTransition (State TheOneAndOnly automaton_sum, [c1 \<mapsto> Msg a]) = (case a of A b
      \<Rightarrow> 
  (
    if((b+automaton_sum) mod 2 = 1) then (* Multiple transitions *)
      Rev {((State TheOneAndOnly (b+automaton_sum),(createC2Output False))), ((State TheOneAndOnly (b+automaton_sum+2),(createC2Output False)))}
    else if((b+automaton_sum) mod 2 = 0) then Rev {((State TheOneAndOnly (b+automaton_sum),(createC2Output True)))}
    else undefined
  )
  | _ \<Rightarrow> undefined)" |

 "evenAutomatonTransition (State TheOneAndOnly automaton_sum, [c1 \<mapsto> Tick]) = Rev {(State TheOneAndOnly (automaton_sum), (tsynbOneTick c2))}"  |

  "dom f\<noteq> {c1} \<Longrightarrow>  evenAutomatonTransition (_,f) = undefined"
  sorry
(* And termination!*)


(* Initial Configuration for the Automaton. The set contains tupel of "(initialState, initialOutput)" *)
definition EvenAutomatonInitial:: "(EvenAutomatonState \<times> EvenAutomaton event SB) set rev" where
"EvenAutomatonInitial = Rev {(State TheOneAndOnly 0, (tsynbOneTick c2)), (State TheOneAndOnly 42, (tsynbOneTick c2))}"

lift_definition EvenAutomatonAutomaton :: "(EvenAutomatonState, EvenAutomaton event) NDA" is 
  "(evenAutomatonTransition, EvenAutomatonInitial, Discr {c1}, Discr {c2})"
  sorry
  
definition EvenAutomatonSPS :: "EvenAutomaton event SPS" where
"EvenAutomatonSPS = nda_H\<cdot>EvenAutomatonAutomaton"



end