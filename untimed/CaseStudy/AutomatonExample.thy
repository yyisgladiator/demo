theory AutomatonExample

imports Automaton "../../timesyn/tsynBundle"

begin

datatype State = myState


instantiation nat :: message
begin
  fun ctype_nat :: "channel \<Rightarrow> nat set" where
  "ctype_nat _ = UNIV" 

  instance
    by(intro_classes)
end

(* Ignore input, output one tick on c1 *)
fun myTransition :: "(State \<times>(channel \<rightharpoonup> nat event)) \<Rightarrow> (State \<times> nat event SB)" where
"myTransition _ = (myState, tsynbOneTick c1)"

lift_definition myAutomaton :: "(State, nat event) automaton" is "(myTransition, myState, tsynbOneTick c1, {c2}, {c1})"
  by simp



definition mySPF :: "nat event SPF" where
"mySPF = H myAutomaton"


(* TODO: final lemma over mySPF *) 


end