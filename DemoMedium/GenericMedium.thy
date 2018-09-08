theory GenericMedium

imports "../untimed/CaseStudy/dAutomaton" "../timesyn/tsynBundle"

begin
default_sort countable


(* BEGIN generic Part *)

datatype medState = OneState nat

datatype 'a abpMedMessage = abpMedData 'a 


instance abpMedMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation abpMedMessage :: (countable) message
begin
  fun ctype_abpMedMessage :: "channel  \<Rightarrow> 'a abpMedMessage set" where
  "ctype_abpMedMessage c = (
    if c = \<C> ''DoNotUseThisChannel_in'' then range abpMedData else            
    if c = \<C> ''DoNotUseThisChannel_out'' then range abpMedData else
    {})"

  instance
    by(intro_classes)
end


lift_definition createMedOutBundle :: "'a \<Rightarrow> 'a abpMedMessage tsyn SB" is
"\<lambda>x. [ \<C> ''DoNotUseThisChannel_out'' \<mapsto> \<up>(Msg (abpMedData x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp



fun medTransitionH :: "(medState \<times> ('a abpMedMessage tsyn)) \<Rightarrow> (medState \<times> 'a abpMedMessage tsyn SB)" where
"medTransitionH (OneState n, ((*In\<mapsto>*)Msg (abpMedData a))) = (OneState (Suc n), createMedOutBundle a)" |
"medTransitionH (state, ((*In\<mapsto>*)-)) = (state, tsynbNull (\<C> ''DoNotUseThisChannel_out''))"

fun abpMedTransition :: "(medState \<times> (channel \<rightharpoonup> 'a abpMedMessage tsyn)) \<Rightarrow> (medState \<times> 'a abpMedMessage tsyn SB)" where
"abpMedTransition (s,f) = (if dom(f) = {\<C> ''DoNotUseThisChannel_in''} then medTransitionH (s,(f\<rightharpoonup>\<C> ''DoNotUseThisChannel_in'')) else undefined)"

lift_definition MedAutomaton :: "(medState, 'a abpMedMessage tsyn) dAutomaton" is
  "(abpMedTransition, OneState 0 , (tsynbNull (\<C> ''DoNotUseThisChannel_out'')), {\<C> ''DoNotUseThisChannel_in''}, {\<C> ''DoNotUseThisChannel_out''})"
  sorry

definition GenMedSPF :: "'a abpMedMessage tsyn SPF" where
"GenMedSPF = da_H MedAutomaton"






(* END Generic part *)









(* BEGIN Special part *)

datatype abpMessage = ABPPair_nat_bool "(nat\<times>bool)" | ABPBool "bool" | ABPNat "nat"

instance abpMessage :: countable
  apply(intro_classes)
  by(countable_datatype)

instantiation abpMessage :: message
begin
  fun ctype_abpMessage :: "channel  \<Rightarrow> abpMessage set" where
  "ctype_abpMessage c = (
    if c = \<C> ''as'' then range ABPBool else              (* MediumRS.as -> Sender.as *)
    if c = \<C> ''dr'' then range ABPPair_nat_bool else     (* MediumSR.dr -> Receiver.dr *)
    if c = \<C> ''ds'' then range ABPPair_nat_bool else     (* Sender.ds -> MediumSR.ds *)
    if c = \<C> ''ar'' then range ABPBool else              (* Receiver.ar -> MediumRS.ar *)
    if c = \<C> ''o'' then range ABPNat else                (* Receiver.o *)
    if c = \<C> ''i'' then range ABPNat else                (* Sender.i *)
    {})"

  instance
    by(intro_classes)
end


(* RSMed takes an bool as input *)
(* For the love of god, this function has to be nicer. This is JUST a demo what it should do *)

(* It takes an input for "MediumRS" (on channel 'as') and converts the datatype/channel to an input for the genMedium *)
definition convertToRSMedInput:: "abpMessage tsyn SB \<rightarrow> bool abpMedMessage tsyn SB" where
"convertToRSMedInput \<equiv> \<Lambda> sb. Abs_ubundle ([\<C> ''DoNotUseThisChannel_in'' \<mapsto>  
        tsynMap (\<lambda>e. abpMedData ((inv ABPBool) e))\<cdot>(sb . \<C> ''as'')])" 

(* Same, but different direction *)
definition convertFromRSMedOutput:: "bool abpMedMessage tsyn SB \<rightarrow> abpMessage tsyn SB" where
"convertFromRSMedOutput = undefined" 



(* This is how it should look like... does not work right now because ufun cannot change types *)
definition RSMed::"abpMessage tsyn SPF" where
"RSMed = ufApplyIn convertToRSMedInput\<cdot>(ufApplyOut convertFromRSMedOutput\<cdot>(GenMedSPF))"

end