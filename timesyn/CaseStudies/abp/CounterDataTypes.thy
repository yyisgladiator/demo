



(* SWS: ? ? Kp was das macht *)

theory CounterDataTypes
imports HOLCF
begin

datatype InputEvent = one | two
instance InputEvent :: countable
by(countable_datatype)

datatype OutputEvent = timeout
instance OutputEvent :: countable
by(countable_datatype)

end