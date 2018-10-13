(*
 * DO NOT MODIFY!
 * This file was generated from Receiver.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 12, 2018 1:15:28 PM by isartransformer 2.0.0
 *)
theory ReceiverStates
  imports ReceiverDatatype

begin


(* These are the actual states from MAA *)
datatype ReceiverSubstate = Rf | Rt

(* And these have also the variables *)
datatype ReceiverState = ReceiverState ReceiverSubstate 

(* Function to get the substate *)
fun getReceiverSubState :: "ReceiverState \<Rightarrow> ReceiverSubstate" where
    "getReceiverSubState (ReceiverState s ) = s"


end