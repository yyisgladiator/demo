(*
 * DO NOT MODIFY!
 * This file was generated from Sender.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * isartransformer 2.0.0
 *)
theory SenderStates
  imports SenderDatatype

begin


(* These are the actual states from MAA *)
datatype SenderSubstate = Sf | St

(* And these have also the variables *)
datatype 'e SenderState = SenderState SenderSubstate (* buffer = *) "'e list" (* c = *) "nat"

(* Function to get the substate *)
fun getSenderSubState :: "'e SenderState \<Rightarrow> SenderSubstate" where
    "getSenderSubState (SenderState s _ _) = s"

(* Functions to get the variables *)
fun getBuffer :: "'e SenderState \<Rightarrow> 'e list" where
"getBuffer (SenderState _ var_buffer var_c) = var_buffer"

fun getC :: "'e SenderState \<Rightarrow> nat" where
"getC (SenderState _ var_buffer var_c) = var_c"


end