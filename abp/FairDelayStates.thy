(*
 * DO NOT MODIFY!
 * This file was generated from FairDelay.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * isartransformer 2.0.0
 *)
theory FairDelayStates
  imports FairDelayDatatype

begin


(* These are the actual states from MAA *)
datatype FairDelaySubstate = Single

(* And these have also the variables *)
datatype 'e FairDelayState = FairDelayState FairDelaySubstate (* ctr = *) "nat" (* buffer = *) "'e list"

(* Function to get the substate *)
fun getFairDelaySubState :: "'e FairDelayState \<Rightarrow> FairDelaySubstate" where
    "getFairDelaySubState (FairDelayState s _ _) = s"

(* Functions to get the variables *)
fun getCtr :: "'e FairDelayState \<Rightarrow> nat" where
"getCtr (FairDelayState _ var_ctr var_buffer) = var_ctr"

fun getBuffer :: "'e FairDelayState \<Rightarrow> 'e list" where
"getBuffer (FairDelayState _ var_ctr var_buffer) = var_buffer"


end