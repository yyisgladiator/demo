(*
 * DO NOT MODIFY!
 * This file was generated from IdMedium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 12, 2018 1:15:32 PM by isartransformer 2.0.0
 *)
theory IdMediumStates
  imports MediumDatatype

begin


(* These are the actual states from MAA *)
datatype IdMediumSubstate = Single

(* And these have also the variables *)
datatype IdMediumState = IdMediumState IdMediumSubstate 

(* Function to get the substate *)
fun getIdMediumSubState :: "IdMediumState \<Rightarrow> IdMediumSubstate" where
    "getIdMediumSubState (IdMediumState s ) = s"


end