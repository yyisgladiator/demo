(*
 * DO NOT MODIFY!
 * This file was generated from Medium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * isartransformer 2.0.0
 *)
theory MediumStates
  imports MediumDatatype

begin


(* These are the actual states from MAA *)
datatype MediumSubstate = Single

(* And these have also the variables *)
datatype MediumState = MediumState MediumSubstate (* c = *) "nat"

(* Function to get the substate *)
fun getMediumSubState :: "MediumState \<Rightarrow> MediumSubstate" where
    "getMediumSubState (MediumState s _) = s"

(* Functions to get the variables *)
fun getC :: "MediumState \<Rightarrow> nat" where
"getC (MediumState _ var_c) = var_c"


end