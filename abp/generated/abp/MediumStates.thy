(*
 * DO NOT MODIFY!
 * This file was generated from Medium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 16, 2018 10:17:27 PM by isartransformer 3.1.0
 *)
theory MediumStates
  imports MediumDatatype

begin


(* These are the actual states from MAA *)
datatype MediumSubstate = Single

(* And these have also the variables *)
datatype MediumState = MediumState MediumSubstate (* coin = *) "int"

(* Function to get the substate *)
fun getMediumSubState :: "MediumState \<Rightarrow> MediumSubstate" where
    "getMediumSubState (MediumState s _) = s"

(* Functions to get the variables *)
fun getCoin :: "MediumState \<Rightarrow> int" where
"getCoin (MediumState _ var_coin) = var_coin"


end