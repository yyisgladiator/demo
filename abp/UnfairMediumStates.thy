(*
 * DO NOT MODIFY!
 * This file was generated from UnfairMedium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * isartransformer 2.0.0
 *)
theory UnfairMediumStates
  imports UnfairMediumDatatype

begin


(* These are the actual states from MAA *)
datatype UnfairMediumSubstate = Single

(* And these have also the variables *)
datatype UnfairMediumState = UnfairMediumState UnfairMediumSubstate (* coin = *) "nat"

(* Function to get the substate *)
fun getUnfairMediumSubState :: "UnfairMediumState \<Rightarrow> UnfairMediumSubstate" where
    "getUnfairMediumSubState (UnfairMediumState s _) = s"

(* Functions to get the variables *)
fun getCoin :: "UnfairMediumState \<Rightarrow> nat" where
"getCoin (UnfairMediumState _ var_coin) = var_coin"


end