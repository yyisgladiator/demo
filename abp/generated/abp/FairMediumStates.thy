(*
 * DO NOT MODIFY!
 * This file was generated from FairMedium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 16, 2018 10:17:27 PM by isartransformer 3.1.0
 *)
theory FairMediumStates
  imports MediumDatatype

begin


(* These are the actual states from MAA *)
datatype FairMediumSubstate = Single

(* And these have also the variables *)
datatype FairMediumState = FairMediumState FairMediumSubstate (* counter = *) "int"

(* Function to get the substate *)
fun getFairMediumSubState :: "FairMediumState \<Rightarrow> FairMediumSubstate" where
    "getFairMediumSubState (FairMediumState s _) = s"

(* Functions to get the variables *)
fun getCounter :: "FairMediumState \<Rightarrow> int" where
"getCounter (FairMediumState _ var_counter) = var_counter"


end