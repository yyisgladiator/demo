(*
 * DO NOT MODIFY!
 * This file was generated from Password.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 15, 2018 8:59:07 PM by isartransformer 2.0.0
 *)
theory PasswordStates
  imports PasswordDatatype

begin


(* These are the actual states from MAA *)
datatype PasswordSubstate = Initial | PasswortSaved | OneTick

(* And these have also the variables *)
datatype PasswordState = PasswordState PasswordSubstate (* lastB = *) "string"

(* Function to get the substate *)
fun getPasswordSubState :: "PasswordState \<Rightarrow> PasswordSubstate" where
    "getPasswordSubState (PasswordState s _) = s"

(* Functions to get the variables *)
fun getLastB :: "PasswordState \<Rightarrow> string" where
"getLastB (PasswordState _ var_lastB) = var_lastB"


end