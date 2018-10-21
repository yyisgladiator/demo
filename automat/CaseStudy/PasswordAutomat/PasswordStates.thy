(*
 * DO NOT MODIFY!
 * This file was generated from Password.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 18, 2018 7:47:14 PM by isartransformer 3.1.0
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