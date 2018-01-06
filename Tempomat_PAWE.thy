(*  Title:        Tempomat.thy
    Author:       Patricia Wessel
    e-mail:       patricia.wessel@rwth-aachen.de

    Description:  Specification of cruise control system
*)

chapter {* Specification of a Cruise Control System *}                                                              

theory Tempomat_PAWE

imports Streams
   
begin

(* ----------------------------------------------------------------------- *)
section {* Specification *}
(* ----------------------------------------------------------------------- *)

(* Regler: Decrease the difference of the input value to 50 by increasing or 
   decreasing its value if the input value is smaller or larger than 50, or by pass 
   it througth if it is already 50 *)
definition regler:: "nat stream \<Rightarrow> nat stream" where
"regler x \<equiv> if (shd x) < 50 then (\<up>((shd x) + 1)\<bullet>(sdrop 1\<cdot>x)) 
  else (if (shd x) = 50 then (\<up>(shd x)\<bullet>(sdrop 1\<cdot>x)) 
  else (\<up>((shd x) - 1)\<bullet>(sdrop 1\<cdot>x)))"

(* Gets the input stream and a chaos stream and adds up the values of the streams element-wise *)
definition chaos:: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" where
"chaos x c \<equiv> \<up>((shd x) + (shd c))\<bullet>(sdrop 1\<cdot>x)"
