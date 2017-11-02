(*  Title:        USBTheorie
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "Universal Stream Bundles" 
*)

theory USB
imports LNat OptionCpo Streams

begin


(* ----------------------------------------------------------------------- *)
section \<open>Datatype Definition\<close>
(* ----------------------------------------------------------------------- *)

datatype channel = c1 | c2

default_sort cpo


(* The new way. 
  us = universal stream *)
(* Not sure if it should be a cpo or pcpo *)
class us = cpo +
  fixes isOkay :: "channel \<Rightarrow> 'a \<Rightarrow> bool"
  fixes len :: "'a \<rightarrow> lnat"
  fixes conc :: "'a \<Rightarrow> 'a \<rightarrow> 'a"  (* Is not really required for a SB... *)

(* assumes "\<And>c. isOkay c \<bottom>" (* Just an example, do not use this *) *)
  assumes "\<And>c. (isOkay c s1 \<Longrightarrow> isOkay c s2 \<Longrightarrow> isOkay c (conc s1\<cdot>s2))"
begin
end

(* The Old way *)
class message = countable +
  fixes ctype :: "channel \<Rightarrow> 'a set" 
begin
end

(* And so it could look like *)
instantiation stream ::  (message) us
begin
  fun isOkay_stream :: "channel \<Rightarrow> 'a stream \<Rightarrow> bool" where
  "isOkay_stream c s = (sdom\<cdot>s \<subseteq> ctype c)"

  (* And so on, other functions are missing *)

  instance
  sorry
end 

  (* Definition: Welltyped. "a \<rightharpoonup> b" means "a => b option" *)
  (* Every Stream may only contain certain elements *)
definition sb_well :: "(channel \<rightharpoonup> ('s::us)) \<Rightarrow> bool" where
"sb_well f \<equiv> \<forall>c \<in> (dom f). (isOkay c (f\<rightharpoonup>c))" 

cpodef 's::us SB = "{b :: channel \<rightharpoonup> 's . sb_well b}"
  sorry

(*

Alternative is ML....

bundledef 'c 's::stream SB2 = "{b :: 'c \<rightharpoonup> 's . True}"
*)




end


