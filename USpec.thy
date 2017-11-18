(*  Title:        USpec
    Author:       Stüber, Jens, Marc
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "universal spezification" 
*)

theory USpec
  imports UnivClasses
begin

default_sort ufuncl

(****************************************************)
section\<open>Data type\<close>
(****************************************************) 
  
definition uspecWell :: "'m set \<Rightarrow> bool" where
"uspecWell S \<equiv> \<exists>In Out. \<forall> f\<in>S . (ufDom\<cdot>f = In \<and> ufRan\<cdot>f=Out) "
(* define a Set of 'm SPF's. all SPS in a set must have the same In/Out channels *)

cpodef 'm uspec = "{S :: 'm set. uspecWell S }"
  sorry

setup_lifting type_definition_uspec


(* 
  (* composite operator on SPS *)
  definition spsComp :: "'m SPS \<Rightarrow>'m  SPS \<Rightarrow> 'm SPS" (infixl "\<Otimes>" 50) where
"spsComp S1 S2 \<equiv> Abs_SPS {f1 \<otimes> f2 | f1 f2. f1\<in>(Rep_SPS S1) \<and> f2\<in>(Rep_SPS S2)}"
*)

definition uspecDom :: "'m uspec \<Rightarrow> channel set" where
"uspecDom S = ufDom\<cdot>(SOME f. f\<in> Rep_uspec S)"

definition uspecRan :: "'m uspec \<Rightarrow> channel set" where
"uspecRan S = ufRan\<cdot>(SOME f. f\<in> Rep_uspec S)"
