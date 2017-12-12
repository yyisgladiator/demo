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

cpodef 'm uspec = "{S :: 'm set rev. uspecWell (inv Rev S) }"
  apply(auto simp add: uspecWell_def)
  sorry

setup_lifting type_definition_uspec


(****************************************************)
section\<open>Definitions\<close>
(****************************************************) 
  
  
definition uspecDom :: "'m uspec \<Rightarrow> channel set" where
"uspecDom S = ufDom\<cdot>(SOME f. f\<in>  ((inv Rev) (Rep_uspec S)))"

definition uspecRan :: "'m uspec \<Rightarrow> channel set" where
"uspecRan S = ufRan\<cdot>(SOME f. f\<in> ((inv Rev) (Rep_uspec S)))"


(****************************************************)
section\<open>Lemmas\<close>
(****************************************************) 

 
  
  
(****************************************************)
section\<open>Composition\<close>
(****************************************************)   
  

(* from here on only lemma on composition *)
default_sort ufuncl_comp
  (* composite operator on SPS *)
(* THIS IS JUST A DEMO! there should be many changes *)
definition uspecComp :: "'m uspec \<Rightarrow>'m uspec \<Rightarrow> 'm uspec" (infixl "\<Otimes>" 50) where
"uspecComp S1 S2 \<equiv> Abs_uspec (Rev {ufunclComp\<cdot>f1\<cdot>f2 | f1 f2. f1\<in>((inv Rev) (Rep_uspec S1)) \<and> f2\<in>((inv Rev) (Rep_uspec S2))})"


end