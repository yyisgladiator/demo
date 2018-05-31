(* Draft for Non-Deterministic Automaton *)

theory NDA

imports Automaton "../../USpec" "../SpsStep" NDA_functions

begin

default_sort type
  
section \<open>Non Deterministic Case \<close>

(* FYI: Non-deterministic version *)
cpodef ('state::type, 'm::message) NDA = 
  "{f::(('state \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> (('state \<times> 'm SB) set rev)) \<times> ('state \<times> 'm SB) set rev \<times> channel set discr \<times> channel set discr. True}"
  by auto

setup_lifting type_definition_NDA

(*
(* relation based on transition function and initial set *)
instantiation NDA :: (type, message) po
begin
  fun below_NDA :: "('a, 'b) NDA \<Rightarrow> ('a, 'b) NDA \<Rightarrow> bool" where
  "below_NDA n1 n2 = ((fst (Rep_NDA n2) \<sqsubseteq>  fst (Rep_NDA n1))  (* Transition function is subset. NOTICE: Reversed *)
                  \<and>   (fst (snd (Rep_NDA n2)) \<sqsubseteq>  fst (snd (Rep_NDA n1)))  (* Initial states subset. NOTICE: Reversed *)
                  \<and>   (fst (snd (snd (Rep_NDA n1))) =  fst (snd (snd (Rep_NDA n2))))  (* input domain identical *)
                  \<and>   (     (snd (snd (snd (Rep_NDA n1)))) =  (snd (snd (snd (Rep_NDA n2))))) )" (* output domain identical *)

instance
  apply(intro_classes)
    apply simp
  apply simp
  apply (meson below_trans)
  by (meson Rep_NDA_inject below_NDA.elims(2) below_antisym prod.expand)
end  

instance NDA :: (type, message) cpo 
  apply(intro_classes)
  apply (rule, rule is_lubI)
  sorry

*)


definition ndaTransition :: "('s, 'm::message) NDA \<rightarrow> (('s \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> (('s \<times> 'm SB) set rev))" where
"ndaTransition \<equiv> \<Lambda> nda. fst (Rep_NDA nda)"

definition ndaInitialState :: "('s, 'm::message) NDA \<rightarrow> ('s \<times> 'm SB) set rev" where
"ndaInitialState = (\<Lambda> nda. fst (snd (Rep_NDA nda)))"

definition ndaDom :: "('s, 'm::message) NDA \<rightarrow> channel set discr" where
"ndaDom = (\<Lambda> nda. fst (snd (snd (Rep_NDA nda))))"

definition ndaRan :: "('s, 'm::message) NDA \<rightarrow> channel set discr" where
"ndaRan =  (\<Lambda> nda. snd (snd (snd (Rep_NDA nda))))" 


(* See: https://git.rwth-aachen.de/montibelle/automaton/core/issues/59 *)
definition spsFix :: "('a \<rightarrow> 'a) \<rightarrow> 'a" where
"spsFix = undefined"  (* Die ganze function ist natürlich grober unsinn *)





(* Test it *)
lemma "setflat\<cdot>{{1,2::nat},{3,4::nat}} = {1,2,3,4}"
  unfolding setflat_insert
  apply blast (* Dauert ein bisschen, lösche das lemma wenn es nervt *)
  done
(*
"channel set \<Rightarrow> channel set \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF) \<rightarrow> 'm SPF"
*)

  
(* See: https://git.rwth-aachen.de/montibelle/automaton/core/issues/70 *)
definition spsConc:: "'m SB \<Rightarrow> 'm SPS \<rightarrow> 'm SPS" where
"spsConc = undefined"

(* See: https://git.rwth-aachen.de/montibelle/automaton/core/issues/70 *)
definition spsRt:: "'m SPS \<rightarrow> 'm SPS" where
"spsRt = undefined"


(* ToDo *)
(* Very Very similar to helper over automaton *)
thm helper_def

(* Es klappt aber nicht.... Der nichtdeterminismus wird nicht berücksichtigt! 
  und ich laufe immer wieder in das problem: https://git.rwth-aachen.de/montibelle/automaton/core/issues/68 *)

definition spsHelper:: "'s \<Rightarrow> (('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) set rev) \<rightarrow> ('s \<Rightarrow> 'm SPS) \<rightarrow> ('e \<Rightarrow> 'm SPS)" where(*Other Idea*)
"spsHelper s \<equiv> undefined"     
    
(* Similar to Rum96 *)
definition nda_h :: "('s::type, 'm::message) NDA \<rightarrow> ('s \<Rightarrow> 'm SPS)" where
"nda_h \<equiv>  \<Lambda> nda. spsFix\<cdot>(\<Lambda> h. (\<lambda>s. spsStep (undiscr(ndaDom\<cdot>nda))(undiscr(ndaRan\<cdot>nda))\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h)))"
    
definition setrevImage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set rev \<rightarrow> 'b set rev" where
"setrevImage = undefined"

(* See: https://git.rwth-aachen.de/montibelle/automaton/core/issues/57 *)
definition uspecImage:: "('m::ufuncl \<Rightarrow> 'n::ufuncl) \<Rightarrow> 'm uspec \<rightarrow> 'n uspec" where
"uspecImage = undefined"

  
(* see: https://git.rwth-aachen.de/montibelle/automaton/core/issues/58 *)
definition uspecUnion:: "'m uspec \<rightarrow> 'm uspec \<rightarrow> 'm uspec" where
"uspecUnion = undefined"


(* Takes an tupel of the initial-state/output message... and returns the corresponding SPS *)
fun helper:: "('s \<times> 'm::message SB) \<Rightarrow> ('s::type, 'm::message) NDA \<rightarrow> 'm SPS" where
"helper (state, output) = (\<Lambda> nda. uspecImage (Rep_cfun (spfConc output))\<cdot>((nda_h\<cdot>nda) state))"


definition nda_H_helper :: "('s, 'm::message) NDA \<rightarrow> 'm SPS set rev" where
"nda_H_helper \<equiv> \<Lambda> nda. (setrevImage (\<lambda>t. helper t\<cdot>nda)\<cdot>(ndaInitialState\<cdot>nda))"

(* https://git.rwth-aachen.de/montibelle/automaton/core/issues/68 *)
definition nda_H :: "('s, 'm::message) NDA \<rightarrow> 'm SPS" where
"nda_H \<equiv> \<Lambda> nda. undefined\<cdot>(nda_H_helper\<cdot>nda)" 





lemma nda_rep_cont[simp]: "cont Rep_NDA"
proof -
  obtain nn :: "(('a, 'b) NDA \<Rightarrow> ('a \<times> (channel \<Rightarrow> 'b option) \<Rightarrow> ('a \<times> 'b stream\<^sup>\<Omega>) set rev) \<times> ('a \<times> 'b stream\<^sup>\<Omega>) set rev \<times> channel set discr \<times> channel set discr) \<Rightarrow> nat \<Rightarrow> ('a, 'b) NDA" where
    f1: "\<forall>f. chain (nn f) \<and> \<not> range (\<lambda>n. f (nn f n)) <<| f (Lub (nn f)) \<or> cont f"
using contI by moura
  have "Rep_NDA (Abs_NDA (\<Squnion>n. Rep_NDA (nn Rep_NDA n))) = (\<Squnion>n. Rep_NDA (nn Rep_NDA n))"
    using Abs_NDA_inverse by blast
then show ?thesis
  using f1 by (metis (no_types) below_NDA_def lub_NDA po_class.chain_def thelubE)
qed


lemma "cont (\<lambda>nda. fst (Rep_NDA nda))"
  by simp


(*
lemma "cont (\<lambda> nda. spsFix\<cdot>(\<Lambda> h. (\<lambda>s. spsStep some suff\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h))))"
  by simp

lemma "cont (\<lambda> h. (\<lambda>s. spsStep (ndaDom\<cdot>nda)(ndaRan\<cdot>nda)\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h)))"
  by simp
*)

end