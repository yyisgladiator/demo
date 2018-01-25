(* Draft for Non-Deterministic Automaton *)

theory NDA

imports Automaton

begin



section \<open>Non Deterministic Case \<close>

(* FYI: Non-deterministic version *)
typedef ('state::type, 'm::message) NDA = 
  "{f::(('state \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> (('state \<times> 'm SB) set)) \<times> ('state \<times> 'm SB) set \<times> channel set \<times> channel set. True}"
  by blast

(* relation based on transition function and initial set *)
instantiation NDA :: (type, message) po
begin
  fun below_NDA :: "('a, 'b) NDA \<Rightarrow> ('a, 'b) NDA \<Rightarrow> bool" where
  "below_NDA n1 n2 = ((fst (Rep_NDA n1) \<sqsubseteq>  fst (Rep_NDA n2))  (* Transition function is subset *)
                  \<and>   (fst (snd (Rep_NDA n1)) \<sqsubseteq>  fst (snd (Rep_NDA n2)))  (* Initial states subset *)
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


definition ndaTransition :: "('s, 'm::message) NDA \<rightarrow> (('s \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> (('s \<times> 'm SB) set))" where
"ndaTransition \<equiv> \<Lambda> nda. fst (Rep_NDA nda)"

definition ndaInitialState :: "('s, 'm::message) NDA \<rightarrow> ('s \<times> 'm SB) set" where
"ndaInitialState = undefined"

definition ndaDom :: "('s, 'm::message) NDA \<rightarrow> channel set" where
"ndaDom = undefined" (* todo *)

definition ndaRan :: "('s, 'm::message) NDA \<rightarrow> channel set" where
"ndaRan = undefined" (* todo *)



definition spsFix :: "('a \<rightarrow> 'a) \<rightarrow> 'a" where
"spsFix = undefined"  (* Die ganze function ist natürlich grober unsinn *)

(* like spfStep, only on SPS *)
definition spsStep :: "channel set \<Rightarrow> channel set \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS) \<rightarrow> 'm SPS" where
"spsStep cin cout \<equiv> undefined"


(* ToDo *)
definition spsHelper:: "'s \<Rightarrow> (('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) set) \<rightarrow> ('s \<Rightarrow> 'm SPS) \<rightarrow> ('e \<Rightarrow> 'm SPS)" where
"spsHelper s \<equiv> undefined (* \<Lambda> h. (\<lambda> e. (h (fst (f (s,e))))) *)"

(* Similar to Rum96 *)
definition nda_h :: "('s::type, 'm::message) NDA \<rightarrow> ('s \<Rightarrow> 'm SPS)" where
"nda_h \<equiv>  \<Lambda> nda. spsFix\<cdot>(\<Lambda> h. (\<lambda>s. spsStep (ndaDom\<cdot>nda)(ndaRan\<cdot>nda)\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h)))"

lemma "cont (\<lambda> nda. spsFix\<cdot>(\<Lambda> h. (\<lambda>s. spsStep (ndaDom\<cdot>nda)(ndaRan\<cdot>nda)\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h))))"
  oops

(* This function also prepends the first SB ... *)
(* But basically she just calls h *)
definition nda_H :: "('s, 'm::message) NDA \<rightarrow> 'm SPF set" where
"nda_H \<equiv> \<Lambda> nda. undefined"



end