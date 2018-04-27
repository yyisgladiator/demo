(* Draft for Non-Deterministic Automaton *)

theory NDA

imports Automaton "../../USpec"

begin

default_sort type
type_synonym 'm SPS = "'m SPF uspec"



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



definition setflat :: "'a set set \<rightarrow> 'a set" where
"setflat = (\<Lambda> S. {K  | Z K. K\<in>Z \<and> Z \<in>S} )"

lemma setflat_mono: "monofun (\<lambda> S. {K  | Z K. K\<in>Z \<and> Z \<in>S} )"
  apply(rule monofunI)
  apply auto
  by (smt SetPcpo.less_set_def mem_Collect_eq subsetCE subsetI)

lemma setflat_cont: "cont (\<lambda> S. {K  | Z K. K\<in>Z \<and> Z \<in>S} )"
  apply(rule contI2)
  using setflat_mono apply simp
  apply auto
  unfolding  SetPcpo.less_set_def
  unfolding lub_eq_Union
  by blast

lemma setflat_insert: "setflat\<cdot>S = {K  | Z K. K\<in>Z \<and> Z \<in>S}"
  unfolding setflat_def
  by (metis (mono_tags, lifting) Abs_cfun_inverse2 setflat_cont)

(* Test it *)
lemma "setflat\<cdot>{{1,2::nat},{3,4::nat}} = {1,2,3,4}"
  unfolding setflat_insert
  apply blast (* Dauert ein bisschen, lösche das lemma wenn es nervt *)
  done



(* like spfStep, copy & pasteonly on SPS *)
fun spsStep :: "channel set discr \<Rightarrow> channel set discr \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS) \<rightarrow> 'm SPS" where
"spsStep (Discr cin) (Discr cout) = undefined"




(* See: https://git.rwth-aachen.de/montibelle/automaton/core/issues/70 *)
definition spsConc:: "'m SB \<Rightarrow> 'm SPS \<rightarrow> 'm SPS" where
"spsConc = undefined"

(* See: https://git.rwth-aachen.de/montibelle/automaton/core/issues/70 *)
definition spsRt:: "'m SPS \<rightarrow> 'm SPS" where
"spsRt = undefined"

definition setmap::"('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<rightarrow> 'b set"where
"setmap f \<equiv> \<Lambda> u. {f x | x. x \<in> u}"

definition setflat_sps::"'m::message SPS set \<rightarrow> 'm SPS" where
"setflat_sps = (\<Lambda> spss. Abs_rev_uspec (setflat\<cdot>(setmap Rep_rev_uspec\<cdot>spss)))"
                                                                              (*One of setflat_sps should be cont*)
definition setflat_sps_rev:: "'m::message SPS set rev \<rightarrow> 'm SPS" where
"setflat_sps_rev = (\<Lambda> spss. Abs_rev_uspec (setflat\<cdot>(setmap Rep_rev_uspec\<cdot>(inv Rev spss))))"
                                                             
definition spsConc_set::"('m::message SB) set rev \<Rightarrow> 'm SPS \<rightarrow> 'm SPS"where (*or with 'm SB set input and with out inv Rev in function*)
"spsConc_set s = (\<Lambda> sps. setflat_sps\<cdot>{spsConc sb\<cdot>sps | sb. sb \<in> (inv Rev s)})"

definition spsRt_set:: "'m::message SPS set rev \<rightarrow> 'm SPS" where
"spsRt_set = (\<Lambda> spss. Abs_rev_uspec (setflat\<cdot>(setmap Rep_rev_uspec\<cdot>(inv Rev spss))))"

definition set_snd::"(('s \<times> 'm::message SB) set rev) \<rightarrow> (('m::message SB) set rev)" where
"set_snd \<equiv> \<Lambda> x. Rev (setmap snd\<cdot>(inv Rev x))"

definition set_fst::"(('s \<times> 'm::message SB) set rev) \<rightarrow> ('s set rev)" where
"set_fst \<equiv> \<Lambda> x. Rev (setmap fst\<cdot>(inv Rev x))"

(* ToDo *)
(* Very Very similar to helper over automaton *)
thm helper_def

(* Es klappt aber nicht.... Der nichtdeterminismus wird nicht berücksichtigt! 
  und ich laufe immer wieder in das problem: https://git.rwth-aachen.de/montibelle/automaton/core/issues/68 *)

definition spsHelper:: "'s \<Rightarrow> (('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) set rev) \<rightarrow> ('s set rev \<Rightarrow> 'm SPS) \<rightarrow> ('e \<Rightarrow> 'm SPS)" where
"spsHelper s \<equiv> \<Lambda> f. \<Lambda> h. (\<lambda> e. spsRt\<cdot>(spsConc_set (set_snd\<cdot> (f (s,e)))\<cdot>(h (set_fst\<cdot>(f (s,e))))))"



(* Similar to Rum96 *)
definition nda_h :: "('s::type, 'm::message) NDA \<rightarrow> ('s \<Rightarrow> 'm SPS)" where
"nda_h \<equiv>  \<Lambda> nda. spsFix\<cdot>(\<Lambda> h. (\<lambda>s. spsStep (ndaDom\<cdot>nda)(ndaRan\<cdot>nda)\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h)))"





definition setrevImage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set rev \<rightarrow> 'b set rev" where
"setrevImage = undefined"

(* See: https://git.rwth-aachen.de/montibelle/automaton/core/issues/57 *)
definition uspecImage:: "('m \<Rightarrow> 'n) \<Rightarrow> 'm uspec \<rightarrow> 'n uspec" where
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
"nda_H \<equiv> \<Lambda> nda. undefined" (* Abs_uspec (setrevImage helper\<cdot>(ndaInitialState\<cdot>nda))" *)





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



lemma "cont (\<lambda> nda. spsFix\<cdot>(\<Lambda> h. (\<lambda>s. spsStep some suff\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h))))"
  by simp

lemma "cont (\<lambda> h. (\<lambda>s. spsStep (ndaDom\<cdot>nda)(ndaRan\<cdot>nda)\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h)))"
  by simp


end