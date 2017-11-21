(*  Title:        UFun_Comp
    Author:       Stüber, Jens, Marc
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines Composition of "Processing functions" 
*)

theory UFun_Comp
  imports UFun
begin

default_sort ubcl_comp  
  
(****************************************************)
section\<open>Definitions\<close>
(****************************************************)    

subsection\<open>channel sets\<close>

  
text {* the input channels of the composition of f1 and f2 *}
definition ufCompI :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> channel set" where
"ufCompI f1 f2 \<equiv> (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) - (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"

text {* the internal channels of the composition of f1 and f2 *}
definition ufCompL :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> channel set" where
"ufCompL f1 f2 \<equiv> (ufDom\<cdot>f1 \<union> ufDom\<cdot>f2) \<inter> (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"

text {* the output channels of the composition of f1 and f2 *}
definition ufCompO :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> channel set" where
"ufCompO f1 f2 \<equiv> (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)"

text {* all channels of the composition of f1 and f2  *}
definition ufCompC :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> channel set" where
"ufCompC f1 f2 \<equiv> ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 \<union> ufRan\<cdot>f1 \<union> ufRan\<cdot>f2"


subsection \<open>ubFix\<close>
  
  
definition ubFix :: "('m \<rightarrow> 'm) \<Rightarrow> channel set \<Rightarrow> 'm" where 
"ubFix = undefined"


subsection \<open>composition helpers\<close>

 
definition ufCompH :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> 'm \<Rightarrow> ('m \<rightarrow> 'm)" where
"ufCompH f1 f2 x = undefined"
(*
"ufCompH f1 f2 x \<equiv> (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f2)))"
*)

subsection \<open>composition operators\<close>

  
definition ufComp :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm)" where
"ufComp f1 f2 \<equiv>
let I = ufCompI f1 f2;
    Oc = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)
in Abs_ufun(Abs_cfun (\<lambda> x. (ubDom\<cdot>x = I) \<leadsto> ubFix (ufCompH f1 f2 x) Oc))" 

(* parcomp *)

(* sercomp *)

(* feedback *)

  
(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)  

end