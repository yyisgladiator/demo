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

(* abbreviations should be defined in the classes or ufun.thy *)
subsection\<open>abbreviations\<close>

  
abbreviation theRep_abbrv :: "('a \<Rrightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b " (infix "\<rightleftharpoons>" 62) where
"(f \<rightleftharpoons> s) \<equiv> (Rep_cfun (Rep_ufun(f)))\<rightharpoonup>s"  

abbreviation ubclUnion_abbr :: " 'm \<Rightarrow> 'm \<Rightarrow> 'm" (infixl "\<uplus>" 100) where 
"b1 \<uplus> b2 \<equiv> ubUnion\<cdot>b1\<cdot>b2"

abbreviation ubclRestrict_abbr :: " 'm \<Rightarrow> channel set \<Rightarrow> 'm" ("(_\<bar>_)" [66,65] 65)
where "b\<bar>cs \<equiv> ubRestrict cs\<cdot>b"

  
subsection\<open>definitions\<close>  

  
(* ufLeast *)
definition ufLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> ('in \<Rrightarrow> 'out)" where
"ufLeast cin cout = Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = cin) \<leadsto> ubLeast cout)"  
  
  
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
"ubFix F cs = (\<Squnion>i. iterate i\<cdot>F\<cdot>(ubLeast cs))"


subsection \<open>composition helpers\<close>

 
definition ufCompH :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> 'm \<Rightarrow> ('m \<rightarrow> 'm)" where
"ufCompH f1 f2 x = (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z) \<bar> ufDom\<cdot>f2)))"


subsection \<open>composition operators\<close>

(* general *) 
definition ufComp :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm)" where
"ufComp f1 f2 \<equiv>
let I = ufCompI f1 f2;
    Oc = (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)
in Abs_ufun (Abs_cfun (\<lambda> x. (ubDom\<cdot>x = I) \<leadsto> ubFix (ufCompH f1 f2 x) Oc))" 

(* parcomp *)
definition ufParComp :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm)" ("_\<parallel>_") where
"ufParComp f1 f2 \<equiv> Abs_ufun (Abs_cfun (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1 \<union> ufDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>ufDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>ufDom\<cdot>f2)))))"

(* sercomp *)
definition ufSerComp :: "('m \<Rrightarrow> 'm) => ('m \<Rrightarrow> 'm) => ('m \<Rrightarrow> 'm)"  ("_\<circ>_") where
"ufSerComp f1 f2 \<equiv> Abs_ufun (Abs_cfun (\<lambda> x. (ubDom\<cdot>x =  ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))"

(* feedback *)
definition ufFeedH:: "('m \<Rrightarrow> 'm) \<Rightarrow> 'm \<Rightarrow> 'm  \<rightarrow> 'm" where
"ufFeedH f x \<equiv> (\<Lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (ufDom\<cdot>f))))"

definition ufFeedbackComp :: "('m \<Rrightarrow> 'm) \<Rightarrow> ('m \<Rrightarrow> 'm)" ("\<mu>_" 50) where
"ufFeedbackComp f \<equiv>
let I  = ufDom\<cdot>f - ufRan\<cdot>f;
    I1 = ufDom\<cdot>f;
    C  = ufRan\<cdot>f
in Abs_ufun (Abs_cfun (\<lambda> sb. (ubDom\<cdot>sb = I) \<leadsto>
    (ubFix (ufFeedH f sb) C)))"  

  
(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)  

(* ufLeast *)
  
(* general *)  
  
(* parcomp *)

(* sercomp *)

(* feedback *)  
  
  
end