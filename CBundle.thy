(*  Title:        UnivClasses
    Author:       Sebastian, Jens, Marc

    Description:  All "Universal Classes". Later used to define bundles/pfun 
*)

theory CBundle
  imports UnivClasses
begin

  (* Definition: Welltyped. "a \<rightharpoonup> b" means "a => b option" *)
  (* Every Stream may only contain certain elements *)
definition cbWell :: "(channel \<rightharpoonup> ('s::us)) \<Rightarrow> bool" where
"cbWell f \<equiv> \<forall>c \<in> (dom f). (usOkay c (f\<rightharpoonup>c))" 

cpodef 's::us cbundle ("(_\<^sup>\<omega>)" [1000] 999) = "{b :: channel \<rightharpoonup> 's . cbWell b}"
  apply auto
   apply (meson domIff optionleast_empty cbWell_def)
  unfolding cbWell_def
  sorry (* We are putting the right assumptions in the us class, so that this holds *)

setup_lifting type_definition_cbundle


(****************************************************)
subsection \<open>General Usage\<close>
(* Independend of the stream definition. Could be stream or tstream *)
(****************************************************)



default_sort us

(* This function can be used in "'m stream USB" and "'m tstream USB" *)
(* and by the way, look at the "'m\<^sup>\<omega>" shorcode for 'm USB *)
definition cbDom :: "'m\<^sup>\<omega> \<rightarrow> channel set" where
"cbDom \<equiv> \<Lambda> b. dom (Rep_cbundle b)"

definition cbRestrict:: "channel set \<Rightarrow> 'm cbundle \<rightarrow> 'm cbundle" where
"cbRestrict cs  \<equiv> \<Lambda> b. Abs_cbundle (Rep_cbundle b |` cs)"

definition cbGetCh :: "channel \<Rightarrow> 'm cbundle \<rightarrow> 'm"  where
"cbGetCh c = (\<Lambda> b. ((Rep_cbundle b) \<rightharpoonup> c))"

definition cbLeast :: "channel set \<Rightarrow> 'm cbundle"  where
"cbLeast cs \<equiv> Abs_cbundle (\<lambda>c. (c \<in> cs) \<leadsto> \<bottom> )"

(* Interesting function, uses the "len" operator over 'm *)
definition cbLen:: " 'm cbundle \<Rightarrow> lnat " where
"cbLen b \<equiv> if cbDom\<cdot>b \<noteq> {} then (LEAST ln. ln\<in>{(usLen\<cdot>(cbGetCh c\<cdot>b)) | c. c \<in> cbDom\<cdot>b}) else \<infinity>"  

(* Thats an easy converter. For example from "tstream USB" to "stream USB" *)
(* Can also be cont *)
definition cbShift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a cbundle \<Rightarrow> 'b cbundle" where
"cbShift f sb = Abs_cbundle (\<lambda>c. ((c\<in>cbDom\<cdot>sb) \<leadsto> f (cbGetCh c\<cdot>sb)))"




end