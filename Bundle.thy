(*  Title:        UnivClasses
    Author:       Sebastian, Jens, Marc

    Description:  All "Universal Classes". Later used to define bundles/pfun 
*)

theory Bundle
  imports UnivClasses
begin

  (* Definition: Welltyped. "a \<rightharpoonup> b" means "a => b option" *)
  (* Every Stream may only contain certain elements *)
definition usbWell :: "(channel \<rightharpoonup> ('s::us)) \<Rightarrow> bool" where
"usbWell f \<equiv> \<forall>c \<in> (dom f). (usOkay c (f\<rightharpoonup>c))" 

cpodef 's::us USB ("(_\<^sup>\<omega>)" [1000] 999) = "{b :: channel \<rightharpoonup> 's . usbWell b}"
  apply auto
   apply (meson domIff optionleast_empty usbWell_def)
  unfolding usbWell_def
  sorry (* We are putting the right assumptions in the us class, so that this holds *)

setup_lifting type_definition_USB


(****************************************************)
subsection \<open>General Usage\<close>
(* Independend of the stream definition. Could be stream or tstream *)
(****************************************************)



default_sort us

(* This function can be used in "'m stream USB" and "'m tstream USB" *)
(* and by the way, look at the "'m\<^sup>\<omega>" shorcode for 'm USB *)
definition usbDom :: "'m\<^sup>\<omega> \<rightarrow> channel set" where
"usbDom \<equiv> \<Lambda> b. dom (Rep_USB b)"

definition usbRestrict:: "channel set \<Rightarrow> 'm USB \<rightarrow> 'm USB" where
"usbRestrict cs  \<equiv> \<Lambda> b. Abs_USB (Rep_USB b |` cs)"

definition usbGetCh :: "channel \<Rightarrow> 'm USB \<rightarrow> 'm"  where
"usbGetCh c = (\<Lambda> b. ((Rep_USB b) \<rightharpoonup> c))"

definition usbLeast :: "channel set \<Rightarrow> 'm USB"  where
"usbLeast cs \<equiv> Abs_USB (\<lambda>c. (c \<in> cs) \<leadsto> \<bottom> )"

(* Interesting function, uses the "len" operator over 'm *)
definition usbLen:: " 'm USB \<Rightarrow> lnat " where
"usbLen b \<equiv> if usbDom\<cdot>b \<noteq> {} then (LEAST ln. ln\<in>{(usLen\<cdot>(usbGetCh c\<cdot>b)) | c. c \<in> usbDom\<cdot>b}) else \<infinity>"  

(* Thats an easy converter. For example from "tstream USB" to "stream USB" *)
(* Can also be cont *)
definition usbShift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a USB \<Rightarrow> 'b USB" where
"usbShift f sb = Abs_USB (\<lambda>c. ((c\<in>usbDom\<cdot>sb) \<leadsto> f (usbGetCh c\<cdot>sb)))"




end