(*  Title:        USBTheorie
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "Universal Stream Bundles" 
*)

theory USB
  imports LNat OptionCpo Streams 
    (* Do NOT import Channel, the datatype/classes are duplicate *)
    (* The final USB.thy will not import "Streams", it is independent of the Stream *)
begin


(* ----------------------------------------------------------------------- *)
section \<open>Datatype Definition\<close>
(* ----------------------------------------------------------------------- *)

(* Mockup for the channel datatype *)
(* This channel is not a CPO... and thats good so *)
datatype channel = c1 | c2

default_sort pcpo


(* The new way. 
  us = universal stream *)
(* SWS: I prefer PCPO, usbLeast/usbFix are IMPORTANT! *)
class us = pcpo +
  fixes isOkay :: "channel \<Rightarrow> 'a \<Rightarrow> bool"
  fixes len :: "'a \<rightarrow> lnat"
  fixes conc :: "'a \<Rightarrow> 'a \<rightarrow> 'a"  (* Is not really required for a SB... just here for a demo *)

  assumes "\<And>c. isOkay c \<bottom>" (* Just an example *)
  assumes "\<And>c. (isOkay c s1 \<Longrightarrow> isOkay c s2 \<Longrightarrow> isOkay c (conc s1\<cdot>s2))" (* Demo that we can set conditions *)
  assumes "\<And>c. adm (isOkay c)"  (* Should be required by SB-adm proof *)
begin
end

(* The Old way *)
class message = countable +
  fixes ctype :: "channel \<Rightarrow> ('a::type) set" 
begin
end

(* And so it could look like *)
(* Notice that this is using message ... The user experience would not change *)
instantiation stream :: (message) us
begin
  fun isOkay_stream :: "channel \<Rightarrow> 'a stream \<Rightarrow> bool" where
  "isOkay_stream c s = (sdom\<cdot>s \<subseteq> ctype c)"

  definition "(len :: 'a stream \<rightarrow> lnat) = slen"
  definition "(conc :: 'a stream \<Rightarrow> 'a stream \<rightarrow> 'a stream) = sconc"

  instance
    apply(intro_classes)
    apply (auto)
    apply (metis (mono_tags, lifting) Un_iff conc_stream_def sconc_sdom subset_eq)
    apply(rule admI, auto)
    using l44 by blast
end 


  (* Definition: Welltyped. "a \<rightharpoonup> b" means "a => b option" *)
  (* Every Stream may only contain certain elements *)
definition usbWell :: "(channel \<rightharpoonup> ('s::us)) \<Rightarrow> bool" where
"usbWell f \<equiv> \<forall>c \<in> (dom f). (isOkay c (f\<rightharpoonup>c))" 

cpodef 's::us USB ("(_\<^sup>\<omega>)" [1000] 999) = "{b :: channel \<rightharpoonup> 's . usbWell b}"
  apply auto
   apply (meson domIff optionleast_empty usbWell_def)
  unfolding usbWell_def
  sorry

setup_lifting type_definition_USB




section \<open>Examples\<close>
(* Some examples how it would look like *)



(****************************************************)
subsection \<open>General Usage\<close>
(* Independend of the stream definition. Could be stream or tstream *)
(****************************************************)



default_sort us

(* This function can be used in "'m stream USB" and "'m tstream USB" *)
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
"usbLen b \<equiv> LEAST ln. ln\<in> {len\<cdot>(usbGetCh c\<cdot>b) | c. c\<in>usbDom\<cdot>b}"  

(* Thats an easy converter. For example from "tstream USB" to "stream USB" *)
(* Can also be cont *)
definition usbShift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a USB \<Rightarrow> 'b USB" where
"usbShift f sb = Abs_USB (\<lambda>c. ((c\<in>usbDom\<cdot>sb) \<leadsto> f (usbGetCh c\<cdot>sb)))"



(****************************************************)
subsection \<open>Specific Usage\<close>
(* DEPENDING on the stream definition. Here only for "stream" *)
(****************************************************)


default_sort message
  (* Just an example that is specific to streams *)
definition sbTake:: "nat \<Rightarrow> 'm stream USB \<rightarrow> 'm stream USB" where
"sbTake n \<equiv> (\<Lambda> b . Abs_USB (\<lambda>c. ((c\<in>usbDom\<cdot>b) \<leadsto> stake n\<cdot>(usbGetCh c\<cdot>b))))"



(****************************************************)
subsection \<open>Concrete Example\<close>
(****************************************************)
datatype M = MNat nat | MBool bool

instantiation M :: message
begin
  fun ctype_M :: "channel \<Rightarrow> M set" where
  "ctype_M c1 = range MNat"  |
  "ctype_M c2 = range MBool"

  instance 
  apply(intro_classes)
  by(countable_datatype)
end

lift_definition stB1 :: "M stream USB" is "([c1\<mapsto><[MNat 1,MNat 2,MNat 3]>, c2\<mapsto><[MBool True,MBool False]>])"
  by(auto simp add: usbWell_def)



(****************************************************)
section \<open>SPF testing\<close>
(****************************************************)


default_sort us

definition uspfWell:: "('m USB \<rightarrow> 'm USB option) \<Rightarrow> bool" where
"uspfWell f \<equiv> \<exists>In Out. \<forall>b. (b \<in> dom (Rep_cfun f) \<longleftrightarrow> usbDom\<cdot>b = In) \<and> 
    (b \<in> dom (Rep_cfun f) \<longrightarrow> usbDom\<cdot>(the (f\<cdot>b)) = Out)"

(* Define the type 'm USPF (Universal Stream Processing Functions) as cpo *)
cpodef 'm USPF = "{f :: 'm USB \<rightarrow> 'm USB option . uspfWell f}"
  sorry



subsection \<open>Strong Causal Subtype\<close>

(* return true iff tickcount holds *)
definition uspfTickCount :: "'m USPF \<Rightarrow> bool" where
"uspfTickCount f = (\<forall>b. (b \<in> dom (Rep_cfun (Rep_USPF f)) \<longrightarrow> usbLen b \<le> usbLen (the ((Rep_USPF f)\<cdot>b))))"

cpodef 'm USPF_strong = "{f :: 'm USPF. uspfTickCount f}"
sorry

(*

Alternative is something with ML....

bundledef 'c 's::stream SB2 = "{b :: 'c \<rightharpoonup> 's . True}"
*)




end