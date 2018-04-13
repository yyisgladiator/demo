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


(* SWS: I prefer PCPO, usbLeast/usbFix are IMPORTANT! *)
default_sort pcpo


(* The new way. 
  us = universal stream *)
(* This class is just the very basic functions required for an Bundle *)
class us = pcpo +
  fixes isOkay :: "channel \<Rightarrow> 'a \<Rightarrow> bool"
  fixes len :: "'a \<rightarrow> lnat"  (* Debatable *)
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
"usbLen b \<equiv> if usbDom\<cdot>b \<noteq> {} then (LEAST ln. ln\<in>{(len\<cdot>(usbGetCh c\<cdot>b)) | c. c \<in> usbDom\<cdot>b}) else \<infinity>"  

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

(* The new way. 
  usb = universal stream bundle *)
(* This class is just the very basic functions required for an SPF *)
default_sort cpo

class usb = cpo +
  fixes usbDom :: "'a \<rightarrow> channel set"
  fixes usbLen :: "'a \<Rightarrow> lnat"  (* Debatable *)
  fixes usbLeast :: "channel set \<Rightarrow> 'a"

  assumes "\<And> x y. x\<sqsubseteq>y \<Longrightarrow> usbDom\<cdot>x = usbDom\<cdot>y"
  assumes "\<And> x. usbLeast (usbDom\<cdot>x)\<sqsubseteq>x"
begin
end

default_sort usb

(* SWS: This is different from the original spf_well *)
(* But hopefully identical, better ... *)
definition uspfWell:: "('in \<rightarrow> 'out option) \<Rightarrow> bool" where
"uspfWell f \<equiv> (\<exists>In. \<forall>b. (b \<in> dom (Rep_cfun f) \<longleftrightarrow> usbDom\<cdot>b = In)) \<and> 
              (\<exists>Out. \<forall>b. (b \<in> ran (Rep_cfun f) \<longrightarrow> usbDom\<cdot>b = Out))"

(* Define the type 'm USPF (Very Universal Stream Processing Functions) as cpo *)
cpodef ('in,'out) vuSPF = "{f :: 'in \<rightarrow> 'out option . uspfWell f}"
  sorry

type_synonym 'm uSPF = "('m, 'm) vuSPF"

definition uspfDom :: "('in,'out) vuSPF \<rightarrow> channel set" where
"uspfDom \<equiv> \<Lambda> f. usbDom\<cdot>(SOME b. b \<in> dom (Rep_cfun (Rep_vuSPF f)))" 

definition uspfRan :: "('in,'out) vuSPF \<rightarrow> channel set" where
"uspfRan \<equiv> \<Lambda> f. usbDom\<cdot>(SOME b. b \<in> ran (Rep_cfun (Rep_vuSPF f)))" 

definition uspfLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> ('in,'out) vuSPF" where
"uspfLeast cin cout = Abs_vuSPF (\<Lambda>  sb.  (usbDom\<cdot>sb = cin) \<leadsto> usbLeast cout)"


(* We can reuse this composition in the subtypes, for weak/strong causal stuff *)
definition uspfComp :: "'m uSPF \<rightarrow> 'm uSPF \<rightarrow> 'm uSPF" where
"uspfComp = undefined"



subsection \<open>Causal Subtype\<close>

(* return true iff tickcount holds *)
definition uspfIsWeak :: "('in,'out) vuSPF \<Rightarrow> bool" where
"uspfIsWeak f = (\<forall>b. (b \<in> dom (Rep_cfun (Rep_vuSPF f)) \<longrightarrow> usbLen b \<le> usbLen (the ((Rep_vuSPF f)\<cdot>b))))"

cpodef ('in,'out)  USPFw = "{f ::  ('in,'out) vuSPF. uspfIsWeak f}"
sorry

definition uspfIsStrong :: "('in,'out) vuSPF \<Rightarrow> bool" where
"uspfIsStrong f = (\<forall>b. (b \<in> dom (Rep_cfun (Rep_vuSPF f)) \<longrightarrow> lnsuc\<cdot>(usbLen b) \<le> usbLen (the ((Rep_vuSPF f)\<cdot>b))))"

cpodef ('in,'out) USPFs = "{f :: ('in,'out) vuSPF. uspfIsStrong f}"
sorry



section \<open>General SPS datatype\<close>

(* First a general class for USPF/USPFw/USPFs *)
class uspf = cpo +
  fixes dom :: "'a \<rightarrow> channel set"
  fixes ran :: "'a \<rightarrow> channel set"

  assumes "\<And>x y. x\<sqsubseteq>y \<Longrightarrow> dom\<cdot>x = dom\<cdot>y" 
  assumes "\<And>x y. x\<sqsubseteq>y \<Longrightarrow> ran\<cdot>x = ran\<cdot>y" 
begin
end

class uspf_comp = uspf +
  fixes comp :: "'a \<rightarrow> 'a \<rightarrow> 'a"  (* Here we can put the abbreviation \<otimes> *)
begin
end

default_sort uspf


definition uspsWell :: "'m set \<Rightarrow> bool" where
"uspsWell S \<equiv> \<exists>In Out. \<forall> f\<in>S . (dom\<cdot>f = In \<and> ran\<cdot>f=Out) "

(* Do not use this! We are changing the SPS definition in the automaton group *)
(* This is just for testing what is possible/what classes are required *)

pcpodef 'm USPS = "{S :: 'm set. uspsWell S }"
   apply (simp add: UU_eq_empty uspsWell_def)
  sorry

  (* composite operator on USPS *)
  (* 'm has to have a composition operator ... duh *)
definition uspsComp :: "'m::uspf_comp USPS \<Rightarrow>'m  USPS \<Rightarrow> 'm USPS"  where
"uspsComp S1 S2 \<equiv> Abs_USPS {comp\<cdot>f1\<cdot>f2 | f1 f2. f1\<in>(Rep_USPS S1) \<and> f2\<in>(Rep_USPS S2)}"


end