(*  Title:        USBTheorie
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "Universal Stream Bundles" 
*)

theory USB
  imports LNat OptionCpo Streams 
    (* Do NOT import Channel, the datatype/classes are duplicate *)

begin


(* ----------------------------------------------------------------------- *)
section \<open>Datatype Definition\<close>
(* ----------------------------------------------------------------------- *)

(* Mockup for the channel datatype *)
datatype channel = c1 | c2

default_sort cpo


(* The new way. 
  us = universal stream *)
(* Not sure if it should be a cpo or pcpo *)
class us = cpo +
  fixes isOkay :: "channel \<Rightarrow> 'a \<Rightarrow> bool"
  fixes len :: "'a \<rightarrow> lnat"
  fixes conc :: "'a \<Rightarrow> 'a \<rightarrow> 'a"  (* Is not really required for a SB... *)

(* assumes "\<And>c. isOkay c \<bottom>" (* Just an example, do not use this *) *)
  assumes "\<And>c. (isOkay c s1 \<Longrightarrow> isOkay c s2 \<Longrightarrow> isOkay c (conc s1\<cdot>s2))"
begin
end

(* The Old way *)
class message = countable +
  fixes ctype :: "channel \<Rightarrow> 'a set" 
begin
end

(* And so it could look like *)
instantiation stream ::  (message) us
begin
  fun isOkay_stream :: "channel \<Rightarrow> 'a stream \<Rightarrow> bool" where
  "isOkay_stream c s = (sdom\<cdot>s \<subseteq> ctype c)"

  (* And so on, other functions are missing *)
  (* there is a way not to newly define the function, but instead directly reusing the old one *)
  instance
  sorry
end 

  (* Definition: Welltyped. "a \<rightharpoonup> b" means "a => b option" *)
  (* Every Stream may only contain certain elements *)
definition sb_well :: "(channel \<rightharpoonup> ('s::us)) \<Rightarrow> bool" where
"sb_well f \<equiv> \<forall>c \<in> (dom f). (isOkay c (f\<rightharpoonup>c))" 

cpodef 's::us USB = "{b :: channel \<rightharpoonup> 's . sb_well b}"
  sorry





section \<open>Examples\<close>
(* Some examples how it would look like *)



(****************************************************)
subsection \<open>General Usage\<close>
(* Independend of the stream definition. Could be stream or tstream *)
(****************************************************)



default_sort us

(* This function can be used in "'m stream USB" and "'m tstream USB" *)
definition usbDom :: "'m USB \<rightarrow> channel set" where
"usbDom \<equiv> \<Lambda> b. dom (Rep_USB b)"

definition usbRestrict:: "channel set \<Rightarrow> 'm USB \<rightarrow> 'm USB" where
"usbRestrict cs  \<equiv> \<Lambda> b. Abs_USB (Rep_USB b |` cs)"

definition usbGetCh :: "channel \<Rightarrow> 'm USB \<rightarrow> 'm"  where
"usbGetCh c = (\<Lambda> b. ((Rep_USB b) \<rightharpoonup> c))"



(****************************************************)
subsection \<open>Specific Usage\<close>
(* DEPENDING on the stream definition. Here only for "stream" *)
(****************************************************)


default_sort message
  (* Just an example that is specific to streams *)
definition sbTake:: "nat \<Rightarrow> 'm stream USB \<rightarrow> 'm stream USB" where
"sbTake n \<equiv> (\<Lambda> b . Abs_USB (\<lambda>c. ((c\<in>usbDom\<cdot>b) \<leadsto> stake n\<cdot>(usbGetCh c\<cdot>b))))"





section \<open>SPF testing\<close>
default_sort us
definition spf_well:: "('m USB \<rightarrow> 'm USB option) \<Rightarrow> bool" where
"spf_well f \<equiv> \<exists>In Out. \<forall>b. (b \<in> dom (Rep_cfun f) \<longleftrightarrow> usbDom\<cdot>b = In) \<and> 
    (b \<in> dom (Rep_cfun f) \<longrightarrow> usbDom\<cdot>(the (f\<cdot>b)) = Out)"

  (* Define the type 'm USPF (Universal Stream Processing Functions) as cpo *)
  cpodef 'm USPF = "{f :: 'm USB \<rightarrow> 'm USB option . spf_well f}"
    sorry

(*

Alternative is ML....

bundledef 'c 's::stream SB2 = "{b :: 'c \<rightharpoonup> 's . True}"
*)




end


