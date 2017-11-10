(*  Title:        UnivClasses
    Author:       Sebastian, Jens, Marc

    Description:  All "Universal Classes". Later used to define bundles/pfun 
*)

theory UnivClasses
  imports "inc/LNat" "inc/OptionCpo"
begin
(* SWS: I prefer PCPO, usbLeast/usbFix are IMPORTANT! *)
default_sort pcpo


(* Mockup for the channel datatype *)
(* This channel is not a CPO... and thats good so *)
datatype channel = c1 | c2


(* The Old way *)
class message = countable +
  fixes ctype :: "channel \<Rightarrow> ('a::type) set" 
begin
end



(* The new way. 
  us = universal stream *)
(* This class is just the very basic functions required for an Bundle *)
class us = pcpo +
  fixes usOkay :: "channel \<Rightarrow> 'a \<Rightarrow> bool"
  fixes usLen :: "'a \<rightarrow> lnat"  (* Debatable *)
(*  fixes usConc :: "'a \<Rightarrow> 'a \<rightarrow> 'a"  (* Is not really required for a SB... just here for a demo *) *)

  assumes usokay_bot: "\<And>c. usOkay c \<bottom>" (* Just an example *)
(*  assumes "\<And>c. (usOkay c s1 \<Longrightarrow> usOkay c s2 \<Longrightarrow> usOkay c (conc s1\<cdot>s2))" (* Demo that we can set conditions *) *)
  assumes usokay_adm: "\<And>c. adm (usOkay c)"  (* Should be required by SB-adm proof *)
begin
end




(* The new way. 
  usb = universal stream bundle *)
(* This class is just the very basic functions required for an SPF *)
default_sort cpo

class usb = cpo +
  fixes usbDom :: "'a \<rightarrow> channel set"
  fixes usbLen :: "'a \<Rightarrow> lnat"  (* Debatable *)
  fixes usbLeast :: "channel set \<Rightarrow> 'a"

  assumes usbdom_fix: "\<And> x y. x\<sqsubseteq>y \<Longrightarrow> usbDom\<cdot>x = usbDom\<cdot>y"
  assumes usbdom_least: "\<And> x. usbLeast (usbDom\<cdot>x)\<sqsubseteq>x"
begin
end





(* First a general class for USPF/USPFw/USPFs *)
class uspf = cpo +
  fixes upfDom :: "'a \<rightarrow> channel set"
  fixes upfRan :: "'a \<rightarrow> channel set"

  assumes uspfdom_fix: "\<And>x y. x\<sqsubseteq>y \<Longrightarrow> uspfDom\<cdot>x = uspfDom\<cdot>y" 
  assumes uspfran_fix: "\<And>x y. x\<sqsubseteq>y \<Longrightarrow> uspfRan\<cdot>x = uspfRan\<cdot>y" 
begin
end

class uspf_comp = uspf +
  fixes uspfComp :: "'a \<rightarrow> 'a \<rightarrow> 'a"  (* Here we can put the abbreviation \<otimes> *)
begin
end


end