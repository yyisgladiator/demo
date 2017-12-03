(*  Title:        UnivClasses
    Author:       Sebastian, Jens, Marc

    Description:  All "Universal Classes". Later used to define bundles/pfun 
*)

theory UnivClasses
  imports "inc/LNat" "inc/OptionCpo" Channel
begin
  

default_sort pcpo

  
(****************************************************)
section\<open>Message\<close>
(****************************************************) 

class message = countable +
  fixes ctype :: "channel \<Rightarrow> ('a::type) set" 
begin
end


(****************************************************)
section\<open>Universal Stream\<close>
(****************************************************) 


(* This class is just the very basic functions required for an Bundle *)
class uscl = cpo +
  fixes usOkay :: "channel \<Rightarrow> 'a \<Rightarrow> bool" (* similar to "ctype" in message *)
  fixes usLen :: "'a \<rightarrow> lnat"

  (*assumes usOkay_bot: "\<And>c. usOkay c \<bottom>"    (* used for ubLeast wellformed proof *)*)
  assumes usOkay_adm: "\<And>c. adm (usOkay c)" (* used to instanciate ubundle *)
begin
end
  
class uscl_pcpo = uscl + pcpo + 
  assumes usOkay_bot: "\<And>c. usOkay c \<bottom>"    (* used for ubLeast wellformed proof *)
begin
end  


(****************************************************)
section\<open>Universal Stream Bundle\<close>
(****************************************************) 
  

(* This class is just the very basic functions required for an SPF *)
default_sort cpo

class ubcl = cpo +
  fixes ubDom :: "'a \<rightarrow> channel set"
  fixes ubLen :: "'a \<Rightarrow> lnat"  (* Debatable *)

  assumes ubdom_fix: "\<And> x y. x\<sqsubseteq>y \<Longrightarrow> ubDom\<cdot>x = ubDom\<cdot>y"
  assumes ubdom_ex: "\<And>C. \<exists>x. ubDom\<cdot>x = C"
    
  assumes ublen_mono: "monofun ubLen"
  assumes ublen_inf_ex: "\<exists>ub. ubLen ub = \<infinity>"
begin
end

class ubcl_comp = ubcl +
  fixes ubLeast :: "channel set \<Rightarrow> 'a"
  fixes ubUnion :: "'a \<rightarrow> 'a \<rightarrow> 'a"
  fixes ubRestrict :: "channel set \<Rightarrow> 'a \<rightarrow> 'a"
  
  assumes ubdom_least: "\<And> x. ubLeast (ubDom\<cdot>x)\<sqsubseteq>x"
  assumes ubdom_least_cs: "\<And> cs. ubDom\<cdot>(ubLeast cs) = cs"

  assumes ubunion_ubdom: "ubDom\<cdot>(ubUnion\<cdot>f1\<cdot>f2) = ubDom\<cdot>f1 \<union> ubDom\<cdot>f2"
  assumes ubunion_ubrestrict: "ubRestrict cs\<cdot>(ubUnion\<cdot>f1\<cdot>f2) = ubUnion\<cdot>(ubRestrict cs\<cdot>f1)\<cdot>(ubRestrict cs\<cdot>f2)" 
  assumes ubrestrict_ubdom: "ubDom\<cdot>(ubRestrict cs\<cdot>b) = ubDom\<cdot>b \<inter> cs"

  assumes ubunion_restrict: "(ubDom\<cdot>y) \<inter> cs = {} \<Longrightarrow> ubRestrict cs\<cdot>(ubUnion\<cdot>f1\<cdot>f2) = ubRestrict cs\<cdot>x"
begin
end  
  

(****************************************************)
section\<open>Universal Stream Processing Function\<close>
(****************************************************) 


(* First a general class for USPF/USPFw/USPFs *)
class ufuncl = cpo +
  fixes ufDom :: "'a \<rightarrow> channel set"
  fixes ufRan :: "'a \<rightarrow> channel set"
  
  assumes ufDom_fix: "\<And>x y. x\<sqsubseteq>y \<Longrightarrow> ufDom\<cdot>x = ufDom\<cdot>y" 
  assumes ufRan_fix: "\<And>x y. x\<sqsubseteq>y \<Longrightarrow> ufRan\<cdot>x = ufRan\<cdot>y" 
begin
end

class ufuncl_comp = ufuncl +
  fixes ufunclComp :: "'a \<rightarrow> 'a \<rightarrow> 'a"  (* Here we can put the abbreviation \<otimes> *)
begin
end


end