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
  fixes usclOkay :: "channel \<Rightarrow> 'a \<Rightarrow> bool" (* similar to "ctype" in message *)
  fixes usclLen :: "'a \<rightarrow> lnat"

  assumes usclOkay_ex: "\<And>c . \<exists> e. usclOkay c e"
  (*assumes usclOkay_bot: "\<And>c. usclOkay c \<bottom>"    (* used for ubLeast wellformed proof *)*)
  assumes usclOkay_adm: "\<And>c. adm (usclOkay c)" (* used to instanciate ubundle *)
begin
end
 

class uscl_pcpo = uscl + pcpo + 
  assumes usclOkay_bot: "\<And>c. usclOkay c \<bottom>"    (* used for ubLeast wellformed proof *)
begin
end  


class uscl_conc = uscl_pcpo +
  fixes usclConc :: "'a \<Rightarrow> 'a \<rightarrow> 'a"
  assumes usclOkay_conc: "\<And>c. \<And>s1 s2. usclOkay c s1 \<Longrightarrow> usclOkay c s2 \<Longrightarrow> usclOkay c (usclConc s1\<cdot>s2)"
begin
end 


(****************************************************)
section\<open>Universal Stream Bundle\<close>
(****************************************************) 
  

(* This class is just the very basic functions required for an SPF *)
default_sort cpo

class ubcl = cpo +
  fixes ubclDom :: "'a \<rightarrow> channel set"
  fixes ubclLen :: "'a \<Rightarrow> lnat"  (* Debatable *)

  assumes ubdom_fix: "\<And> x y. x\<sqsubseteq>y \<Longrightarrow> ubclDom\<cdot>x = ubclDom\<cdot>y"
  assumes ubdom_ex: "\<And>C. \<exists>x. ubclDom\<cdot>x = C"
    
  assumes ublen_mono: "monofun ubclLen"
  assumes ublen_inf_ex: "\<exists>ub. ubclLen ub = \<infinity>"
begin
end

class ubcl_comp = ubcl +
  fixes ubLeast :: "channel set \<Rightarrow> 'a"
  fixes ubUnion :: "'a \<rightarrow> 'a \<rightarrow> 'a"
  fixes ubRestrict :: "channel set \<Rightarrow> 'a \<rightarrow> 'a"
  
  assumes ubunion_dom: "ubclDom\<cdot>(ubUnion\<cdot>f1\<cdot>f2) = ubclDom\<cdot>f1 \<union> ubclDom\<cdot>f2"
  assumes ubunion_restrict: "ubRestrict cs\<cdot>(ubUnion\<cdot>f1\<cdot>f2) = ubUnion\<cdot>(ubRestrict cs\<cdot>f1)\<cdot>(ubRestrict cs\<cdot>f2)" 
  assumes ubrestrict_dom: "ubclDom\<cdot>(ubRestrict cs\<cdot>b) = ubclDom\<cdot>b \<inter> cs"  
    
  (* we need this assm to proof the equality between ufComp and ufParComp *)
  assumes ubunion_restrict_R: "(ubclDom\<cdot>y) \<inter> cs = {} \<Longrightarrow> ubRestrict cs\<cdot>(ubUnion\<cdot>x\<cdot>y) = ubRestrict cs\<cdot>x"
  (* we need this assm to proof the equality between ufComp and ufSerComp *)
  assumes ubunion_restrict2 :"ubRestrict (ubclDom\<cdot>y)\<cdot>(ubUnion\<cdot>x\<cdot>y) = y"
  assumes ubrestrict_dom_id: "ubRestrict (ubclDom\<cdot>x)\<cdot>x = x"
  assumes ubrestrict_twice: "ubRestrict cs2\<cdot>(ubRestrict cs1\<cdot>ub) = ubRestrict (cs1\<inter>cs2)\<cdot>ub"  
  
  assumes ubdom_least: "\<And> x. ubLeast (ubclDom\<cdot>x)\<sqsubseteq>x"
  assumes ubdom_least_cs: "\<And> cs. ubclDom\<cdot>(ubLeast cs) = cs"
  
  assumes ubunion_ubdom: "ubclDom\<cdot>(ubUnion\<cdot>f1\<cdot>f2) = ubclDom\<cdot>f1 \<union> ubclDom\<cdot>f2"
  assumes ubunion_ubrestrict: "ubRestrict cs\<cdot>(ubUnion\<cdot>f1\<cdot>f2) = ubUnion\<cdot>(ubRestrict cs\<cdot>f1)\<cdot>(ubRestrict cs\<cdot>f2)" 
  assumes ubrestrict_ubdom: "ubclDom\<cdot>(ubRestrict cs\<cdot>b) = ubclDom\<cdot>b \<inter> cs"

  assumes ubunion_asso:"ubclDom\<cdot>f1 \<inter> ubclDom\<cdot>f2 = {} \<and> ubclDom\<cdot>f2 \<inter> ubclDom\<cdot>f3 = {} \<and> ubclDom\<cdot>f1 \<inter> ubclDom\<cdot>f3 = {} \<longrightarrow> ubUnion\<cdot>(ubUnion\<cdot>f1\<cdot>f2)\<cdot>f3 = ubUnion\<cdot>f1\<cdot>(ubUnion\<cdot>f2\<cdot>f3)"
  assumes ubunion_commu: "ubclDom\<cdot>f1 \<inter> ubclDom\<cdot>f2 = {} \<longrightarrow> ubUnion\<cdot>f1\<cdot>f2 = ubUnion\<cdot>f2\<cdot>f1"
  assumes ubunion_test: "(ubRestrict cs2\<cdot>(ubRestrict cs1\<cdot>ub)) = (ubRestrict (cs1\<inter>cs2)\<cdot>ub)"
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
  fixes ufunclSerComp :: "'a \<rightarrow> 'a \<rightarrow> 'a"  (* Here we can put the abbreviation \<circ> *) 
  fixes ufunclParComp :: "'a \<rightarrow> 'a \<rightarrow> 'a"  (* Here we can put the abbreviation \<parallel> *) 
  fixes ufunclFeedbackComp :: "'a \<rightarrow> 'a"  (* Here we can put the abbreviation \<mu> *) 

begin
end


end
