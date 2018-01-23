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
  (*assumes usclOkay_bot: "\<And>c. usclOkay c \<bottom>"    (* used for ubclLeast wellformed proof *)*)
  assumes usclOkay_adm: "\<And>c. adm (usclOkay c)" (* used to instanciate ubundle *)
begin
end
 

class uscl_pcpo = uscl + pcpo + 
  assumes usclOkay_bot: "\<And>c. usclOkay c \<bottom>"    (* used for ubclLeast wellformed proof *)
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

  assumes ubcldom_fix: "\<And> x y. x\<sqsubseteq>y \<Longrightarrow> ubclDom\<cdot>x = ubclDom\<cdot>y"
  assumes ubcldom_ex: "\<And>C. \<exists>x. ubclDom\<cdot>x = C"
    
  assumes ubcllen_mono: "monofun ubclLen"
  assumes ubcllen_inf_ex: "\<exists>ub. ubclLen ub = \<infinity>"
begin
end

class ubcl_comp = ubcl +
  fixes ubclLeast :: "channel set \<Rightarrow> 'a"
  fixes ubclUnion :: "'a \<rightarrow> 'a \<rightarrow> 'a"
  fixes ubclRestrict :: "channel set \<Rightarrow> 'a \<rightarrow> 'a"
  
  assumes ubclunion_dom: "ubclDom\<cdot>(ubclUnion\<cdot>f1\<cdot>f2) = ubclDom\<cdot>f1 \<union> ubclDom\<cdot>f2"
  assumes ubclunion_restrict: "ubclRestrict cs\<cdot>(ubclUnion\<cdot>f1\<cdot>f2) = ubclUnion\<cdot>(ubclRestrict cs\<cdot>f1)\<cdot>(ubclRestrict cs\<cdot>f2)" 
  assumes ubclrestrict_dom: "ubclDom\<cdot>(ubclRestrict cs\<cdot>b) = ubclDom\<cdot>b \<inter> cs"  
    
  (* we need this assm to proof the equality between ufComp and ufParComp *)
  assumes ubclunion_restrict_R: "(ubclDom\<cdot>y) \<inter> cs = {} \<Longrightarrow> ubclRestrict cs\<cdot>(ubclUnion\<cdot>x\<cdot>y) = ubclRestrict cs\<cdot>x"
  (* we need this assm to proof the equality between ufComp and ufSerComp *)
  assumes ubclunion_restrict2 :"ubclRestrict (ubclDom\<cdot>y)\<cdot>(ubclUnion\<cdot>x\<cdot>y) = y"
  assumes ubclrestrict_dom_id: "ubclRestrict (ubclDom\<cdot>x)\<cdot>x = x"
  assumes ubclrestrict_twice: "ubclRestrict cs2\<cdot>(ubclRestrict cs1\<cdot>ub) = ubclRestrict (cs1\<inter>cs2)\<cdot>ub"  
  
  assumes ubcldom_least: "\<And> x. ubclLeast (ubclDom\<cdot>x)\<sqsubseteq>x"
  assumes ubcldom_least_cs: "\<And> cs. ubclDom\<cdot>(ubclLeast cs) = cs"
  
  assumes ubclunion_ubcldom: "ubclDom\<cdot>(ubclUnion\<cdot>f1\<cdot>f2) = ubclDom\<cdot>f1 \<union> ubclDom\<cdot>f2"
  assumes ubclunion_ubclrestrict: "ubclRestrict cs\<cdot>(ubclUnion\<cdot>f1\<cdot>f2) = ubclUnion\<cdot>(ubclRestrict cs\<cdot>f1)\<cdot>(ubclRestrict cs\<cdot>f2)" 
  assumes ubclrestrict_ubcldom: "ubclDom\<cdot>(ubclRestrict cs\<cdot>b) = ubclDom\<cdot>b \<inter> cs"

  assumes ubclunion_asso:"ubclDom\<cdot>f1 \<inter> ubclDom\<cdot>f2 = {} \<and> ubclDom\<cdot>f2 \<inter> ubclDom\<cdot>f3 = {} \<and> ubclDom\<cdot>f1 \<inter> ubclDom\<cdot>f3 = {} \<longrightarrow> ubclUnion\<cdot>(ubclUnion\<cdot>f1\<cdot>f2)\<cdot>f3 = ubclUnion\<cdot>f1\<cdot>(ubclUnion\<cdot>f2\<cdot>f3)"
  assumes ubclunion_commu: "ubclDom\<cdot>f1 \<inter> ubclDom\<cdot>f2 = {} \<longrightarrow> ubclUnion\<cdot>f1\<cdot>f2 = ubclUnion\<cdot>f2\<cdot>f1"
  assumes ubclunion_test: "(ubclRestrict cs2\<cdot>(ubclRestrict cs1\<cdot>ub)) = (ubclRestrict (cs1\<inter>cs2)\<cdot>ub)"
begin
end  
  

(****************************************************)
section\<open>Universal Stream Processing Function\<close>
(****************************************************) 


(* First a general class for USPF/USPFw/USPFs *)
class ufuncl = cpo +
  fixes ufclDom :: "'a \<rightarrow> channel set"
  fixes ufclRan :: "'a \<rightarrow> channel set"

  assumes ufclDom_fix: "\<And>x y. x\<sqsubseteq>y \<Longrightarrow> ufclDom\<cdot>x = ufclDom\<cdot>y" 
  assumes ufclRan_fix: "\<And>x y. x\<sqsubseteq>y \<Longrightarrow> ufclRan\<cdot>x = ufclRan\<cdot>y" 
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
