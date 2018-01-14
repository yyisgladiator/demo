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

  (*
class uscl_pcpo = uscl + pcpo + 
  assumes usOkay_bot: "\<And>c. usOkay c \<bottom>"    (* used for ubLeast wellformed proof *)
begin
end  
*)

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
  
  assumes ubunion_dom: "ubDom\<cdot>(ubUnion\<cdot>f1\<cdot>f2) = ubDom\<cdot>f1 \<union> ubDom\<cdot>f2"
  assumes ubunion_restrict: "ubRestrict cs\<cdot>(ubUnion\<cdot>f1\<cdot>f2) = ubUnion\<cdot>(ubRestrict cs\<cdot>f1)\<cdot>(ubRestrict cs\<cdot>f2)" 
  assumes ubrestrict_dom: "ubDom\<cdot>(ubRestrict cs\<cdot>b) = ubDom\<cdot>b \<inter> cs"  
    
  (* we need this assm to proof the equality between ufComp and ufParComp *)
  assumes ubunion_restrict_R: "(ubDom\<cdot>y) \<inter> cs = {} \<Longrightarrow> ubRestrict cs\<cdot>(ubUnion\<cdot>x\<cdot>y) = ubRestrict cs\<cdot>x"
  (* we need this assm to proof the equality between ufComp and ufSerComp *)
  assumes ubunion_restrict2 :"ubRestrict (ubDom\<cdot>y)\<cdot>(ubUnion\<cdot>x\<cdot>y) = y"
  assumes ubrestrict_dom_id: "ubRestrict (ubDom\<cdot>x)\<cdot>x = x"
  assumes ubrestrict_twice: "ubRestrict cs2\<cdot>(ubRestrict cs1\<cdot>ub) = ubRestrict (cs1\<inter>cs2)\<cdot>ub"  
  
  assumes ubdom_least: "\<And> x. ubLeast (ubDom\<cdot>x)\<sqsubseteq>x"
  assumes ubdom_least_cs: "\<And> cs. ubDom\<cdot>(ubLeast cs) = cs"
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
  fixes ufunclComp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<otimes>" 55)
  fixes ufunclParComp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixl "\<parallel>" 55)
  fixes ufunclSerComp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<circ>" 55)
  fixes ufunclFeedbackComp :: "'a \<Rightarrow> 'a"  ("\<mu>" 55)

  fixes ufunclCompWell:: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes ufunclSerCompWell:: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes ufunclParCompWell:: "'a \<Rightarrow> 'a \<Rightarrow> bool"

  assumes ufunclParCompWell_commute: "ufunclParCompWell f1 f2 = ufunclParCompWell f2 f1"
  assumes ufunclCompWell_commute: "ufunclCompWell f1 f2 = ufunclCompWell f2 f1"

  assumes comp_commute: "ufunclCompWell f1 f2 \<Longrightarrow> (f1 \<otimes> f2) = (f2 \<otimes> f1)"
  assumes parcomp_commute: "ufunclParCompWell f1 f2 \<Longrightarrow> (f1 \<parallel> f2) = (f2 \<parallel> f1)"

  assumes parcomp_asso: "ufunclParCompWell f1 f2 \<Longrightarrow>
                      ufunclParCompWell f2 f3 \<Longrightarrow> 
                      ufunclParCompWell f1 f3 \<Longrightarrow>  f1 \<parallel> (f2 \<parallel> f3) = (f1 \<parallel> f2) \<parallel> f3"

  assumes sercomp_asso: "ufunclSerCompWell f1 f2 \<Longrightarrow>
                      ufunclSerCompWell f2 f3 \<Longrightarrow> 
                      ufRan\<cdot>f1 \<inter> ufRan\<cdot>f3 = {} \<Longrightarrow>  f1 \<circ> (f2 \<circ> f3) = (f1 \<circ> f2) \<circ> f3"

begin
end


end
