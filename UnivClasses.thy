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

class uscl_ind = uscl_conc  +
  fixes usclTake :: "nat \<Rightarrow> 'a  \<rightarrow> 'a"
  fixes usclDrop :: "nat \<Rightarrow> 'a  \<rightarrow> 'a"

  assumes uscl_Hd_Rt : "\<And>x.  x = usclConc (usclTake 1 \<cdot> x)\<cdot>(usclDrop 1 \<cdot> x)"

  assumes usclLen_zero : "\<And>x. usclLen\<cdot>x \<le> 0 \<Longrightarrow> x = \<bottom>"       
  assumes usclLen_bot: "usclLen\<cdot>\<bottom> = (0::lnat)" 

  assumes usclTake_len : "\<And>x n.  usclLen\<cdot>x \<ge> Fin n \<Longrightarrow> usclLen\<cdot>(usclTake n\<cdot>x) = Fin n"
  assumes usclTake_len_le :"\<And>x k m. usclLen\<cdot>x = Fin k \<Longrightarrow> Fin k < Fin m \<Longrightarrow>  usclLen\<cdot>(usclTake m\<cdot>x) = Fin k" 
  assumes usclTake_eq : "\<And>x. usclLen\<cdot>x \<le> Fin n \<Longrightarrow> usclTake n\<cdot>x = x"
  assumes usclTake_well : "\<And> cs s n. (usclOkay cs s \<Longrightarrow> usclOkay cs (usclTake n \<cdot> s))"
  assumes usclTake_below : "\<And>x n. usclTake n\<cdot> x \<sqsubseteq> usclTake (Suc n) \<cdot> x"
  assumes usclTake_lub : "(\<Squnion>i. usclTake i\<cdot>s) = s"

  assumes usclDrop_len : "\<And>x n.  (usclLen\<cdot>x \<le> Fin (Suc n)) = (usclLen\<cdot>(usclDrop (Suc 0)\<cdot>x) \<le> Fin n)" 
  assumes usclDrop_eq : "\<And>x. usclDrop 0 \<cdot> x = x"
  assumes usclDrop_well : "\<And> cs s n. (usclOkay cs s \<Longrightarrow> usclOkay cs (usclDrop n \<cdot> s))"

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
  assumes ubclrestrict_ubcldom: "ubclDom\<cdot>(ubclRestrict cs\<cdot>b) = ubclDom\<cdot>b \<inter> cs"

  assumes ubclunion_ubclrestrict: "ubclRestrict cs\<cdot>(ubclUnion\<cdot>f1\<cdot>f2) = ubclUnion\<cdot>(ubclRestrict cs\<cdot>f1)\<cdot>(ubclRestrict cs\<cdot>f2)" 
  assumes ubclunion_ubclrestrict_minus: "cs2 \<subseteq> ubclDom\<cdot>f2 \<Longrightarrow> ubclUnion\<cdot>(ubclRestrict (cs1 - cs2)\<cdot>f1)\<cdot>f2 =  ubclUnion\<cdot>(ubclRestrict cs1\<cdot>f1)\<cdot>f2"
  assumes ubclunion_ubclrestrict_minus_id: "ubclUnion\<cdot>(ubclRestrict (cs1 - cs2)\<cdot>ub)\<cdot>(ubclRestrict (cs1 \<inter> cs2)\<cdot>ub) = ubclRestrict cs1\<cdot>ub "
  
  assumes ubclunion_id: "ubclUnion\<cdot>ub\<cdot>ub = ub"
  assumes ubclunion_asso:"ubclUnion\<cdot>(ubclUnion\<cdot>ub1\<cdot>ub2)\<cdot>ub3 = ubclUnion\<cdot>ub1\<cdot>(ubclUnion\<cdot>ub2\<cdot>ub3)"
  assumes ubclunion_commu: "ubclDom\<cdot>ub1 \<inter> ubclDom\<cdot>ub2 = {} \<longrightarrow> ubclUnion\<cdot>ub1\<cdot>ub2 = ubclUnion\<cdot>ub2\<cdot>ub1"
begin

lemma ubclrestrict_dom_idI: "ubclDom\<cdot>x = cs \<Longrightarrow> ubclRestrict cs\<cdot>x = x"
  using local.ubclrestrict_dom_id by blast
lemma ubclunion_ubclrestrict_RI:"ubclDom\<cdot>ub = cs \<Longrightarrow> ubclRestrict cs\<cdot>(ubclUnion\<cdot>ub2\<cdot>ub) = ubclRestrict cs\<cdot>ub"
  using local.ubclunion_restrict2 ubclrestrict_dom_idI by auto

lemma ubclunion_lub_sep: assumes "chain Y1" and "chain Y2"
  shows "ubclUnion\<cdot>(Lub Y1)\<cdot>(Lub Y2) = (\<Squnion>i. ubclUnion\<cdot>(Y1 i)\<cdot>(Y2 i))"
proof -
  have "ubclUnion\<cdot>(Lub Y1)\<cdot>(Lub Y2) = (\<Squnion>n. ubclUnion\<cdot>(Y1 n))\<cdot>(Lub Y2) \<and> chain (\<lambda>n. ubclUnion\<cdot>(Y1 n))"
    by (simp add: assms(1) contlub_cfun_arg)
  then show ?thesis
    by (simp add: assms(2) lub_APP)
qed

lemma ubclunion_lub_sep2: assumes "chain Y1" and "chain Y2"
  shows "(\<Squnion>i. ubclUnion\<cdot>(Y1 i)\<cdot>(Y2 i)) = ubclUnion\<cdot>(Lub Y1)\<cdot>(Lub Y2)"
  by (simp add: assms(1) assms(2) ubclunion_lub_sep)

lemma ubclunion_ubclrestrict_id: "ubclDom\<cdot>ub = cs1 \<union> cs2 \<Longrightarrow> cs1 \<inter> cs2 = {} \<Longrightarrow> ubclUnion\<cdot>(ubclRestrict cs1\<cdot>ub)\<cdot>(ubclRestrict cs2\<cdot>ub) = ub"
  by (metis Diff_cancel Un_Diff Un_Diff_Int local.ubclrestrict_dom_id local.ubclrestrict_twice local.ubclunion_ubclrestrict_minus_id)

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
  fixes ufunclLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> 'a"
  
  assumes ufuncldom_least: "\<And> x. ufunclLeast (ufclDom\<cdot>x) (ufclRan\<cdot>x)\<sqsubseteq>x"
  assumes ufuncldom_least_dom: "\<And> cs. ufclDom\<cdot>(ufunclLeast cin cout) = cin"
  assumes ufuncldom_least_ran: "\<And> cs. ufclRan\<cdot>(ufunclLeast cin cout) = cout"

begin
end
(*
class ufuncl_comp = ufuncl +
  fixes ufunclLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> 'a"

  fixes ufunclComp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<otimes>" 55)
  fixes ufunclParComp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"   (infixl "\<parallel>" 55)
  fixes ufunclSerComp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<circ>" 55)
  fixes ufunclFeedbackComp :: "'a \<Rightarrow> 'a"  ("\<mu>" 55)

  fixes ufunclCompWell:: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes ufunclSerCompWell:: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes ufunclParCompWell:: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  
  assumes ufuncldom_least: "\<And> x. ufunclLeast (ufclDom\<cdot>x) (ufclRan\<cdot>x)\<sqsubseteq>x"
  assumes ufuncldom_least_dom: "\<And> cs. ufclDom\<cdot>(ufunclLeast cin cout) = cin"
  assumes ufuncldom_least_ran: "\<And> cs. ufclRan\<cdot>(ufunclLeast cin cout) = cout"

  assumes ufunclParCompWell_commute: "ufunclParCompWell f1 f2 = ufunclParCompWell f2 f1"
  assumes ufunclCompWell_commute: "ufunclCompWell f1 f2 = ufunclCompWell f2 f1"

  assumes ufuncl_comp_dom: "ufunclCompWell f1 f2 \<Longrightarrow> ufclDom\<cdot>(f1 \<otimes> f2) = (ufclDom\<cdot>f1 \<union> ufclDom\<cdot>f2) - (ufclRan\<cdot>f1 \<union> ufclRan\<cdot>f2)"
  assumes ufuncl_comp_ran: "ufunclCompWell f1 f2 \<Longrightarrow> ufclRan\<cdot>(f1 \<otimes> f2) = ufclRan\<cdot>f1 \<union> ufclRan\<cdot>f2"

  assumes ufuncl_parcomp_dom: "ufunclParCompWell f1 f2 \<Longrightarrow> ufclDom\<cdot>(f1 \<parallel> f2) = ufclDom\<cdot>f1 \<union> ufclDom\<cdot>f2"
  assumes ufuncl_parcomp_ran: "ufunclParCompWell f1 f2 \<Longrightarrow> ufclRan\<cdot>(f1 \<parallel> f2) = ufclRan\<cdot>f1 \<union> ufclRan\<cdot>f2"

  assumes ufuncl_sercomp_dom: "ufunclSerCompWell f1 f2 \<Longrightarrow> ufclDom\<cdot>(f1 \<circ> f2) = ufclDom\<cdot>f1"
  assumes ufuncl_sercomp_ran: "ufunclSerCompWell f1 f2 \<Longrightarrow> ufclRan\<cdot>(f1 \<circ> f2) = ufclRan\<cdot>f2"

  assumes ufuncl_feedbackcomp_dom: "ufclDom\<cdot>(ufunclFeedbackComp f) = ufclDom\<cdot>f - ufclRan\<cdot>f"
  assumes ufuncl_feedbackcomp_ran: "ufclRan\<cdot>(ufunclFeedbackComp f) = ufclRan\<cdot>f"

  assumes comp_commute: "ufunclCompWell f1 f2 \<Longrightarrow> (f1 \<otimes> f2) = (f2 \<otimes> f1)"
  assumes parcomp_commute: "ufunclParCompWell f1 f2 \<Longrightarrow> (f1 \<parallel> f2) = (f2 \<parallel> f1)"

  assumes parcomp_asso: "ufunclParCompWell f1 f2 \<Longrightarrow>
                      ufunclParCompWell f2 f3 \<Longrightarrow> 
                      ufunclParCompWell f1 f3 \<Longrightarrow>  f1 \<parallel> (f2 \<parallel> f3) = (f1 \<parallel> f2) \<parallel> f3"

  assumes sercomp_asso: "ufunclSerCompWell f1 f2 \<Longrightarrow>
                      ufunclSerCompWell f2 f3 \<Longrightarrow> f1 \<circ> (f2 \<circ> f3) = (f1 \<circ> f2) \<circ> f3"


  assumes parcompwell_asso: "ufunclParCompWell f1 f2 \<Longrightarrow>
                      ufunclParCompWell f2 f3 \<Longrightarrow> 
                      ufunclParCompWell f1 f3 \<Longrightarrow> ufunclParCompWell f1 (f2 \<parallel> f3)"
  assumes sercompwell_asso: "ufunclSerCompWell f1 f2 \<Longrightarrow>
                      ufunclSerCompWell f2 f3 \<Longrightarrow> 
                       ufclDom\<cdot>f1 \<inter> ufclRan\<cdot>f2 = {} \<Longrightarrow> ufclDom\<cdot>f2 \<inter> ufclRan\<cdot>f3 = {} \<Longrightarrow>  ufunclSerCompWell f1 (f2 \<circ> f3) \<and> ufunclSerCompWell (f1 \<circ> f2) f3"

begin

lemma  sercompwell_asso1: "ufunclSerCompWell f1 f2 \<Longrightarrow>
                      ufunclSerCompWell f2 f3 \<Longrightarrow> 
                      ufclDom\<cdot>f1 \<inter> ufclRan\<cdot>f2 = {} \<Longrightarrow> ufclDom\<cdot>f2 \<inter> ufclRan\<cdot>f3 = {} \<Longrightarrow>  ufunclSerCompWell f1 (f2 \<circ> f3)"
  by (simp add: local.sercompwell_asso)
lemma sercompwell_asso2: "ufunclSerCompWell f1 f2 \<Longrightarrow>
                      ufunclSerCompWell f2 f3 \<Longrightarrow> 
                      ufclDom\<cdot>f1 \<inter> ufclRan\<cdot>f2 = {} \<Longrightarrow> ufclDom\<cdot>f2 \<inter> ufclRan\<cdot>f3 = {} \<Longrightarrow> ufunclSerCompWell (f1 \<circ> f2) f3"
  by (simp add: local.sercompwell_asso)
end
*)

end
