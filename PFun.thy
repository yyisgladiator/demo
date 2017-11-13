(*  Title:        PFun
    Author:       Stüber, Jens, Marc
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "Processing functions" 
*)

theory PFun
  imports UnivClasses
begin

(****************************************************)
section\<open>Data type\<close>
(****************************************************) 
  
  
default_sort usb

  
definition pfWell:: "('in \<rightarrow> 'out option) \<Rightarrow> bool" where
"pfWell f \<equiv> (\<exists>In. \<forall>b. (b \<in> dom (Rep_cfun f) \<longleftrightarrow> usbDom\<cdot>b = In)) \<and> 
              (\<exists>Out. \<forall>b. (b \<in> ran (Rep_cfun f) \<longrightarrow> usbDom\<cdot>b = Out))"

declare [[show_types]]
lemma pf_least_cont: "cont [usbLeast {} \<mapsto> usbLeast {}]"
proof - 
  have f00: "\<And>cs. usbDom\<cdot>(usbLeast cs) = cs"
    sorry
  have f0: "\<And>(x::'a) y::'a. x \<sqsubseteq> y \<Longrightarrow> [usbLeast {} \<mapsto> usbLeast {}] x \<sqsubseteq> [usbLeast {} \<mapsto> usbLeast {}] y"
  proof - 
    fix x :: "'a" 
    fix y :: "'a"
    assume "x \<sqsubseteq> y"
    show "[usbLeast {} \<mapsto> usbLeast {}] x \<sqsubseteq> [usbLeast {} \<mapsto> usbLeast {}] y"
    proof(cases "usbDom\<cdot>x = {}")
      case True
      then show ?thesis 
        sorry
    next
      case False
      then show ?thesis 
        by (metis \<open>(x::'a) \<sqsubseteq> (y::'a)\<close> f00 fun_upd_apply po_eq_conv usbdom_fix)
    qed
  qed
  have f1: "\<And>Y::nat \<Rightarrow> 'a. chain Y \<Longrightarrow> [usbLeast {} \<mapsto> usbLeast {}] (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. [usbLeast {} \<mapsto> usbLeast {}] (Y i))"
  proof - 
    fix Y :: "nat \<Rightarrow> 'a"
    assume f2: "chain Y"
    have f3: "\<forall>i. usbDom\<cdot>(Y i) = usbDom\<cdot>(Lub Y)"
      by (simp add: f2 is_ub_thelub usbdom_fix)
    show "([usbLeast {} \<mapsto> usbLeast {}] (\<Squnion>i. Y i)) \<sqsubseteq> (\<Squnion>i. [usbLeast {} \<mapsto> usbLeast {}] (Y i))"
    proof(cases "usbDom\<cdot>(Lub Y) = {}")
      case True
      then show ?thesis 
        (* proof found by sledgehammer *)
        sorry
    next
      case False
      have f5:"usbDom\<cdot>(usbLeast {}) = {}"
        by (simp add: f00)
      then have f6: "[usbLeast {} \<mapsto> usbLeast {}] (\<Squnion>i. Y i) = None"
        using False by auto
      have f7: "\<forall>i. [usbLeast {} \<mapsto> usbLeast {}] (Y i) = None"
        by (metis False f3 f5 fun_upd_apply)
      then show ?thesis 
        by (metis (mono_tags, lifting) below_option_def f6 op_is_lub optionLub_def po_class.chainI)
    qed
  qed
  show ?thesis
    apply(rule contI2)
     apply(simp add: f0)
      using f1 by blast
qed
    
lemma pf_least_well: "pfWell (Abs_cfun [usbLeast {} \<mapsto> usbLeast {}])"
  sorry
    
lemma pfWell_adm: "adm pfWell"
  sorry

(* Define the type 'm USPF (Very Universal Stream Processing Functions) as cpo *)
cpodef ('in,'out) pfun = "{f :: 'in \<rightarrow> 'out option . pfWell f}"
  using pf_least_well apply auto[1]
  using pfWell_adm by auto

type_synonym 'm uSPF = "('m, 'm) pfun"

  
(****************************************************)
section\<open>Definitions\<close>
(****************************************************)   
  
  
definition uspfDom :: "('in,'out) pfun \<rightarrow> channel set" where
"uspfDom \<equiv> \<Lambda> f. usbDom\<cdot>(SOME b. b \<in> dom (Rep_cfun (Rep_pfun f)))" 

definition uspfRan :: "('in,'out) pfun \<rightarrow> channel set" where
"uspfRan \<equiv> \<Lambda> f. usbDom\<cdot>(SOME b. b \<in> ran (Rep_cfun (Rep_pfun f)))" 

definition uspfLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> ('in,'out) pfun" where
"uspfLeast cin cout = Abs_pfun (\<Lambda>  sb.  (usbDom\<cdot>sb = cin) \<leadsto> usbLeast cout)"

(* We can reuse this composition in the subtypes, for weak/strong causal stuff *)
definition uspfComp :: "'m uSPF \<rightarrow> 'm uSPF \<rightarrow> 'm uSPF" where
"uspfComp = undefined"


(****************************************************)
section\<open>Subtype\<close>
(****************************************************) 

  
(* return true iff tickcount holds *)
definition uspfIsWeak :: "('in,'out) pfun \<Rightarrow> bool" where
"uspfIsWeak f = (\<forall>b. (b \<in> dom (Rep_cfun (Rep_pfun f)) \<longrightarrow> usbLen b \<le> usbLen (the ((Rep_pfun f)\<cdot>b))))"

cpodef ('in,'out)  USPFw = "{f ::  ('in,'out) pfun. uspfIsWeak f}"
sorry

definition uspfIsStrong :: "('in,'out) pfun \<Rightarrow> bool" where
"uspfIsStrong f = (\<forall>b. (b \<in> dom (Rep_cfun (Rep_pfun f)) \<longrightarrow> lnsuc\<cdot>(usbLen b) \<le> usbLen (the ((Rep_pfun f)\<cdot>b))))"

cpodef ('in,'out) USPFs = "{f :: ('in,'out) pfun. uspfIsStrong f}"
sorry


(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)   
  

end