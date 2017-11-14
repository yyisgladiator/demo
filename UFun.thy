(*  Title:        PFun
    Author:       Stüber, Jens, Marc
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "Processing functions" 
*)

theory UFun
  imports UnivClasses
begin

(****************************************************)
section\<open>Data type\<close>
(****************************************************) 
  
  
default_sort ubcl

declare[[show_types]]  
definition ufWell:: "('in \<rightarrow> 'out option) \<Rightarrow> bool" where
"ufWell f \<equiv> (\<exists>In. \<forall>b. (b \<in> dom (Rep_cfun f) \<longleftrightarrow> ubDom\<cdot>b = In)) \<and> 
              (\<exists>Out. \<forall>b. (b \<in> ran (Rep_cfun f) \<longrightarrow> ubDom\<cdot>b = Out))"

declare [[show_types]]
lemma pf_least_cont: "cont [ubLeast {} \<mapsto> ubLeast {}]"
proof - 
  have f00: "\<And>cs. ubDom\<cdot>(ubLeast cs) = cs"
    sorry
  have f0: "\<And>(x::'a) y::'a. x \<sqsubseteq> y \<Longrightarrow> [ubLeast {} \<mapsto> ubLeast {}] x \<sqsubseteq> [ubLeast {} \<mapsto> ubLeast {}] y"
  proof - 
    fix x :: "'a" 
    fix y :: "'a"
    assume "x \<sqsubseteq> y"
    show "[ubLeast {} \<mapsto> ubLeast {}] x \<sqsubseteq> [ubLeast {} \<mapsto> ubLeast {}] y"
    proof(cases "y = ubLeast {}")
      case True
      then show ?thesis 
        by (metis \<open>(x::'a) \<sqsubseteq> (y::'a)\<close> f00 po_eq_conv ubdom_fix ubdom_least)
    next
      case False
      then show ?thesis 
        
        sorry
    qed
  qed
  have f1: "\<And>Y::nat \<Rightarrow> 'a. chain Y \<Longrightarrow> [ubLeast {} \<mapsto> ubLeast {}] (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. [ubLeast {} \<mapsto> ubLeast {}] (Y i))"
  proof - 
    fix Y :: "nat \<Rightarrow> 'a"
    assume f2: "chain Y"
    have f3: "\<forall>i. ubDom\<cdot>(Y i) = ubDom\<cdot>(Lub Y)"
      by (simp add: f2 is_ub_thelub ubdom_fix)
    show "([ubLeast {} \<mapsto> ubLeast {}] (\<Squnion>i. Y i)) \<sqsubseteq> (\<Squnion>i. [ubLeast {} \<mapsto> ubLeast {}] (Y i))"
    proof(cases "ubDom\<cdot>(Lub Y) = {}")
      case True
      then show ?thesis 
        (* proof found by sledgehammer *)
        sorry
    next
      case False
      have f5:"ubDom\<cdot>(ubLeast {}) = {}"
        by (simp add: f00)
      then have f6: "[ubLeast {} \<mapsto> ubLeast {}] (\<Squnion>i. Y i) = None"
        using False by auto
      have f7: "\<forall>i. [ubLeast {} \<mapsto> ubLeast {}] (Y i) = None"
        by (metis False f3 f5 fun_upd_apply)
      then show ?thesis 
        by (metis (mono_tags, lifting) below_option_def f6 op_is_lub optionLub_def po_class.chainI)
    qed
  qed
  show ?thesis
    apply(rule contI2)
     apply(simp only: monofun_def)
      using f0 apply blast
      using f1 by blast
qed
 
lemma uf_least_well: "ufWell (Abs_cfun [ubLeast {} \<mapsto> ubLeast {}])"
  apply(simp add: ufWell_def)
  
  sorry
    
lemma ufWell_adm: "adm (\<lambda>f. ((\<exists>In. \<forall>b. (b \<in> dom (Rep_cfun f) \<longleftrightarrow> ubDom\<cdot>b = In)) \<and> 
              (\<exists>Out. \<forall>b. (b \<in> ran (Rep_cfun f) \<longrightarrow> ubDom\<cdot>b = Out))))" (is "adm( ?P )")
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a \<rightarrow> 'b option"
  assume chY: "chain Y" and  as2: "\<forall>i. ?P (Y i)"
  show "?P (\<Squnion>i. Y i)"
    
    sorry
qed

lemma ufWell_adm2: "adm (\<lambda>f. ufWell f)"
  using ufWell_adm
  by (simp add: ufWell_def)
  
(* Define the type 'm USPF (Very Universal Stream Processing Functions) as cpo *)
cpodef ('in,'out) ufun = "{f :: 'in \<rightarrow> 'out option . ufWell f}"
  using uf_least_well apply auto[1]
  using ufWell_adm2 by auto

type_synonym 'm uSPF = "('m, 'm) ufun"

  
(****************************************************)
section\<open>Definitions\<close>
(****************************************************)   
  
  
definition ufDom :: "('in,'out) ufun \<rightarrow> channel set" where
"ufDom \<equiv> \<Lambda> f. ubDom\<cdot>(SOME b. b \<in> dom (Rep_cfun (Rep_ufun f)))" 

definition ufRan :: "('in,'out) ufun \<rightarrow> channel set" where
"ufRan \<equiv> \<Lambda> f. ubDom\<cdot>(SOME b. b \<in> ran (Rep_cfun (Rep_ufun f)))" 

definition ufLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> ('in,'out) ufun" where
"ufLeast cin cout = Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = cin) \<leadsto> ubLeast cout)"

(* We can reuse this composition in the subtypes, for weak/strong causal stuff *)
definition ufComp :: "'m uSPF \<rightarrow> 'm uSPF \<rightarrow> 'm uSPF" where
"ufComp = undefined"


(****************************************************)
section\<open>Subtype\<close>
(****************************************************) 

  
(* return true iff tickcount holds *)
definition ufIsWeak :: "('in,'out) ufun \<Rightarrow> bool" where
"ufIsWeak f = (\<forall>b. (b \<in> dom (Rep_cfun (Rep_ufun f)) \<longrightarrow> ubLen b \<le> ubLen (the ((Rep_ufun f)\<cdot>b))))"

cpodef ('in,'out)  USPFw = "{f ::  ('in,'out) ufun. ufIsWeak f}"
sorry

definition ufIsStrong :: "('in,'out) ufun \<Rightarrow> bool" where
"ufIsStrong f = (\<forall>b. (b \<in> dom (Rep_cfun (Rep_ufun f)) \<longrightarrow> lnsuc\<cdot>(ubLen b) \<le> ubLen (the ((Rep_ufun f)\<cdot>b))))"

cpodef ('in,'out) USPFs = "{f :: ('in,'out) ufun. ufIsStrong f}"
sorry


(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)   
  

end