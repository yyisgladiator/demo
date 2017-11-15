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

lemma uf_least_cont: "cont (\<lambda> f. if ubDom\<cdot>f = {} then  Some (ubLeast {}) else None)"
proof - 
  have f0: "\<And>(x::'a) y::'a. x \<sqsubseteq> y \<Longrightarrow> (if ubDom\<cdot>x = {} then  Some (ubLeast {}) else None) \<sqsubseteq> (if ubDom\<cdot>y = {} then  Some (ubLeast {}) else None)"
  proof - 
    fix x :: "'a" 
    fix y :: "'a"
    assume "x \<sqsubseteq> y"
    show "(if ubDom\<cdot>x = {} then  Some (ubLeast {}) else None) \<sqsubseteq> (if ubDom\<cdot>y = {} then  Some (ubLeast {}) else None)"
    proof(cases "ubDom\<cdot>x = {}")
      case True
      then show ?thesis 
        using \<open>(x::'a) \<sqsubseteq> (y::'a)\<close> ubdom_fix by auto
    next
      case False
      then show ?thesis 
        using \<open>(x::'a) \<sqsubseteq> (y::'a)\<close> ubdom_fix by auto
    qed
  qed
  have f1: "\<And>Y::nat \<Rightarrow> 'a. chain Y \<Longrightarrow> (if ubDom\<cdot>(\<Squnion>i. Y i) = {} then  Some (ubLeast {}) else None) \<sqsubseteq> (\<Squnion>i. (if ubDom\<cdot>(Y i) = {} then  Some (ubLeast {}) else None))"
  proof - 
    fix Y :: "nat \<Rightarrow> 'a"
    assume f2: "chain Y"
    have f3: "\<forall>i. ubDom\<cdot>(Y i) = ubDom\<cdot>(Lub Y)"
      by (simp add: f2 is_ub_thelub ubdom_fix)
    show "(if ubDom\<cdot>(\<Squnion>i. Y i) = {} then  Some (ubLeast {}) else None) \<sqsubseteq> (\<Squnion>i. (if ubDom\<cdot>(Y i) = {} then  Some (ubLeast {}) else None))"
    proof(cases "ubDom\<cdot>(Lub Y) = {}")
      case True
      then show ?thesis 
        by (simp add: f3)        
    next
      case False
      then show ?thesis 
        by (simp add: f3)
    qed
  qed
  show ?thesis
    apply(rule contI2)
     apply(simp only: monofun_def)
      using f0 apply blast
      using f1 by blast
qed
  
lemma uf_least_well: "ufWell (Abs_cfun (\<lambda> f. if ubDom\<cdot>f = {} then  Some (ubLeast {}) else None))"
  apply(simp add: ufWell_def)
  apply rule
   apply(simp add: uf_least_cont)
  apply (metis (mono_tags, lifting) domIff dom_empty option.distinct(1))
  apply(simp add: uf_least_cont ran_def)
  by blast
    
lemma ufWell_adm: "adm (\<lambda>f. ((\<exists>In. \<forall>b. (b \<in> dom (Rep_cfun f) \<longleftrightarrow> ubDom\<cdot>b = In)) \<and> 
              (\<exists>Out. \<forall>b. (b \<in> ran (Rep_cfun f) \<longrightarrow> ubDom\<cdot>b = Out))))" (is "adm( ?P )")
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a \<rightarrow> 'b option"
  assume chY: "chain Y" and  as2: "\<forall>i. ?P (Y i)"
  show "?P (\<Squnion>i. Y i)"
  proof -
    have f1: "\<exists>Out::channel set. \<forall>b. b \<in> dom (Rep_cfun (\<Squnion>i::nat. Y i)) \<longrightarrow> ubDom\<cdot>(the ((Lub Y)\<cdot>b)) = Out"
    proof -
      { fix aa :: "channel set \<Rightarrow> 'a"
        have ff1: "\<And>c ca. c \<notsqsubseteq> ca \<or> {a. c\<cdot>(a::'a) \<noteq> (None::'b option)} = {a. ca\<cdot>a \<noteq> None}"
          by (metis (no_types) below_cfun_def dom_def part_dom_eq)
        obtain CC :: "nat \<Rightarrow> channel set" where
          ff2: "\<And>a n. a \<notin> {a. Y n\<cdot>a \<noteq> None} \<or> ubDom\<cdot>a = CC n"
          by (metis (no_types) as2 dom_def)
        { assume "\<exists>n. Lub Y\<cdot> (aa (ubDom\<cdot> Rep_cfun (Lub Y)\<rightharpoonup>ubLeast (CC n))) \<noteq> Lub Y\<cdot>(ubLeast (CC n))"
          moreover
          { assume "\<exists>n C. ubLeast (CC n) \<notsqsubseteq> aa C"
            then have "\<exists>C. aa C \<notin> dom (Rep_cfun (Lub Y)) \<or> ubDom\<cdot>Rep_cfun (Lub Y)\<rightharpoonup>aa C = C"
              using ff2 ff1 by (metis chY dom_def is_ub_thelub ubdom_least) }
          ultimately have "(\<exists>C. aa C \<notin> dom (Rep_cfun (Lub Y)) \<or> ubDom\<cdot>Rep_cfun (Lub Y)\<rightharpoonup>aa C = C) \<or> (\<exists>b. b \<sqsubseteq> Rep_cfun (Lub Y)\<rightharpoonup>aa (ubDom\<cdot>b))"
            by (metis (no_types) below_option_def monofun_cfun_arg) }
        then have "(\<exists>C. aa C \<notin> dom (Rep_cfun (Lub Y)) \<or> ubDom\<cdot>Rep_cfun (Lub Y)\<rightharpoonup>aa C = C) \<or> (\<exists>b. b \<sqsubseteq> Rep_cfun (Lub Y)\<rightharpoonup>aa (ubDom\<cdot>b))"
          by (metis (full_types) ubdom_least)
        then have "\<exists>C. aa C \<notin> dom (Rep_cfun (Lub Y)) \<or> ubDom\<cdot>Rep_cfun (Lub Y)\<rightharpoonup>aa C = C"
          by (metis (full_types) ubdom_fix) }
      then show ?thesis
        by meson
    qed
    have f2: "\<forall>b \<in> ran (Rep_cfun (\<Squnion>i::nat. Y i)). \<exists>a \<in> dom (Rep_cfun (\<Squnion>i::nat. Y i)). b = (the ((Lub Y)\<cdot>a))"
      by (smt domI mem_Collect_eq option.sel ran_def)
    show ?thesis
      apply rule
      apply (metis as2 below_cfun_def chY is_ub_thelub part_dom_eq)
      using f1 f2 by metis
  qed
qed

lemma ufWell_adm2: "adm (\<lambda>f. ufWell f)"
  apply(simp add: ufWell_def)
  using ufWell_adm by blast
  
(* Define the type 'm USPF (Very Universal Stream Processing Functions) as cpo *)
cpodef ('in,'out) ufun ("(_ \<Rrightarrow>/ _)" [20, 20] 20) = "{f :: 'in \<rightarrow> 'out option . ufWell f}"
  using uf_least_well apply auto[1]
  using ufWell_adm2 by auto

(* this synonym sucks ... *)
(* type_synonym 'm uSPF = "('m, 'm) ufun" *)

  
(****************************************************)
section\<open>Definitions\<close>
(****************************************************)   
  
  
definition ufDom :: "('in \<Rrightarrow> 'out) \<rightarrow> channel set" where
"ufDom \<equiv> \<Lambda> f. ubDom\<cdot>(SOME b. b \<in> dom (Rep_cfun (Rep_ufun f)))" 

definition ufRan :: "('in,'out) ufun \<rightarrow> channel set" where
"ufRan \<equiv> \<Lambda> f. ubDom\<cdot>(SOME b. b \<in> ran (Rep_cfun (Rep_ufun f)))" 

definition ufLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> ('in \<Rrightarrow> 'out)" where
"ufLeast cin cout = Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = cin) \<leadsto> ubLeast cout)"

(* We can reuse this composition in the subtypes, for weak/strong causal stuff *)
definition ufComp :: "('m \<Rrightarrow> 'm) \<rightarrow> ('m \<Rrightarrow> 'm) \<rightarrow> ('m \<Rrightarrow> 'm)" where
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