(*  Title:        UFun
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

  
definition ufWell:: "('in \<rightarrow> 'out option) \<Rightarrow> bool" where
"ufWell f \<equiv> (\<exists>In. \<forall>b. (b \<in> dom (Rep_cfun f) \<longleftrightarrow> ubDom\<cdot>b = In)) \<and> 
              (\<exists>Out. \<forall>b. (b \<in> ran (Rep_cfun f) \<longrightarrow> ubDom\<cdot>b = Out))"

lemma ufWell_exists: "\<exists>x::('in \<rightarrow> 'out option). ufWell x"
proof - 
  obtain inf_ub:: "'out"  where inf_ub_ublen: "ubLen inf_ub = \<infinity>"
    using ublen_inf_ex by auto
  obtain ufun1:: "'in \<Rightarrow> 'out option" where ufun1_def: "ufun1 = (\<lambda> f. if ubDom\<cdot>f = {} then  Some inf_ub else None)"
    by simp
  have f1: "cont ufun1"
    apply(rule contI2)
    apply (simp add: monofun_def ubdom_fix ufun1_def)
    by (smt below_refl is_ub_thelub po_class.chainI ubdom_fix ufun1_def)
  have f2: "(Rep_cfun (Abs_cfun ufun1)) = ufun1"
    using f1 by auto
  have f3: "ufWell (Abs_cfun ufun1)"
    apply (simp only: ufWell_def f2, rule)
    apply (metis domIff option.distinct(1) ufun1_def)
    apply (rule_tac x = "ubDom\<cdot>inf_ub" in exI)
    by (smt CollectD option.distinct(1) option.sel ran_def ufun1_def)
  thus ?thesis
    by auto
qed
    
lemma ufWell_adm: "adm (\<lambda>f. ((\<exists>In. \<forall>b. (b \<in> dom (Rep_cfun f) \<longleftrightarrow> ubDom\<cdot>b = In)) \<and> 
              (\<exists>Out. \<forall>b. (b \<in> ran (Rep_cfun f) \<longrightarrow> ubDom\<cdot>b = Out))))" (is "adm( ?P )")
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a \<rightarrow> 'b option"
  assume chY: "chain Y" and  as2: "\<forall>i. ?P (Y i)"
  hence f1: "\<And>i. Rep_cfun (Y i) \<sqsubseteq> Rep_cfun (\<Squnion>i. Y i)" by (meson below_cfun_def is_ub_thelub)
  hence f2: "\<And>i. dom (Rep_cfun (Y i)) =  dom (Rep_cfun (\<Squnion>i. Y i))" by (simp add: part_dom_eq)
  have f0: "\<forall>i.(\<exists>Out::channel set. \<forall>b::'b. b \<in> ran (Rep_cfun (Y i)) \<longrightarrow> ubDom\<cdot>b = Out)"
    using as2 by simp 
  hence f01: "\<forall>i.(\<exists>Out::channel set. \<forall>b::'a. b \<in> dom (Rep_cfun (\<Squnion>i. Y i)) \<longrightarrow> ubDom\<cdot>(the ((Y i)\<cdot>b)) = Out)"
    by (metis (mono_tags, lifting) domD f2 mem_Collect_eq option.sel ran_def) 
  hence f4: "\<forall>i. \<forall>j\<ge>i. (\<forall>b::'a. b \<in> dom (Rep_cfun (\<Squnion>i. Y i)) \<longrightarrow> (the ((Y i)\<cdot>b)) \<sqsubseteq> (the ((Y j)\<cdot>b)))"
    by (metis f2 chY domIff monofun_cfun_fun option.collapse po_class.chain_mono some_below2)
  hence f4: "\<forall>i. \<forall>j\<ge>i. (\<forall>b::'a. b \<in> dom (Rep_cfun (\<Squnion>i. Y i)) \<longrightarrow> ubDom\<cdot>(the ((Y i)\<cdot>b)) = ubDom\<cdot>(the ((Y j)\<cdot>b)))"
    by (simp add: ubdom_fix)
  then obtain Out where f6: "\<forall>i::nat. (\<forall>b::'a. b \<in> dom (Rep_cfun (\<Squnion>i. Y i)) \<longrightarrow> ubDom\<cdot>(the ((Y i)\<cdot>b)) = Out)"
    by (metis f01 le_cases)
  hence f7: "(\<forall>b::'a. b \<in> dom (Rep_cfun (\<Squnion>i. Y i)) \<longrightarrow> ubDom\<cdot>(the ((\<Squnion>i. Y i)\<cdot>b)) = Out)"
    by (metis cfun_below_iff chY domIff f2 is_ub_thelub option.collapse some_below2 ubdom_fix)
  hence f8: "\<forall>b::'b. b \<in> ran (Rep_cfun (\<Squnion>i. Y i)) \<longrightarrow> ubDom\<cdot>b = Out"
    by (smt CollectD domI option.sel ran_def)
  hence f10: "\<exists>Out::channel set. \<forall>b::'b. b \<in> ran (Rep_cfun (\<Squnion>i::nat. Y i)) \<longrightarrow> ubDom\<cdot>b = Out"
    by simp
  show "?P (\<Squnion>i. Y i)"
    apply rule
    apply (metis as2 below_cfun_def chY is_ub_thelub part_dom_eq)
    using f10 by blast
qed

lemma ufWell_adm2: "adm (\<lambda>f. ufWell f)"
  apply(simp add: ufWell_def)
  using ufWell_adm by blast
  
(* Define the type 'm USPF (Very Universal Stream Processing Functions) as cpo *)
cpodef ('in,'out) ufun ("(_ \<Rrightarrow>/ _)" [20, 20] 20) = "{f :: 'in \<rightarrow> 'out option . ufWell f}"
  apply (simp add: ufWell_exists)
  using ufWell_adm2 by auto

  
(****************************************************)
section\<open>Definitions\<close>
(****************************************************)   
  
(* ufDom *) 
definition ufDom :: "('in \<Rrightarrow> 'out) \<rightarrow> channel set" where
"ufDom \<equiv> \<Lambda> f. ubDom\<cdot>(SOME b. b \<in> dom (Rep_cfun (Rep_ufun f)))" 

(* ufRan *)
definition ufRan :: "('in,'out) ufun \<rightarrow> channel set" where
"ufRan \<equiv> \<Lambda> f. ubDom\<cdot>(SOME b. b \<in> ran (Rep_cfun (Rep_ufun f)))" 

(* spfType *)

(* spfIO *)

(* apply *)


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
 
(* ufDom *) 

(* ufRan *)

(* spfType *)

(* spfIO *)

(* apply *)
  

end