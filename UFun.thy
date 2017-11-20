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

(* Shorter version to get to normal functions from 'm SPF's *)
abbreviation Rep_cufun:: "('in, 'out) ufun \<Rightarrow> ('in \<Rightarrow> 'out option)" where
"Rep_cufun F \<equiv>  Rep_cfun (Rep_ufun F) "

(* Shorter version to get from normal functions to 'm SPF's *)
  (* of course the argument should be "spf_well" and "cont" *)
abbreviation Abs_cufun:: "('in \<Rightarrow> 'out option) \<Rightarrow> ('in, 'out) ufun " where
"Abs_cufun F \<equiv> Abs_ufun (Abs_cfun F)"
  
(****************************************************)
section\<open>Definitions\<close>
(****************************************************)   
  
(* ufDom *) 
definition ufDom :: "('in \<Rrightarrow> 'out) \<rightarrow> channel set" where
"ufDom \<equiv> \<Lambda> f. ubDom\<cdot>(SOME b. b \<in> dom (Rep_cfun (Rep_ufun f)))" 

(* ufRan *)
definition ufRan :: "('in,'out) ufun \<rightarrow> channel set" where
"ufRan \<equiv> \<Lambda> f. ubDom\<cdot>(SOME b. b \<in> ran (Rep_cfun (Rep_ufun f)))" 

(* ufLeast *)
definition ufLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> ('in \<Rrightarrow> 'out)" where
"ufLeast cin cout = Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = cin) \<leadsto> ubLeast cout)"

(* ufComp *)
(* We can reuse this composition in the subtypes, for weak/strong causal stuff *)
definition ufComp :: "('m \<Rrightarrow> 'm) \<rightarrow> ('m \<Rrightarrow> 'm) \<rightarrow> ('m \<Rrightarrow> 'm)" where
"ufComp = undefined"

(* spfType *)

(* spfIO *)

(* apply *)

(* Composition channel sets *)

(* sbFix *)

(* Composition *)


(****************************************************)
section\<open>Subtype\<close>
(****************************************************) 

  
(* return true iff tickcount holds *)
definition ufIsWeak :: "('in,'out) ufun \<Rightarrow> bool" where
"ufIsWeak f = (\<forall>b. (b \<in> dom (Rep_cfun (Rep_ufun f)) \<longrightarrow> ubLen b \<le> ubLen (the ((Rep_ufun f)\<cdot>b))))"


lemma ufIsWeak_adm: "adm (\<lambda> f. (\<forall>b. (b \<in> dom (Rep_cfun (Rep_ufun f)) \<longrightarrow> ubLen b \<le> ubLen (the ((Rep_ufun f)\<cdot>b)))))" (is "adm( ?P )")
proof (rule admI)
  fix Y :: "nat \<Rightarrow> (('a,'b) ufun)"
  assume chY: "chain Y" and  as2: "\<forall>i. ?P (Y i)"
  show "?P (\<Squnion>i. Y i)"
  proof (auto)
    fix b:: "'a"
    fix y:: "'b"
    fix i2:: "nat"
    assume as3: "Rep_cufun (\<Squnion>i. Y i) b = Some y"
    obtain c where c_def: "Rep_cufun (Y i2) b = Some c"
      by (metis as3 below_cfun_def below_ufun_def chY domD domI is_ub_thelub part_dom_eq)
    show "ubLen b \<le> ubLen y"
      by (metis (no_types, lifting) ublen_mono as2 as3 below_ufun_def c_def cfun_below_iff chY domI is_ub_thelub 
          lnle_def monofun_def option.sel some_below2 trans_lnle)
  qed
qed

lemma ufIsWeak_adm2: "adm (\<lambda>f. ufIsWeak f)"
  by  (simp add: ufIsWeak_def ufIsWeak_adm)

(*  
lemma uf_least_well: "ufWell (Abs_cfun (\<lambda> f. if ubDom\<cdot>f = {} then  Some (ubLeast {}) else None))"
*)

lemma rep_abs_ufun: assumes "ufWell  f" shows "(Rep_ufun (Abs_ufun f)) = f"
  by (simp add: Abs_ufun_inverse assms)

lemma rep_abs_cufun: assumes "cont f" and 
  "ufWell  (Abs_cfun f)" shows "(Rep_cufun (Abs_cufun f)) = f"
  by (simp add: assms(1) assms(2) rep_abs_ufun)

definition emptydom_fun:: "'a \<Rightarrow> 'b option"
  where "emptydom_fun = (\<lambda>f. (ubDom\<cdot>f = {})\<leadsto> (ubLeast (ubDom\<cdot>f)))"

lemma emptydom_fun_cont: "cont emptydom_fun"
  apply (simp add: emptydom_fun_def, rule contI)
  by (smt cont_def image_cong is_ub_thelub some_cont ubdom_fix uf_least_cont)


lemma emptydom_fun_ufwell: "ufWell (Abs_cfun emptydom_fun)"
  apply(simp only: ufWell_def)
  apply rule
   apply(simp add: emptydom_fun_cont)
  apply (metis (full_types) domIff emptydom_fun_def option.simps(3))
  apply (simp add: emptydom_fun_cont ran_def)
  by (metis emptydom_fun_def option.sel option.simps(3))


thm ufIsWeak_def
(*
lemma emptydom_fun_ufisweak: "ufIsWeak (Abs_ufun (Abs_cfun emptydom_fun))"
  apply (simp  add: ufIsWeak_def)
  apply (subst rep_abs_cufun)
    apply (simp add: emptydom_fun_cont)
   apply (simp add: emptydom_fun_ufwell)
  apply (subst rep_abs_cufun)
    apply (simp add: emptydom_fun_cont)
   apply (simp add: emptydom_fun_ufwell)
  sorry
*)


lift_definition bla :: "('in, 'in) ufun" 
is "Abs_ufun (Abs_cfun (\<lambda>f. (f = ubLeast {})\<leadsto> (ubLeast {})))"
  done

lemma bla_ufIsWeak: "ufIsWeak bla"
  sorry


cpodef ('in,'out)  USPFw = "{f ::  ('in,'out) ufun. ufIsWeak f}"
  using bla_ufIsWeak apply auto[1]
  using ufIsWeak_adm2 by auto



definition ufIsStrong :: "('in,'out) ufun \<Rightarrow> bool" where
"ufIsStrong f = (\<forall>b. (b \<in> dom (Rep_cfun (Rep_ufun f)) \<longrightarrow> lnsuc\<cdot>(ubLen b) \<le> ubLen (the ((Rep_ufun f)\<cdot>b))))"

cpodef ('in,'out) USPFs = "{f :: ('in,'out) ufun. ufIsStrong f}"
sorry


(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)   
   subsection \<open>Rep_ufun / Abs_ufun\<close>

lemma Rep_ufun_chain [simp]: assumes "chain Y" shows "chain (\<lambda>i. Rep_ufun (Y i))"
  by (meson assms below_ufun_def po_class.chain_def)

lemma Rep_ufun_mono [simp]: "monofun Rep_ufun"
  by (meson below_ufun_def monofunI)

(* The newly defined Rep_SPF is a continuous function *)
lemma Rep_ufun_cont [simp]: "cont Rep_ufun"
  using cont_Rep_ufun cont_id by blast


lemma Rep_ufun_well [simp]:  "ufWell (Rep_ufun s)"
  using Rep_ufun by blast

lemma Rep_cufun_cont [simp]: "cont Rep_cufun"
  by simp

lemma Rep_cufun_well [simp]: "ufWell (Abs_cfun (Rep_cufun x))"
  by (simp add: Cfun.cfun.Rep_cfun_inverse)

lemma Rep_cufun_cont2 [simp]: "cont (Rep_cufun x)"
  by simp

lemma Rep_Abs_cufun [simp]: assumes "cont f" and "ufWell (Abs_cfun f)" 
  shows "Rep_cufun (Abs_cufun f) = f"
  by (simp add: Abs_ufun_inverse assms(1) assms(2))

lemma [simp]: "ufWell f \<Longrightarrow> Rep_ufun (Abs_ufun f) = f"
  by (simp add: Abs_ufun_inverse)

  (* lemmata for reverse substitution *)
lemma Abs_cufun_rev: "Abs_ufun (Abs_cfun F) = Abs_cufun F"
  by simp
    
lemma Rep_cufun_rev: "Rep_cfun (Rep_ufun F) = Rep_cufun F"
  by simp


subsection \<open>ufun_definition\<close>

text{*  introduction rules for mono proofs *}
lemma ufun_monoI2 [simp]: assumes "\<And> x y. ubDom\<cdot>x = In \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> (g x) \<sqsubseteq> (g y)"
  shows "monofun (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)"
  by (simp add: assms monofunI some_below ubdom_fix)
 
text{* introduction rules for cont proofs *}
lemma ufun_contI [simp]: assumes "\<And> x y. ubDom\<cdot>x = In \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> (g x) \<sqsubseteq> (g y)"
                  and "\<And> Y. chain Y \<Longrightarrow> (ubDom\<cdot>(\<Squnion>i. Y i) = In) \<Longrightarrow> g (\<Squnion>i. Y i)\<sqsubseteq> (\<Squnion>i. (g (Y i)))"
  shows "cont (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)"
    apply (rule contI2)
   apply (simp only: assms(1) ufun_monoI2)
  by (smt assms(1) assms(2) below_option_def is_ub_thelub lub_eq op_the_lub 
      option.sel option.simps(3) po_class.chain_def ubdom_fix)

text{* Alternative Intro rule for SPF is mono with stronger assumptions than 
         @{thm (prem 1) ufun_monoI2} *}
lemma ufun_monoI3 [simp]: assumes "monofun g"
  shows "monofun (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)"
    apply (rule ufun_monoI2)
    using assms monofunE by blast
  
text{* Alternative Intro rule for SPF is cont with stronger assumptions than 
         @{thm (prem 1) ufun_contI} *}
lemma ufun_contI2 [simp]: assumes "cont g"
  shows "cont (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)"
proof(rule contI2)
  show "monofun (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)"
    by (simp add: assms cont2mono)
  thus " \<forall>Y. chain Y \<longrightarrow> (ubDom\<cdot>(\<Squnion>i. Y i) = In)\<leadsto>g (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. (ubDom\<cdot>(Y i) = In)\<leadsto>g (Y i))"
    by (smt assms below_refl if_then_lub2 is_ub_thelub lub_eq po_class.chain_def ubdom_fix)
qed


text{* Intro rule for ufun well *}
lemma ufun_wellI:  assumes "\<And>b. (b \<in> dom (Rep_cfun f)) \<Longrightarrow> (ubDom\<cdot>b = In)"
  and "(\<And>b. b \<in> dom (Rep_cfun f) \<Longrightarrow> ubDom\<cdot>((Rep_cfun f)\<rightharpoonup>b) = Out)"
  and "\<And>b2. (ubDom\<cdot>b2 = In) \<Longrightarrow> (b2 \<in> dom (Rep_cfun f))"
  shows "ufWell f"
  apply (simp add: ufWell_def)
  apply rule
   apply (meson assms(1) assms(3))
  by (smt assms(2) domI mem_Collect_eq option.sel ran_def)
    


(* only 'm SBs with the same domain are in an 'm SPF *)
lemma ufun_sbdom2dom: assumes "ubDom\<cdot>x = ubDom\<cdot>y" 
  shows "x\<in>dom (Rep_cufun f) \<longleftrightarrow>y\<in>dom (Rep_cufun f)"
  by (metis Rep_ufun_well assms ufWell_def)

(* only 'm SBs with the same domain are in an 'm SPF *)
lemma ufun_dom2sbdom: assumes "x\<in>dom (Rep_cufun f)" and "y\<in>dom (Rep_cufun f)" 
  shows "ubDom\<cdot>x = ubDom\<cdot>y"
  by (metis Rep_ufun_well assms(1) assms(2) ufWell_def)


(* helper function for "ufun_ran2sbdom". Somehow it doesn't work without *)
lemma ran2exists[simp]: assumes "x\<in>(ran f)"
  shows "\<exists> xb. ((f xb) = (Some x))"
  using assms by (simp add: ran_def)

(* only 'm SBs with the same domain are in an 'm SPF *)
lemma ufun_ran2sbdom: assumes "x\<in>ran (Rep_cufun f)" and "y\<in>ran (Rep_cufun f)" 
  shows "ubDom\<cdot>x = ubDom\<cdot>y"
  using Rep_ufun_well assms(1) assms(2) ufWell_def by blast


(* if 2 'm SPF's are in a below-relation their Input-Channels are equal *)
lemma ufun_below_sbdom: assumes "a\<sqsubseteq>b" and "x \<in> dom (Rep_cufun b)" and "y \<in> dom (Rep_cufun a)"
  shows "ubDom\<cdot>x = ubDom\<cdot>y"
  by (metis assms(1) assms(2) assms(3) below_cfun_def below_ufun_def part_dom_eq ufun_dom2sbdom)


(* if 2 'm SPF's are in a below-relation their Output-Channels are equal *)
lemma ufun_below_ran: assumes "a\<sqsubseteq>b" and "x \<in> ran (Rep_cufun b)" and "y \<in> ran (Rep_cufun a)"
  shows "ubDom\<cdot>x = ubDom\<cdot>y"
  proof -
    obtain sx where sx_def: "((Rep_cufun b) sx) =  (Some x)" 
      using assms ran2exists by fastforce
    obtain sy where sy_def: "((Rep_cufun a) sy) =  (Some y)" 
      using assms ran2exists by fastforce

    have "dom (Rep_cufun a) = dom (Rep_cufun b) " 
      by (meson assms(1) below_cfun_def below_ufun_def part_dom_eq)
    thus ?thesis
      by (metis (no_types, lifting) Rep_ufun_well assms(1) assms(3) below_ufun_def cfun_below_iff domD domI ranI some_below2 sx_def ubdom_fix ufWell_def)
qed

lemma ufun_pref_eq: assumes "(a \<sqsubseteq> b)"
  shows "((Rep_cufun f) a) \<sqsubseteq> ((Rep_cufun f) b)"
  by (simp add: assms monofun_cfun_arg)
    
lemma ufun_arg_eqI: assumes "(a = b)"
  shows "(Rep_cufun f) a = (Rep_cufun f) b"
  by (simp add: assms)


(* ufDom *) 

(* ufRan *)

(* ufLeast *)

(* ufComp *)

(* spfType *)

(* spfIO *)

(* apply *)

(* Composition channel sets *)

(* sbFix *)

(* Composition *)  

end