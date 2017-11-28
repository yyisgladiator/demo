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


(* Shorter version to get to normal functions from ('in,'out) ufun's *)
abbreviation Rep_cufun:: "('in, 'out) ufun \<Rightarrow> ('in \<Rightarrow> 'out option)" where
"Rep_cufun F \<equiv>  Rep_cfun (Rep_ufun F) "

(* Shorter version to get from normal functions to ('in,'out)  ufun's *)
  (* of course the argument should be "ufun_well" and "cont" *)
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

(* ufType *)
definition ufunType :: "('in,'out) ufun \<rightarrow> (channel set \<times> channel set)" where
"ufunType \<equiv> \<Lambda> f . (ufDom\<cdot>f, ufRan\<cdot>f)"

(* ufunIO *)
definition ufunIO :: "channel set \<Rightarrow> channel set \<Rightarrow> ('in,'out) ufun set" where
"ufunIO In Out = {f. ufDom\<cdot>f = In \<and> ufRan\<cdot>f = Out}"

(* apply *)
abbreviation theRep_abbrv :: "('in,'out) ufun \<Rightarrow> 'in \<Rightarrow> 'out " (infix "\<rightleftharpoons>" 62) where
"(f \<rightleftharpoons> s) \<equiv> (Rep_cufun f)\<rightharpoonup>s"


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
 

subsection \<open>Rep_ufun / Abs_ufun\<close>

     
(* if we have a ufun chain, then we still have a chain after applying rep on each element in the chain  *)
lemma rep_ufun_chain [simp]: assumes "chain Y" shows "chain (\<lambda>i. Rep_ufun (Y i))"
  by (meson assms below_ufun_def po_class.chain_def)

(* rep_ufun is a mono func *)
lemma rep_ufun_mono [simp]: "monofun Rep_ufun"
  by (meson below_ufun_def monofunI)

(* rep_ufun is a continuous function *)
lemma rep_ufun_cont [simp]: "cont Rep_ufun"
  using cont_Rep_ufun cont_id by blast

(* rep_ufun produces a ufwell function  *)
lemma rep_ufun_well [simp]:  "ufWell (Rep_ufun s)"
  using Rep_ufun by blast

(* Rep_cufun is continuous  *)
lemma rep_cufun_cont [simp]: "cont Rep_cufun"
  by simp

(* Rep_cufun produces a ufwell function  *)
lemma rep_cufun_well [simp]: "ufWell (Abs_cfun (Rep_cufun x))"
  by (simp add: Cfun.cfun.Rep_cfun_inverse)

(* applying rep and abs after eachother proces the origin function  *)
lemma rep_abs_cufun [simp]: assumes "cont f" and "ufWell (Abs_cfun f)" 
  shows "Rep_cufun (Abs_cufun f) = f"
  by (simp add: Abs_ufun_inverse assms(1) assms(2))

(* like rep_abs_cufun but with less assm *)
lemma rep_abs_cufun2 [simp]: "ufWell f \<Longrightarrow> Rep_ufun (Abs_ufun f) = f"
  by (simp add: Abs_ufun_inverse)

  (* lemmata for reverse substitution *)
lemma rbs_cufun_rev: "Abs_ufun (Abs_cfun F) = Abs_cufun F"
  by simp
    
lemma rep_cufun_rev: "Rep_cfun (Rep_ufun F) = Rep_cufun F"
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

text{* Alternative Intro rule for ufun is mono with stronger assumptions than 
         @{thm (prem 1) ufun_monoI2} *}
lemma ufun_monoI3 [simp]: assumes "monofun g"
  shows "monofun (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)"
    apply (rule ufun_monoI2)
    using assms monofunE by blast
  
text{* Alternative Intro rule for ufun is cont with stronger assumptions than 
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

(* only 'm ubs with the same domain are in an (in, out) ufun *)
lemma ufun_ufundom2dom: assumes "ubDom\<cdot>x = ubDom\<cdot>y" 
  shows "x\<in>dom (Rep_cufun f) \<longleftrightarrow>y\<in>dom (Rep_cufun f)"
  by (metis rep_ufun_well assms ufWell_def)

(* only 'm ubs with the same domain are in an (in, out) ufun *)
lemma ufun_dom2ufundom: assumes "x\<in>dom (Rep_cufun f)" and "y\<in>dom (Rep_cufun f)" 
  shows "ubDom\<cdot>x = ubDom\<cdot>y"
  by (metis rep_ufun_well assms(1) assms(2) ufWell_def)


(* helper function for "ufun_ran2ufundom" *)
lemma ran2exists[simp]: assumes "x\<in>(ran f)"
  shows "\<exists> xb. ((f xb) = (Some x))"
  using assms by (simp add: ran_def)

(* only 'm ubs with the same domain are in an 'm ufun *)
lemma ufun_ran2ufundom: assumes "x\<in>ran (Rep_cufun f)" and "y\<in>ran (Rep_cufun f)" 
  shows "ubDom\<cdot>x = ubDom\<cdot>y"
  using rep_ufun_well assms(1) assms(2) ufWell_def by blast


(* if 2 (in, out) ufun's are in a below-relation their Input-Channels are equal *)
lemma ufun_below_ufundom: assumes "a\<sqsubseteq>b" and "x \<in> dom (Rep_cufun b)" and "y \<in> dom (Rep_cufun a)"
  shows "ubDom\<cdot>x = ubDom\<cdot>y"
  by (metis assms(1) assms(2) assms(3) below_cfun_def below_ufun_def part_dom_eq ufun_dom2ufundom)


(* if 2 (in, out) ufun's are in a below-relation their Output-Channels are equal *)
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
      by (metis (no_types, lifting) rep_ufun_well assms(1) assms(3) below_ufun_def cfun_below_iff domD domI ranI some_below2 sx_def ubdom_fix ufWell_def)
qed

(*   *)
lemma ufun_rel_eq: assumes "(a \<sqsubseteq> b)"
  shows "((Rep_cufun f) a) \<sqsubseteq> ((Rep_cufun f) b)"
  by (simp add: assms monofun_cfun_arg)

(*   *)
lemma ufun_arg_eqI: assumes "(a = b)"
  shows "(Rep_cufun f) a = (Rep_cufun f) b"
  by (simp add: assms)

(* empty function is not ufWell  *)
lemma map_not_ufun [simp]: "\<not>(ufWell (Abs_cfun empty))"
  apply (simp add: ufWell_def)
  using ubdom_least_cs by auto

(* there is at least one element in a ufun dom *)
lemma ufdom_not_empty [simp]: 
  shows "\<exists>x. x\<in>dom (Rep_cufun F)"
  by (metis domIff ex_in_conv map_not_ufun part_eq rep_cufun_well)

(* there is at least one element in a ufun ran *)
lemma ufran_not_empty [simp]: 
  shows "\<exists>x. x\<in> (ran (Rep_cufun F))"
  by (meson domIff not_None_eq ranI ufdom_not_empty)


subsection \<open>ufDom\<close>
(* ufDom *) 
thm ufDom_def

  
(* mono proof of ufDom  *)
lemma ufdom_mono[simp]: "monofun (\<lambda>f. ubDom\<cdot>(SOME b. b \<in> dom (Rep_cufun f)))"
proof(rule monofunI)
  fix x y:: "('in, 'out) ufun"
  assume "x \<sqsubseteq> y"
  thus "ubDom\<cdot>(SOME b. b \<in> dom (Rep_cufun x)) \<sqsubseteq> ubDom\<cdot>(SOME b. b \<in> dom (Rep_cufun y))"
    by (simp add: below_cfun_def below_ufun_def part_dom_eq)
qed

(* used to show that ufunDom is continuous *)
lemma ufdom_contlub [simp]: assumes "chain Y" 
  shows "ubDom\<cdot>(SOME b. b \<in> dom (Rep_cufun (\<Squnion>i. Y i))) 
         \<sqsubseteq> (\<Squnion>i. ubDom\<cdot>(SOME b. b \<in> dom (Rep_cufun (Y i))))"
proof -
  have "\<And>f n. \<not> chain f \<or> dom (Rep_cufun (f n::'a \<Rrightarrow> 'b)) = dom (Rep_cufun (Lub f))"
    by (meson below_cfun_def below_ufun_def is_ub_thelub part_dom_eq)
  then show ?thesis
    using assms by force
qed

(* ufunDom is continuous *)
lemma ufdom_cont [simp]:"cont (\<lambda>f. ubDom\<cdot>(SOME b. b \<in> dom (Rep_cufun f)))"
  by(simp add: contI2)

  
(* Insertion rule for ufunDom *)
lemma ufdom_insert: "ufDom\<cdot>f = ubDom\<cdot>(SOME b. b \<in> dom (Rep_cufun f))"
  by (simp add: ufDom_def)

(* if two ufuns are in a below relation their ufunDom is equal *)
lemma ufdom_below_eq: assumes "x \<sqsubseteq> y"
  shows "ufDom\<cdot>x = ufDom\<cdot>y"
  by (metis (no_types) assms below_cfun_def below_ufun_def part_dom_eq ufdom_insert)


(* The lub of a chain of ufuns has the same domain as each chain element *)
lemma ufdom_lub_eq: assumes "chain Y"
  shows "ufDom\<cdot>(\<Squnion>i. Y i) = ufDom\<cdot>(Y i)"
  using assms is_ub_thelub ufdom_below_eq by blast

(* if function S applies on a return none null then a has the same dome as the funtion S  *)    
lemma ufdom_2ufundom [simp]: assumes "(Rep_cufun S) a = Some b"
  shows "ufDom\<cdot>S = ubDom\<cdot>a"
  by (metis assms domI someI_ex ufun_dom2ufundom ufdom_insert)

(* ubLeast is in the same dome as the function f  *)
lemma ufunLeastIDom: "(ubLeast (ufDom\<cdot>f)) \<in> dom (Rep_cufun f)"
  by (metis rep_ufun_well domD ubdom_least_cs ufWell_def ufdom_2ufundom)

(* if the function has the same dom then they also have the same dom after rep is applied  *)
lemma ufdom_2_dom_ctufun: assumes "ufDom\<cdot>f = ufDom\<cdot>g"
  shows "dom (Rep_cufun f) = dom (Rep_cufun g)"  
    by (metis (no_types, lifting) Cfun.cfun.Rep_cfun_inverse Collect_cong  assms(1) 
          dom_def mem_Collect_eq rep_cufun_well ufunLeastIDom ufWell_def)

(* induction rule to proof that f is leq g  *)
lemma ufun_belowI: assumes "ufDom\<cdot>f = ufDom\<cdot>g"
          and "\<And>x. (ubDom\<cdot>x = ufDom\<cdot>f \<Longrightarrow> (Rep_cufun f)\<rightharpoonup>x \<sqsubseteq> (Rep_cufun g)\<rightharpoonup>x)"
        shows "f \<sqsubseteq> g"
proof -
  have "dom (Rep_cufun f) = dom (Rep_cufun g)"
    using assms(1) ufdom_2_dom_ctufun by blast
  thus ?thesis
    by (metis (full_types) assms(2) below_cfun_def below_ufun_def domI part_below ran2exists 
        ufran_not_empty ufun_dom2ufundom ufdom_2ufundom)
qed

(* the dom of a function is the if-argument  *)
lemma ufun_ufdom_abs: assumes "cont (\<lambda> x. (ubDom\<cdot>x = cs ) \<leadsto> f(x))" 
                     and "ufWell (\<Lambda> x. (ubDom\<cdot>x = cs ) \<leadsto> f(x))"
                   shows "ufDom\<cdot>(Abs_cufun (\<lambda> x. (ubDom\<cdot>x = cs ) \<leadsto> f(x))) = cs" 
  proof -
    have "ubLeast (UFun.ufDom\<cdot> (Abs_cufun (\<lambda>a. (ubDom\<cdot>a = cs)\<leadsto>f a))) \<in> dom (\<lambda>a. (ubDom\<cdot>a = cs)\<leadsto>f a)"
      by (metis (no_types) assms(1) assms(2) rep_abs_cufun ufunLeastIDom)
    then have "(ubDom\<cdot> (ubLeast (UFun.ufDom\<cdot> (Abs_cufun (\<lambda>a. (ubDom\<cdot>a = cs)\<leadsto>f a)))::'a) = cs)\<leadsto>f (ubLeast (UFun.ufDom\<cdot> (Abs_cufun (\<lambda>a. (ubDom\<cdot>a = cs)\<leadsto>f a)))) \<noteq> None"
      by blast
    then have "ubDom\<cdot> (ubLeast (UFun.ufDom\<cdot> (Abs_cufun (\<lambda>a. (ubDom\<cdot>a = cs)\<leadsto>f a)))::'a) = cs"
      by meson
    then show ?thesis
      using ubdom_least_cs by blast
  qed


  subsection \<open>ufRan\<close>
(* ufRan *)
  thm ufRan_def

    
(* ufRan_def is monotone *)
lemma ufran_mono [simp]: "monofun (\<lambda> F. ubDom\<cdot>(SOME b. b \<in> ran (Rep_cufun F)))"
proof (rule monofunI)
  fix x y :: "('in, 'out) ufun"
  assume "x \<sqsubseteq> y"
  thus "ubDom\<cdot>(SOME b. b \<in> ran (Rep_cufun x)) \<sqsubseteq> ubDom\<cdot>(SOME b. b \<in> ran (Rep_cufun y))"
    by (metis (no_types, lifting) po_eq_conv someI ufun_below_ran ufran_not_empty)
qed

(* helper function for cont proof of ufran  *)
lemma ufran_contlub [simp]: assumes "chain Y"
  shows "ubDom\<cdot>(SOME b. b \<in> ran (Rep_cufun (\<Squnion>i. Y i))) 
          \<sqsubseteq> (\<Squnion>i. ubDom\<cdot>(SOME b. b \<in> ran (Rep_cufun (Y i))))"
  by (metis (no_types, lifting) assms below_refl is_ub_thelub po_class.chain_def 
             someI_ex ufun_below_ran ufran_not_empty)

(* ufRan_def is continuous *)
lemma ufran_cont [simp]: "cont (\<lambda> F. ubDom\<cdot>(SOME b. b \<in> ran (Rep_cufun F)))"
  by (rule contI2, simp_all)

(* Insertion rule for ufran *)
lemma ufran_insert: "ufRan\<cdot>f = ubDom\<cdot>(SOME b. b \<in> ran (Rep_cufun f))"
  by (simp add: ufRan_def)
    
(* If two ufuns are in a below relation their output channels are equal *)
lemma ufran_below: assumes "x \<sqsubseteq> y"
  shows "ufRan\<cdot>x = ufRan\<cdot>y"
  by (smt Abs_cfun_inverse2 assms someI_ex ufRan_def ufun_below_ran ufran_cont 
          ufran_not_empty)

(* the lub of an ufun chain has the same output channels as all the ufuns in the chain *)
lemma ufran_lub_eq: assumes "chain Y"
  shows "ufRan\<cdot>(\<Squnion>i. Y i) = ufRan\<cdot>(Y i)"
  using assms is_ub_thelub ufran_below by blast

(*   *)
lemma ufran_2_ubdom [simp]: assumes "(Rep_cufun F) a = Some b"
  shows "ufRan\<cdot>F = ubDom\<cdot>b"
    by (metis (no_types, lifting) Abs_cfun_inverse2 assms ranI someI_ex ufRan_def 
            ufun_ran2ufundom ufran_cont)

(* The range of an ufun is equal to the domain of f applied to the least ubundle with domain 
       ufDom f *)
lemma ufran_least: "ufRan\<cdot>f = ubDom\<cdot>((Rep_cufun f)\<rightharpoonup>(ubLeast (ufDom\<cdot>f)))"
  apply (simp add: ufRan_def)
  by (metis (no_types) domD option.sel ufunLeastIDom ufran_2_ubdom ufran_insert)

(*   *)
lemma ufran_2_ubdom2: assumes "ubDom\<cdot>tb = ufDom\<cdot>f"
  shows "ubDom\<cdot>((Rep_cufun f)\<rightharpoonup>tb) = ufRan\<cdot>f"
  by (metis rep_ufun_well assms domIff option.collapse ubdom_least_cs ufWell_def ufunLeastIDom ufran_2_ubdom)
    
    
  subsection \<open>ufLeast\<close>
(* ufLeast *)
  thm ufLeast_def

    
(* ufelast if a mono function  *)
lemma ufleast_mono[simp]: "\<And> cin cout. monofun (\<lambda>sb. (ubDom\<cdot>sb = cin)\<leadsto>ubLeast cout)"
  by simp

(* ufleast is a cont function *)
lemma ufleast_cont[simp]: "\<And> cin cout. cont (\<lambda>sb. (ubDom\<cdot>sb = cin)\<leadsto>ubLeast cout)"
  by simp

(* ufleast produce a ufwell function  *)
lemma ufleast_ufwell[simp]: "\<And> cin cout. ufWell (Abs_cfun (\<lambda>sb. (ubDom\<cdot>sb = cin)\<leadsto>ubLeast cout))"
  apply (simp add: ufWell_def, rule)
   apply (rule_tac x="cin" in exI, simp add: domIff)
  by (smt option.distinct(1) option.sel ran2exists ubdom_least_cs)

(* insert rule of ufleast *)
lemma ufleast_insert:"ufLeast In Out = Abs_ufun (Abs_cfun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>ubLeast Out))"
  by (simp add: ufLeast_def)

(* somwe how ufleast_ufran need this otherwise this cannt be proven with metis  *)
lemma ufleast_rep_abs[simp]: "(Rep_cufun (Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>ubLeast Out))) = (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>ubLeast Out)"
  by simp

(* ufdom of ufleast is the first argument  *)
lemma ufleast_ufdom: "ufDom\<cdot>(ufLeast In Out) = In"
  apply (simp add: ufLeast_def  ufdom_insert domIff)
  by (meson someI_ex ubdom_least_cs)

(* ufran of ufleast is its second argument *)
lemma ufleast_ufRan: "ufRan\<cdot>(ufLeast In Out) = Out"
  by (metis (no_types) option.sel ubdom_least_cs ufleast_insert ufleast_rep_abs ufleast_ufdom ufran_least)

(* ufleast can produce a function smaller or equal other function  *)
lemma ufleast_min: "(ufLeast (ufDom\<cdot>uf) (ufRan\<cdot>uf)) \<sqsubseteq> uf"
proof (rule ufun_belowI)
  show "ufDom\<cdot>(ufLeast (ufDom\<cdot>uf) (ufRan\<cdot>uf)) = UFun.ufDom\<cdot>uf"
    by (simp add: ufleast_ufdom)
next
  show "\<And>x. ubDom\<cdot>x = ufDom\<cdot>(ufLeast (ufDom\<cdot>uf) (ufRan\<cdot>uf)) \<Longrightarrow>
         Rep_cufun (ufLeast (ufDom\<cdot>uf) (ufRan\<cdot>uf))\<rightharpoonup>x \<sqsubseteq> Rep_cufun uf\<rightharpoonup>x"
    by (metis ufleast_rep_abs option.sel ubdom_least ufLeast_def ufleast_ufdom ufran_2_ubdom2)
qed


(* ufComp *)

  
subsection \<open>ufunType\<close>
(* ufunType *)

  
(* cont proof because ufdom and ufran are cont *)
lemma ufuntype_cont: "cont (\<lambda>f. (ufDom\<cdot>f, ufRan\<cdot>f))"
  by simp

(* insert rule for ufuntype *)
lemma ufuntype_insert: "ufunType\<cdot>f = (ufDom\<cdot>f, ufRan\<cdot>f)"
  by (simp add: ufunType_def)

(* ufunIO *)
 

end