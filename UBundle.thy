(*  Title:        UnivClasses
    Author:       Sebastian, Jens, Marc

    Description:  All "Universal Classes". Later used to define bundles/pfun 
*)

theory UBundle
  imports UnivClasses
begin

default_sort uscl

  
(****************************************************)
section\<open>Data type\<close>
(****************************************************)  
  
  
definition ubWell :: "(channel \<rightharpoonup> ('s::uscl)) \<Rightarrow> bool" where
"ubWell f \<equiv> \<forall>c \<in> (dom f). (usOkay c (f\<rightharpoonup>c))" 

lemma ubWell_empty: "ubWell empty"
  by(simp add: ubWell_def)

lemma ubWell_adm: "adm ubWell"
proof - 
  have "\<And>(Y :: nat \<Rightarrow> (channel \<Rightarrow> 'a option)). chain Y \<Longrightarrow> (\<forall>i. \<forall>c\<in>dom (Y i). usOkay c Y i\<rightharpoonup>c) \<longrightarrow> (\<forall>c\<in>dom (Lub Y). usOkay c Lub Y\<rightharpoonup>c)"  
  proof -
    fix Y :: "nat \<Rightarrow> (channel \<Rightarrow> 'a option)"
    assume f0: "chain Y"
    have f1: "\<forall>i. dom (Y i) = dom (Lub Y)"
      using f0 part_dom_lub by blast
    have f2: "\<And>c. c\<in>dom (Lub Y) \<Longrightarrow> (\<forall>i. usOkay c Y i\<rightharpoonup>c) \<longrightarrow> (usOkay c Lub Y\<rightharpoonup>c)"
    proof - 
      fix c
      assume "c\<in>dom (Lub Y)"
      show "(\<forall>i. usOkay c Y i\<rightharpoonup>c) \<longrightarrow> (usOkay c Lub Y\<rightharpoonup>c)"
        using usOkay_adm adm_def by (metis (mono_tags, lifting) f0 part_the_chain part_the_lub)
    qed
    show "(\<forall>i. \<forall>c\<in>dom (Y i). usOkay c Y i\<rightharpoonup>c) \<longrightarrow> (\<forall>c\<in>dom (Lub Y). usOkay c Lub Y\<rightharpoonup>c)"
      by (simp add: f1 f2)
  qed
  then show ?thesis
    by(simp add: adm_def ubWell_def)
qed

cpodef 's::uscl ubundle ("(_\<^sup>\<omega>)" [1000] 999) = "{b :: channel \<rightharpoonup> 's . ubWell b}"
  using ubWell_empty apply auto[1]
  using ubWell_adm by auto


setup_lifting type_definition_ubundle


(****************************************************)
section\<open>Definitions\<close>
(****************************************************)

(* ubDom *)
(* This function can be used in "'m stream USB" and "'m tstream USB" *)
(* and by the way, look at the "'m\<^sup>\<omega>" shorcode for 'm USB *)
definition ubDom :: "'m\<^sup>\<omega> \<rightarrow> channel set" where
"ubDom \<equiv> \<Lambda> b. dom (Rep_ubundle b)"

(* ubRestrict *)
definition ubRestrict:: "channel set \<Rightarrow> 'm ubundle \<rightarrow> 'm ubundle" where
"ubRestrict cs  \<equiv> \<Lambda> b. Abs_ubundle (Rep_ubundle b |` cs)"


(* ubGetCh *)
definition ubGetCh :: "channel \<Rightarrow> 'm ubundle \<rightarrow> 'm"  where
"ubGetCh c = (\<Lambda> b. ((Rep_ubundle b) \<rightharpoonup> c))"

(* ubLeast *)
definition ubLeast :: "channel set \<Rightarrow> 'm ubundle"  where
"ubLeast cs \<equiv> Abs_ubundle (\<lambda>c. (c \<in> cs) \<leadsto> \<bottom> )"

(* ubLen *)
(* Interesting function, uses the "len" operator over 'm *)
definition ubLen:: " 'm ubundle \<Rightarrow> lnat " where
"ubLen b \<equiv> if ubDom\<cdot>b \<noteq> {} then (LEAST ln. ln\<in>{(usLen\<cdot>(ubGetCh c\<cdot>b)) | c. c \<in> ubDom\<cdot>b}) else \<infinity>"  

(* ubShift *)
(* Thats an easy converter. For example from "tstream USB" to "stream USB" *)
(* Can also be cont *)
definition ubShift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ubundle \<Rightarrow> 'b ubundle" where
"ubShift f sb = Abs_ubundle (\<lambda>c. ((c\<in>ubDom\<cdot>sb) \<leadsto> f (ubGetCh c\<cdot>sb)))"

(* ubUnion *)

(* ubSetCh *)

(* ubRemCh *)

(* ubRenameCh *)

(* ubUp *)

(* ubEqSelected *)

(* ubEqCommon *)

(* ubPrefixSelected *)

(* ubPrefixCommon *)

(* ubMapStream *)


(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)
(* if ub is a chain then its unlifted functions are also a chain  *)
lemma rep_chain[simp]: assumes "chain S"
  shows "chain (\<lambda>n. Rep_ubundle (S n))"
  by (meson assms below_ubundle_def po_class.chain_def)

(* the lub of a channel in a chain is the same as when apply on each element of the chain  *)
lemma lub_eval: assumes "chain S"
  shows "the (Rep_ubundle (\<Squnion>i. S i) c) = (\<Squnion>j. the (Rep_ubundle (S j) c))"
  by (metis (mono_tags) Abs_ubundle_inverse Rep_ubundle adm_def assms lub_ubundle mem_Collect_eq part_the_lub rep_chain ubWell_adm)

  subsection \<open>ubDom\<close>
(* ubDom *)

thm ubDom_def
(*
definition ubDom :: "'m\<^sup>\<omega> \<rightarrow> channel set" where
"ubDom \<equiv> \<Lambda> b. dom (Rep_ubundle b)"
*)
(* the function udom is continuous *)
lemma ubDom_cont[simp]: "cont (\<lambda> ub. dom (Rep_ubundle ub))"
  by (smt Cont.contI2 below_ubundle_def is_ub_thelub monofunI not_below2not_eq part_dom_eq)

(* the dom of ub is the same as the dom of the unlifted ub *)
lemma ubDom_insert: "ubDom\<cdot>tb = dom (Rep_ubundle tb)"
  by (simp add: ubDom_def)

(* the dom of the ub is the same as the dom of the lifted function *)
lemma ubDom_rep_eq: "ubWell ub \<Longrightarrow> ubDom\<cdot>(Abs_ubundle ub) = dom ub"
  by (simp add: Abs_ubundle_inverse ubDom_insert)

(* if there is a relation between 2 ubs, they two have same dom  *)
lemma ubDom_below: assumes "ub1 \<sqsubseteq> ub2"
  shows "ubDom\<cdot>ub1 = ubDom\<cdot>ub2"
  by (metis assms below_ubundle_def part_dom_eq ubDom_insert)

(* all bundles in a chain have the same dom *)
lemma ubChain_dom_eq3: assumes "chain S"
  shows "ubDom\<cdot>(S i) = ubDom\<cdot>(S j)"
  using assms is_ub_thelub ubDom_below by blast
                      
(* all bundles in a chain have the same dom as the lub *)
lemma ubChain_dom_eq2[simp]: assumes "chain S"
  shows "ubDom\<cdot>(S i) = ubDom\<cdot>(\<Squnion>j. S j)"
  by (simp add: assms is_ub_thelub ubDom_below)

(* see ubChain_dom_eq2 *)
lemma ubDom_lub: assumes "chain Y" and "ubDom\<cdot>(Y i) = cs"
  shows "ubDom\<cdot>(\<Squnion> i. Y i) = cs"
  using assms(1) assms(2) by auto


  subsection \<open>ubGetCh\<close>
(* ubGetCh *)
thm ubGetCh_def
(* ubGetCh is cont *)
lemma ubGetCh_cont [simp]: "cont (\<lambda>ub. ((Rep_ubundle ub) \<rightharpoonup> c))"
  by (smt Prelude.contI2 below_ubundle_def fun_below_iff lub_eq lub_eval monofun_def not_below2not_eq op_the_mono)

(* the element in a channel is the same when it's lifted  *)
lemma ubGetCh_rep_eq: "ubWell ub \<Longrightarrow> ubGetCh c\<cdot>(Abs_ubundle ub) = ub \<rightharpoonup> c"
  by (simp add: Abs_ubundle_inverse ubGetCh_def)

(* the element in a channel is the same when unlifted  *)
lemma ubGetChE: assumes "c \<in> ubDom\<cdot>ub"
  shows "Some (ubGetCh c\<cdot>ub) = (Rep_ubundle ub) c"
  by (metis (full_types) Rep_ubundle Rep_ubundle_inverse assms domIff mem_Collect_eq option.exhaust_sel ubGetCh_rep_eq ubDom_insert)

(* the element in a channel of the lub is the same when applying ubGetCh on each ele  *)
lemma ubGetCh_lub: assumes "chain Y" and "c \<in> ubDom\<cdot>(\<Squnion> i. Y i)"
  shows "ubGetCh c\<cdot>(\<Squnion>i. Y i) = (\<Squnion>i. ubGetCh c\<cdot>(Y i))"
  using assms(1) contlub_cfun_arg by auto

(* the element in each channel has the same relation as its bundle  *)
lemma ubGetCh_below: assumes "x \<sqsubseteq> y"
  shows "\<forall> c. ubGetCh c\<cdot>x \<sqsubseteq> ubGetCh c\<cdot>y"
  by (simp add: assms monofun_cfun_arg)

(* the element in a channel is the same when it's unlifted  *)
lemma ubGetCh_insert: "ubGetCh c\<cdot>ub= (Rep_ubundle ub) \<rightharpoonup> c"
  by (simp add: ubGetCh_def)

(* induction rule for equal proof of two bundle  *)
lemma ubGetChI: assumes "ubDom\<cdot>x = ubDom\<cdot>y" and "\<And>c. c\<in>(ubDom\<cdot>x) \<Longrightarrow> ubGetCh c\<cdot>x = ubGetCh c\<cdot>y"
  shows "x = y"
  by (metis Rep_ubundle_inject assms(1) assms(2) part_eq ubDom_insert ubGetCh_insert)

(* id function *)
lemma [simp]: "Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>b)\<leadsto>ubGetCh c\<cdot>b) = b"
  apply (rule ubGetChI, subst ubDom_rep_eq)
    apply (smt Rep_ubundle domIff mem_Collect_eq ubGetChE ubWell_def)
   apply simp
  by (smt Abs_cfun_inverse2 Abs_ubundle_inverse Rep_ubundle domIff mem_Collect_eq option.sel ubDom_def ubGetChE ubWell_def ubDom_cont)



subsection \<open>ubLeast\<close>
(* ubLeast *)

  thm ubLeast_def

(* the optionLeast of the optionCpo is well-formed  *)
lemma ubleast_well: "ubWell (optionLeast cs)"
  by (simp add: ubWell_def usOkay_bot)

(* our definition of ubLeast is equal optionLeast  *)
lemma ubLeast_optionLeast_eq: "ubLeast cs = Abs_ubundle(optionLeast cs)"
  by (simp add: ubLeast_def optionLeast_def)
  
(* the dom of ubLeast is the same as the argument of the function  *)
lemma ubleast_ubDom [simp]: "ubDom\<cdot>(ubLeast cs) = cs"
  apply (simp add: ubDom_def)
  by (metis ubLeast_optionLeast_eq optionleast_dom ubDom_insert ubDom_rep_eq ubleast_well)

(* the element in each channel is the bottom element  *)
lemma ubLeast_getCh[simp]:  assumes "c \<in> cs"
  shows "ubGetCh c\<cdot>(ubLeast cs) = \<bottom>"
  by (simp add: assms ubGetCh_rep_eq ubLeast_optionLeast_eq ubleast_well)

(* the ubLeast bundle is the smallest bundle  *)
lemma tsbleast_below [simp]: assumes "cs = ubDom\<cdot>ub"
  shows "ubLeast cs \<sqsubseteq> ub"
  by (metis assms below_ubundle_def minimal part_below ubLeast_getCh ubDom_insert ubGetCh_insert ubleast_ubDom)

(* if ubLeast {} is in an chain, all elements are equal *)
lemma ubundle_allempty: assumes "chain Y" and "ubLeast {} \<in> range Y"
  shows "\<And>i. (Y i) = ubLeast {}"
  by (metis (no_types, lifting) Abs_cfun_inverse2 Rep_ubundle_inverse assms(1) assms(2) empty_iff f_inv_into_f 
        part_eq ubChain_dom_eq2 ubDom_def ubDom_cont ubleast_ubDom)



  subsection \<open>ubRestrict\<close>
(* ubRestrict *)
thm ubRestrict_def

(* the ubRestrict function returns a well-formed ubundle  *)
lemma ubRestrict_well [simp]: "ubWell (Rep_ubundle b |` cs)"
  by (metis (no_types, lifting) Rep_ubundle domIff mem_Collect_eq restrict_in restrict_out ubWell_def)

(* the ubRestrict function is monoton  *)
lemma ubRestrict_monofun[simp]: "monofun  (\<lambda>b. Rep_ubundle b |` cs)"
  by (metis (no_types, lifting) below_ubundle_def monofun_def part_restrict_monofun)

(* the ubRestrict function is continuous  part 1*)
lemma ubRestrict_cont1[simp]: "cont  (\<lambda>b. ((Rep_ubundle b) |` cs))"
  apply (rule contI2)
  apply simp
  by (smt Abs_ubundle_inverse Rep_ubundle adm_def below_option_def domIff fun_below_iff lub_eq lub_fun lub_ubundle mem_Collect_eq 
      part_dom_lub po_class.chain_def rep_chain restrict_map_def ubChain_dom_eq2 ubWell_adm)

(* the ubRestrict function is continuous *)
lemma ubRestrict_cont [simp]: "cont (\<lambda>b. Abs_ubundle (Rep_ubundle b |` cs))"
  by (simp add: cont_Abs_ubundle)

(*   *) 
lemma ubRestrict_insert : "ubRestrict cs\<cdot>tb = Abs_ubundle (Rep_ubundle tb |` cs)"
  by (simp add: ubRestrict_def)

(*   *)
lemma ubRestrict_rep_eq : "ubWell tb \<Longrightarrow> ubRestrict cs\<cdot>(Abs_ubundle tb) = Abs_ubundle (tb |` cs)"
  by (simp add: Abs_ubundle_inverse ubRestrict_insert)

(* the dom of the bundle after restrict its channel is a subset (or equal) its argument*)
lemma ubRestrict_dom [simp]: "ubDom\<cdot>(ubRestrict cs\<cdot>tb) \<subseteq> cs"
  by (simp add: ubDom_rep_eq ubRestrict_insert)

(* the dom of the bundle after restrict its channel is the conjunction of dom ub and first argument*)
lemma ubRestrict_dom2 [simp]: "ubDom\<cdot>(ubRestrict cs\<cdot>ub) = ubDom\<cdot>ub \<inter> cs"
  by (metis dom_restrict ubDom_insert ubDom_rep_eq ubRestrict_insert ubRestrict_well)


(* applying 2 times ubRestriction on a ubundle is eq the application of the function with the union of both channel set as argument  *)
lemma ubRestrict_twice [simp]: "ubRestrict cs2\<cdot>(ubRestrict cs1\<cdot>ub) = ubRestrict (cs1\<inter>cs2)\<cdot>ub"
  by (metis restrict_restrict ubRestrict_insert ubRestrict_rep_eq ubRestrict_well)

(* the element in the channel after restriction is equal the unrestrict bundle *)
lemma ubGetCh_restrict [simp]: assumes "c \<in> cs"
  shows "ubGetCh c\<cdot>(ubRestrict cs\<cdot>ub) = ubGetCh c\<cdot>ub"
  by (metis (no_types, lifting) Abs_cfun_inverse2 assms restrict_in ubGetCh_def ubGetCh_cont ubGetCh_rep_eq ubRestrict_insert ubRestrict_well)

(* the bundles after applying ubRestrict have the same below relation like its second  *)
lemma ubRestrict_belowI1: assumes "(a \<sqsubseteq> b)"
  shows "ubRestrict cs\<cdot>a \<sqsubseteq> ubRestrict cs\<cdot>b"
  using assms monofun_cfun_arg by auto

(* if an empty channel set is the first argument, then ubRestrict return the ubLeast with empty channel set  *)
lemma ubRestrict_least [simp]: "ubRestrict {}\<cdot>ub = ubLeast {}"
  by (metis Rep_ubundle_inverse empty_iff empty_subsetI optionleast_dom part_eq subset_antisym ubLeast_optionLeast_eq ubDom_insert ubRestrict_dom)

(* if the first argument disjoint with the domain of the bundle then the function return ubLeast with an empty channel set *)
lemma ubRestrict_least2[simp]: assumes "cs \<inter> ubDom\<cdot>ub = {}" 
  shows "ubRestrict cs\<cdot>ub = ubLeast {}"
  by (metis Int_commute Int_empty_right assms dom_restrict ex_in_conv part_eq ubDom_insert ubRestrict_insert ubRestrict_least)


lemma ubRestrict_id [simp]: assumes "ubDom\<cdot>ub \<subseteq> cs" shows "ubRestrict cs\<cdot>ub = ub"
  by (metis (mono_tags, lifting) assms contra_subsetD inf.absorb_iff1 ubGetChI ubGetCh_restrict ubRestrict_dom2)



  subsection \<open>ubLen\<close>
(* ubLen *) 
  thm ubLen_def


  subsection \<open>ubShift\<close>
(* ubShift *) 
  thm ubShift_def
(*
definition ubShift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ubundle \<Rightarrow> 'b ubundle" where
"ubShift f sb = Abs_ubundle (\<lambda>c. ((c\<in>ubDom\<cdot>sb) \<leadsto> f (ubGetCh c\<cdot>sb)))"
*)

  
(* ubUnion *)

(* ubSetCh *)

(* ubRemCh *)

(* ubRenameCh *)

(* ubUp *)

(* ubEqSelected *)

(* ubEqCommon *)

(* ubPrefixSelected *)

(* ubPrefixCommon *)

(* ubMapStream *)
  
  
end