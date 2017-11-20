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
text {* @{text "ubDom"} returns the domain of the given bundle *}
(* This function can be used in "'m stream USB" and "'m tstream USB" *)
(* and by the way, look at the "'m\<^sup>\<omega>" shorcode for 'm USB *)
definition ubDom :: "'m\<^sup>\<omega> \<rightarrow> channel set" where
"ubDom \<equiv> \<Lambda> b. dom (Rep_ubundle b)"

(* ubRestrict *)
text {* @{text "ubRestrict"} creates a new bundle with the restricted channel set *}
definition ubRestrict:: "channel set \<Rightarrow> 'm ubundle \<rightarrow> 'm ubundle" where
"ubRestrict cs  \<equiv> \<Lambda> b. Abs_ubundle (Rep_ubundle b |` cs)"

abbreviation ubRestrict_abbr :: "'m ubundle \<Rightarrow> channel set \<Rightarrow> 'm ubundle" (infix "\<bar>" 65) where 
"b \<bar> cs \<equiv> ubRestrict cs\<cdot>b"


(* ubGetCh *)
text {* @{text "ubGetCh"} returns the element of a given channel  *}
definition ubGetCh :: "channel \<Rightarrow> 'm ubundle \<rightarrow> 'm"  where
"ubGetCh c = (\<Lambda> b. ((Rep_ubundle b) \<rightharpoonup> c))"

abbreviation ubGetCh_abbr :: "'m ubundle \<Rightarrow> channel \<Rightarrow> 'm" (infix " . " 65) where 
"b . c \<equiv> ubGetCh c\<cdot>b"


(* ubLeast *)
text {* @{text "ubLeast"} creates a bundle with \<bottom> in each channel  *}
definition ubLeast :: "channel set \<Rightarrow> 'm ubundle"  where
"ubLeast cs \<equiv> Abs_ubundle (\<lambda>c. (c \<in> cs) \<leadsto> \<bottom> )"


(* ubLen *)
(* Interesting function, uses the "len" operator over 'm *)
definition ubLen:: " 'm ubundle \<Rightarrow> lnat " where
"ubLen b \<equiv> if ubDom\<cdot>b \<noteq> {} then (LEAST ln. ln\<in>{(usLen\<cdot>(b . c)) | c. c \<in> ubDom\<cdot>b}) else \<infinity>"  


(* ubShift *)
text {* @{text "ubShift"}  the channel-domains are merged . Thats an easy converter. For example from "tstream USB" to "stream USB" *}
(* Can also be cont *)
definition ubShift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ubundle \<Rightarrow> 'b ubundle" where
"ubShift f ub = Abs_ubundle (\<lambda>c. ((c\<in>ubDom\<cdot>ub) \<leadsto> f (ub . c)))"


(* ubUnion *)
text {* @{text "ubUnion"}  the channel-domains are merged *}
definition ubUnion :: "'m ubundle \<rightarrow> 'm ubundle \<rightarrow> 'm ubundle"  where 
"ubUnion \<equiv> \<Lambda> ub1 ub2 . Abs_ubundle ((Rep_ubundle ub1) ++ (Rep_ubundle ub2))"


(* ubSetCh *)
text {* @{text "ubSetCh"} adds a channel or ubReplaces its content *}
definition ubSetCh :: "'m ubundle \<rightarrow> channel \<Rightarrow> 'm  \<Rightarrow> 'm ubundle" where
"ubSetCh \<equiv> \<Lambda> ub. (\<lambda> c m. ubUnion\<cdot>ub\<cdot>(Abs_ubundle([c \<mapsto> m])))"


(* ubRemCh *)
text {* @{text "ubRemCh"} removes a channel from a timed stream bundle *}
abbreviation ubRemCh :: "channel \<Rightarrow> 'm ubundle  \<rightarrow> 'm ubundle" where
"ubRemCh \<equiv> \<lambda> c. \<Lambda> b. ubRestrict (-{c})\<cdot>b"


(* ubRenameCh *)
text {* @{text "ubRenameCh"} renames a channel  in a bundle *}
definition ubRenameCh :: "'m ubundle \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> 'm ubundle" where
 "ubRenameCh b ch1 ch2 \<equiv> (ubSetCh\<cdot>(ubRemCh ch1\<cdot>b)) ch2 (b . ch1)"


(* ubUp *)
text {* @{text "ubUp"}  replaces all "None" channels with \<bottom>. *}
definition ubUp:: " 'm ubundle \<rightarrow> 'm ubundle"  where
"ubUp \<equiv> \<Lambda> b . Abs_ubundle (\<lambda>c. if (c \<in> ubDom\<cdot>b) then (Rep_ubundle b) c else Some \<bottom>)"


(* ubEqSelected *)
text {* @{text "ubEqSelected"} equality on specific channels *}
definition ubEqSelected:: " channel set \<Rightarrow> 'm ubundle => 'm ubundle => bool" where
"ubEqSelected cs b1 b2 \<equiv>  (b1\<bar>cs) = (b2\<bar>cs)"


(* ubEqCommon *)
text {* @{text "ubEqCommon"} equality on common channels *}
definition ubEqCommon:: " 'm ubundle => 'm ubundle => bool" where
"ubEqCommon b1 b2\<equiv> ubEqSelected (ubDom\<cdot>b1 \<inter> ubDom\<cdot>b2) b1 b2"


(* ubPrefixSelected *)
text {* @{text " ubPrefixSelected"} prefix relation on selected channels *}
definition ubPrefixSelected:: "channel set \<Rightarrow> 'm ubundle \<Rightarrow> 'm ubundle \<Rightarrow> bool" where
"ubPrefixSelected cs b1 b2 \<equiv> (b1\<bar>cs \<sqsubseteq> b2\<bar>cs)"

(* ubPrefixCommon *)

(* ubMapStream *)


(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)

subsection \<open>General Lemmas\<close>

(*Streambundles are sb_well by definition*)
theorem ubRep_well[simp]: "ubWell (Rep_ubundle x)"
  using Rep_ubundle by auto

(*Rep und Abs - Theorems*)
theorem ubRep_ubAbs[simp]: assumes "ubWell f" shows "Rep_ubundle (Abs_ubundle f) = f"
  by (simp add: Abs_ubundle_inverse assms)

theorem ubAbs_ubReps[simp]: shows "Abs_ubundle (Rep_ubundle f) = f"
  by (simp add: Rep_ubundle_inverse)


(* a chain of 'm SBs is also a chain after applying Rep_ubundle *)
lemma ubRep_chain[simp]: assumes "chain S"
  shows "chain (\<lambda>n. Rep_ubundle (S n))"
  by (meson assms below_ubundle_def po_class.chain_def)


lemma ubRep_chain_the[simp]: assumes "chain S" 
  shows "chain (\<lambda>n. the (Rep_ubundle (S n) c))"
  by (metis assms below_ubundle_def fun_belowD monofun_def op_the_mono po_class.chain_def)


(* the lub of a chain after applying rep on each element is also ubWell  *)
lemma ubWell_lub[simp]: assumes "chain S"
  shows "ubWell (\<Squnion>n. Rep_ubundle (S n))"
  by (metis adm_def assms lub_eq ubRep_chain ubRep_well ubWell_adm)


(*   *)
lemma ubRep_lub:assumes "chain Y"
  shows "(\<Squnion>i. Rep_ubundle (Y i)) = Rep_ubundle (\<Squnion>i.  Y i)"
  using assms lub_ubundle by fastforce


(*  *)
lemma ubRep_cont [simp]: "cont Rep_ubundle"
  by (smt Abs_ubundle_inject Cont.contI2 Rep_ubundle Rep_ubundle_inverse adm_def below_ubundle_def 
      lub_eq lub_ubundle mem_Collect_eq monofunI po_eq_conv ubWell_adm)


(*   *)
lemma ubRep_up_lub[simp]: assumes "chain Y"
  shows "range (\<lambda>n. the (Rep_ubundle (Y n) c)) <<| the (\<Squnion>n. Rep_ubundle (Y n) c)"
  by (metis assms cpo_lubI lub_fun part_the_lub ubRep_chain ubRep_chain_the)


(* Equivalence of evaluation of 'm ubundle based on lub of function values. *)
lemma ubRep_lub_eval: assumes "chain S" 
  shows "the (Rep_ubundle (\<Squnion>i. S i) c) = (\<Squnion>j. the (Rep_ubundle (S j) c))"
using assms part_the_lub ubRep_chain ubRep_lub by fastforce


(*   *)
lemma ubRep_chain_lub_dom_eq: assumes "chain S" 
  shows "dom (Rep_ubundle (S i)) = dom (Rep_ubundle (\<Squnion>i. S i))"
  by (meson assms below_ubundle_def is_ub_thelub part_dom_eq)


(*   *)
lemma ubRep_LessI: assumes "dom (Rep_ubundle b1) = dom (Rep_ubundle b2)" 
    and "\<And>c. c\<in>dom (Rep_ubundle b1) \<Longrightarrow>  the ((Rep_ubundle b1) c) \<sqsubseteq> the ((Rep_ubundle b2) c)"
  shows "b1 \<sqsubseteq> b2"
  by (meson assms(1) assms(2) below_ubundle_def part_below)


(*   *)
lemma ubRep_Less_Lub1: assumes "chain S" 
  shows "the (Rep_ubundle (S i) c) \<sqsubseteq> the (Rep_ubundle (\<Squnion>i. S i) c)"
  by (metis assms(1) is_ub_thelub ubRep_chain_the ubRep_lub_eval)


(*   *)
lemma ubRep_Less_Lub2: assumes "chain S"  and "range S <| u"
  shows "the (Rep_ubundle (\<Squnion>i. S i) c) \<sqsubseteq> the (Rep_ubundle u c)"
  by (metis assms(1) assms(2) below_option_def below_refl below_ubundle_def fun_below_iff is_lub_thelub)

(* if the function is ubWell then each element in the stream is usOkay  *)
lemma [simp]: assumes "ubWell f" and "c \<in> dom f"
  shows "usOkay c (f\<rightharpoonup>c)"
  using assms(1) assms(2) ubWell_def by auto


(* if each element in the stream is usOkay then the function is ubWell  *)
lemma ubWellI: assumes "\<And> c. c \<in> dom f \<Longrightarrow> usOkay c (f\<rightharpoonup>c)"
  shows "ubWell f"
  using assms ubWell_def by blast


  subsection \<open>ubDom\<close>
(* ubDom *)

  thm ubDom_def

(* the function udom is continuous *)
lemma ubDom_cont[simp]: "cont (\<lambda> ub. dom (Rep_ubundle ub))"
  by (smt Cont.contI2 below_ubundle_def is_ub_thelub monofunI not_below2not_eq part_dom_eq)

(* the dom of ub is the same as the dom of the unlifted ub *)
lemma ubDom_insert: "ubDom\<cdot>tb = dom (Rep_ubundle tb)"
  by (simp add: ubDom_def)

(* the dom of the ub is the same as the dom of the lifted function *)
lemma ubDom_ubRep_eq: "ubWell ub \<Longrightarrow> ubDom\<cdot>(Abs_ubundle ub) = dom ub"
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


lemma ubDom_channel_usOkay[simp]: assumes "c \<in> ubDom\<cdot>ub"
  shows "usOkay c ((Rep_ubundle ub)\<rightharpoonup>c)"
  using assms ubRep_well ubDom_insert ubWell_def by blast


  subsection \<open>ubGetCh\<close>
(* ubGetCh *)
  thm ubGetCh_def


(* ubGetCh is cont *)
lemma ubGetCh_cont [simp]: "cont (\<lambda>ub. ((Rep_ubundle ub) \<rightharpoonup> c))"
  by (smt Prelude.contI2 below_ubundle_def fun_below_iff lub_eq ubRep_lub_eval monofun_def not_below2not_eq op_the_mono)

(* the element in a channel is the same when it's lifted  *)
lemma ubGetCh_ubRep_eq: "ubWell ub \<Longrightarrow> (Abs_ubundle ub) . c= ub \<rightharpoonup> c"
  by (simp add: Abs_ubundle_inverse ubGetCh_def)

(* the element in a channel is the same when unlifted  *)
lemma ubGetChE: assumes "c \<in> ubDom\<cdot>ub"
  shows "Some (ub . c) = (Rep_ubundle ub) c"
  by (metis (full_types) Rep_ubundle Rep_ubundle_inverse assms domIff mem_Collect_eq option.exhaust_sel ubGetCh_ubRep_eq ubDom_insert)

(* the element in a channel of the lub is the same when applying ubGetCh on each ele  *)
lemma ubGetCh_lub: assumes "chain Y" and "c \<in> ubDom\<cdot>(\<Squnion> i. Y i)"
  shows "(\<Squnion>i. Y i) . c = (\<Squnion>i. (Y i) . c)"
  using assms(1) contlub_cfun_arg by auto

(* the element in each channel has the same relation as its bundle  *)
lemma ubGetCh_below: assumes "x \<sqsubseteq> y"
  shows "\<forall> c. x . c \<sqsubseteq> y . c"
  by (simp add: assms monofun_cfun_arg)

(* the element in a channel is the same when it's unlifted  *)
lemma ubGetCh_insert: "ub . c = (Rep_ubundle ub) \<rightharpoonup> c"
  by (simp add: ubGetCh_def)

(* induction rule for equal proof of two bundle  *)
lemma ubGetChI: assumes "ubDom\<cdot>x = ubDom\<cdot>y" and "\<And>c. c\<in>(ubDom\<cdot>x) \<Longrightarrow> x . c = y . c"
  shows "x = y"
  by (metis Rep_ubundle_inject assms(1) assms(2) part_eq ubDom_insert ubGetCh_insert)

(* id function *)
lemma [simp]: "Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>b)\<leadsto> b . c) = b"
  apply (rule ubGetChI, subst ubDom_ubRep_eq)
    apply (smt Rep_ubundle domIff mem_Collect_eq ubGetChE ubWell_def)
   apply simp
  by (smt Abs_cfun_inverse2 Abs_ubundle_inverse Rep_ubundle domIff mem_Collect_eq option.sel ubDom_def ubGetChE ubWell_def ubDom_cont)

  subsection \<open>eq/below\<close>

(* one bundle is below an other if they have the same domain and the below relation is the same on each channel  *)
lemma ub_below: assumes "ubDom\<cdot>x = ubDom\<cdot>y" and "\<And> c. c \<in> ubDom\<cdot>x \<Longrightarrow> x . c \<sqsubseteq> y . c"
  shows "x \<sqsubseteq> y"
  by (metis assms(1) assms(2) ubDom_insert ubGetCh_insert ubRep_LessI)

(* one bundle is eq an other if the have the same domain and element in each channel is eq on *)
lemma ub_eq: assumes "ubDom\<cdot>x = ubDom\<cdot>y" and "\<And> c. c\<in>ubDom\<cdot>x \<Longrightarrow> x . c =y . c"
  shows "x=y"
  using assms(1) assms(2) ubGetChI by blast


subsection \<open>ubLeast\<close>
(* ubLeast *)

  thm ubLeast_def

(* the optionLeast of the optionCpo is well-formed  *)
lemma ubLeast_well: "ubWell (optionLeast cs)"
  by (simp add: ubWell_def usOkay_bot)

(* our definition of ubLeast is equal optionLeast  *)
lemma ubLeast_optionLeast_eq: "ubLeast cs = Abs_ubundle(optionLeast cs)"
  by (simp add: ubLeast_def optionLeast_def)
  
(* the dom of ubLeast is the same as the argument of the function  *)
lemma ubLeast_ubDom [simp]: "ubDom\<cdot>(ubLeast cs) = cs"
  apply (simp add: ubDom_def)
  by (metis ubLeast_optionLeast_eq optionleast_dom ubDom_insert ubDom_ubRep_eq ubLeast_well)

(* the element in each channel is the bottom element  *)
lemma ubLeast_getCh[simp]:  assumes "c \<in> cs"
  shows "(ubLeast cs) . c = \<bottom>"
  by (simp add: assms ubGetCh_ubRep_eq ubLeast_optionLeast_eq ubLeast_well)

(* the ubLeast bundle is the smallest bundle  *)
lemma ubLeast_below [simp]: assumes "cs = ubDom\<cdot>ub"
  shows "ubLeast cs \<sqsubseteq> ub"
  by (metis assms below_ubundle_def minimal part_below ubLeast_getCh ubDom_insert ubGetCh_insert ubLeast_ubDom)

(* if ubLeast {} is in an chain, all elements are equal *)
lemma ubundle_allempty: assumes "chain Y" and "ubLeast {} \<in> range Y"
  shows "\<And>i. (Y i) = ubLeast {}"
  by (metis (no_types, lifting) Abs_cfun_inverse2 Rep_ubundle_inverse assms(1) assms(2) empty_iff f_inv_into_f 
        part_eq ubChain_dom_eq2 ubDom_def ubDom_cont ubLeast_ubDom)


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
      part_dom_lub po_class.chain_def ubRep_chain restrict_map_def ubChain_dom_eq2 ubWell_adm)

(* the ubRestrict function is continuous *)
lemma ubRestrict_cont [simp]: "cont (\<lambda>b. Abs_ubundle (Rep_ubundle b |` cs))"
  by (simp add: cont_Abs_ubundle)

(*   *) 
lemma ubRestrict_insert : "ubRestrict cs\<cdot>tb = Abs_ubundle (Rep_ubundle tb |` cs)"
  by (simp add: ubRestrict_def)

(*   *)
lemma ubRestrict_ubRep_eq : "ubWell tb \<Longrightarrow> ubRestrict cs\<cdot>(Abs_ubundle tb) = Abs_ubundle (tb |` cs)"
  by (simp add: Abs_ubundle_inverse ubRestrict_insert)

(* the dom of the bundle after restrict its channel is a subset (or equal) its argument*)
lemma ubRestrict_dom [simp]: "ubDom\<cdot>(ubRestrict cs\<cdot>tb) \<subseteq> cs"
  by (simp add: ubDom_ubRep_eq ubRestrict_insert)

(* the dom of the bundle after restrict its channel is the conjunction of dom ub and first argument*)
lemma ubRestrict_dom2 [simp]: "ubDom\<cdot>(ubRestrict cs\<cdot>ub) = ubDom\<cdot>ub \<inter> cs"
  by (metis dom_restrict ubDom_insert ubDom_ubRep_eq ubRestrict_insert ubRestrict_well)

(* applying 2 times ubRestriction on a ubundle is eq the application of the function with the union of both channel set as argument  *)
lemma ubRestrict_twice [simp]: "ubRestrict cs2\<cdot>(ubRestrict cs1\<cdot>ub) = ubRestrict (cs1\<inter>cs2)\<cdot>ub"
  by (metis restrict_restrict ubRestrict_insert ubRestrict_ubRep_eq ubRestrict_well)

(* the element in the channel after restriction is equal the unrestrict bundle *)
lemma ubGetCh_ubRestrict [simp]: assumes "c \<in> cs"
  shows "(ubRestrict cs\<cdot>ub) . c= ub . c "
  by (metis (no_types, lifting) Abs_cfun_inverse2 assms restrict_in ubGetCh_def ubGetCh_cont ubGetCh_ubRep_eq ubRestrict_insert ubRestrict_well)

(* the bundles after applying ubRestrict have the same below relation like its second  *)
lemma ubRestrict_belowI1: assumes "(a \<sqsubseteq> b)"
  shows "ubRestrict cs\<cdot>a \<sqsubseteq> ubRestrict cs\<cdot>b"
  using assms monofun_cfun_arg by auto

(* if an empty channel set is the first argument, then ubRestrict return the ubLeast with empty channel set  *)
lemma ubRestrict_ubLeast [simp]: "ubRestrict {}\<cdot>ub = ubLeast {}"
  by (metis Rep_ubundle_inverse empty_iff empty_subsetI optionleast_dom part_eq subset_antisym ubLeast_optionLeast_eq ubDom_insert ubRestrict_dom)

(* if the first argument disjoint with the domain of the bundle then the function return ubLeast with an empty channel set *)
lemma ubRestrict_ubLeast2[simp]: assumes "cs \<inter> ubDom\<cdot>ub = {}" 
  shows "ubRestrict cs\<cdot>ub = ubLeast {}"
  by (metis Int_commute Int_empty_right assms dom_restrict ex_in_conv part_eq ubDom_insert ubRestrict_insert ubRestrict_ubLeast)


lemma ubRestrict_id [simp]: assumes "ubDom\<cdot>ub \<subseteq> cs" shows "ubRestrict cs\<cdot>ub = ub"
  by (metis (mono_tags, lifting) assms contra_subsetD inf.absorb_iff1 ubGetChI ubGetCh_ubRestrict ubRestrict_dom2)



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

  
  subsection \<open>ubUnion\<close>
(* ubUnion *)
  thm ubUnion_def

lemma ubUnion_well[simp]: assumes "ubWell b1" and "ubWell b2"
  shows "ubWell (b1 ++ b2)"
  by (metis assms(1) assms(2) domIff mapadd2if_then ubWell_def)

(* helper function for continuity proof *)
lemma ubUnion_contL [simp]: "cont (\<lambda>b1. (Rep_ubundle b1) ++ (Rep_ubundle b2))"
  using cont_compose part_add_contL ubRep_cont by blast

(* helper function for continuity proof *)
lemma ubUnion_contR [simp]: "cont (\<lambda>b2. (Rep_ubundle b1) ++ (Rep_ubundle b2))"
using cont_compose part_add_contR ubRep_cont by blast

(* sbUnion is an coninuous function *)
lemma ubUnion_cont [simp]: "cont (\<lambda> b1. \<Lambda> b2.(Abs_ubundle (Rep_ubundle b1 ++ Rep_ubundle b2)))"
  apply (rule cont2cont_LAM)
  apply (metis (mono_tags) Rep_ubundle cont_Abs_ubundle mem_Collect_eq ubUnion_contR ubUnion_well)
  by (metis (mono_tags) Rep_ubundle cont_Abs_ubundle mem_Collect_eq ubUnion_contL ubUnion_well)

    
(* insert rule for sbUnion *)
lemma ubUnion_insert: "ubUnion\<cdot>ub1\<cdot>ub2 = (Abs_ubundle (Rep_ubundle ub1 ++ Rep_ubundle ub2))"
  apply (simp add: ubUnion_def)
  using ubUnion_contR ubUnion_contL ubUnion_cont 
  by (simp add: cont_Abs_ubundle)

(* if all channels in b1 are also in b2 the union produces b2 *)
lemma ubUnion_idL [simp]: assumes "ubDom\<cdot>ub1 \<subseteq> ubDom\<cdot>ub2" shows "ubUnion\<cdot>ub1\<cdot>ub2 = ub2"
  using ubUnion_insert ubDom_insert  
  by (metis Rep_ubundle_inverse assms part_add_id)


lemma ubUnion_idR [simp]: "ubUnion\<cdot>ub\<cdot>(ubLeast {}) = ub"
  by (simp add: Rep_ubundle_inverse map_add_comm ubLeast_optionLeast_eq ubUnion_insert ubLeast_well)


(* if b1 and b2 have no common channels, sbUnion is commutative *)
lemma ubUnion_commutative: assumes "ubDom\<cdot>ub1 \<inter> ubDom\<cdot>ub2 = {}"
  shows "ubUnion\<cdot>ub1\<cdot>ub2 = ubUnion\<cdot>ub2\<cdot>ub1"
  apply(simp add: ubUnion_insert)
  by (metis assms map_add_comm ubDom_insert)


lemma ubUnion_asso: "ubUnion\<cdot>ub1\<cdot>(ubUnion\<cdot>ub2\<cdot>ub3) = ubUnion\<cdot>(ubUnion\<cdot>ub1\<cdot>ub2)\<cdot>ub3"
  by (simp add: ubUnion_insert)

(* the second argument has priority in sbUnion *)
lemma ubUnion_ubGetchR [simp]: assumes "c \<in> ubDom\<cdot>ub2"
  shows "ubUnion\<cdot>ub1\<cdot>ub2  .  c = ub2  .  c"
  by (metis assms map_add_dom_app_simps(1) ubRep_well ubDom_insert ubGetCh_insert ubGetCh_ubRep_eq ubUnion_insert ubUnion_well)


lemma ubUnion_ubGetchL [simp]: assumes "c \<notin> ubDom\<cdot>ub2"
  shows "ubUnion\<cdot>ub1\<cdot>ub2   .  c = ub1  .  c"
  by (metis assms domIff mapadd2if_then ubRep_ubAbs ubRep_well ubDom_insert ubGetCh_insert ubUnion_insert ubUnion_well)

lemma ubUnion_ubRestrict3 [simp]: assumes "(ubDom\<cdot>ub1)\<inter>(ubDom\<cdot>ub2) = {}" 
  shows "ubRestrict (ubDom\<cdot>ub1)\<cdot>(ubUnion\<cdot>ub1\<cdot>ub2) = ub1"
  apply(simp add: ubUnion_insert ubDom_insert)
  by (metis Rep_ubundle_inverse assms map_add_comm map_union_restrict2 ubRep_well ubDom_insert ubRestrict_ubRep_eq ubUnion_well)


lemma ubUnion_ubRestrict2 [simp]:"ubRestrict (ubDom\<cdot>ub2)\<cdot>(ubUnion\<cdot>ub1\<cdot>ub2) = ub2"
  by (simp add: Rep_ubundle_inverse ubDom_def ubRestrict_insert ubUnion_insert)


lemma ubUnion_ubRestrict [simp]: assumes "(ubDom\<cdot>ub2) \<inter> cs = {}" 
  shows "ubRestrict cs\<cdot>(ubUnion\<cdot>ub1\<cdot>ub2) = ubRestrict cs\<cdot>ub1"
  using assms by (simp add: ubUnion_insert ubRestrict_insert ubDom_def)


lemma ubUnion_ubRestrict4: "ubRestrict cs\<cdot>(ubUnion\<cdot>ub1\<cdot>ub2) = ubUnion\<cdot>(ubRestrict cs\<cdot>ub1)\<cdot>(ubRestrict cs\<cdot>ub2)"
  apply (simp add: ubRestrict_insert ubUnion_insert)
  by (metis mapadd2if_then restrict_map_def)
    

lemma ubUnion_dom [simp]: "ubDom\<cdot>(ubUnion\<cdot>ub1\<cdot>ub2) = ubDom\<cdot>ub1 \<union> ubDom\<cdot>ub2"
  by (simp add: ubDom_insert ubUnion_insert Un_commute) 


lemma ubUnion_belowI1: assumes "(ub1 \<sqsubseteq> ub2)" and "(ub3 \<sqsubseteq> ub4)"
  shows "ubUnion\<cdot>ub1\<cdot>ub3 \<sqsubseteq> ubUnion\<cdot>ub2\<cdot>ub4"
  by (simp add: assms(1) assms(2) monofun_cfun)


  subsection \<open>ubSetCh\<close>
(* ubSetCh *)
  thm ubSetCh_def


lemma ubSetCh_cont [simp]: "cont (\<lambda> ub. (\<lambda>c m. ubUnion\<cdot>ub\<cdot>(Abs_ubundle [c \<mapsto> m])))"
  by simp


lemma ubSetCh_well [simp]: assumes "usOkay c s"
  shows "ubWell ((Rep_ubundle b) (c \<mapsto> s) )"
  by (metis assms dom_fun_upd fun_upd_apply insert_iff option.sel option.simps(3) ubRep_well ubWell_def)
    
    
(* insertion lemma for tsbSetCh *)
lemma ubSetCh_insert: assumes "usOkay c s"
  shows "(ubSetCh\<cdot>b) c s = ubUnion\<cdot>b\<cdot>(Abs_ubundle [c \<mapsto> s])"
  by (simp add: ubSetCh_def)
    
  subsection \<open>ubRemCh\<close>
(* ubRemCh *)


lemma ubRemCh_insert: "ubRemCh c\<cdot>b =  b \<bar> -{c}"
  by simp

lemma ubRemCh_dom [simp]: "ubDom\<cdot>(ubRemCh c\<cdot>b) = ubDom\<cdot>b - {c}"
  by auto
    
lemma ubRemCh2restrict: "ubRemCh c\<cdot>b = ubRestrict (ubDom\<cdot>b - {c})\<cdot>b"
  by (metis (no_types, lifting) diff_eq eta_cfun subset_iff ubRestrict_id ubRestrict_twice)


  subsection \<open>ubRenameCh\<close>
(* ubRenameCh *)
  thm ubRenameCh_def
(* a bundle with only one channel based on other bundel is ubWell  *)
lemma ubWell_single_channel: assumes "c \<in> ubDom\<cdot>tb" shows "ubWell [c \<mapsto> Rep_ubundle tb\<rightharpoonup>c]"
  by (metis (full_types) assms ubRep_ubAbs ubSetCh_well ubDom_channel_usOkay ubWell_empty)

(* change a channel to itself returns the same bundle  *)
lemma ubRenameCh_id: assumes "c \<in> ubDom\<cdot>tb"
  shows "ubRenameCh tb c c = tb"
  apply (simp add: ubRenameCh_def ubGetCh_insert ubSetCh_def ubRemCh_insert ubRestrict_insert)
  by (smt assms compl_inf_bot dom_empty dom_fun_upd fun_upd_triv fun_upd_upd map_add_upd option.discI ubRep_ubAbs restrict_complement_singleton_eq ubDom_ubRep_eq ubGetChE ubGetCh_insert 
      ubRestrict_insert ubRestrict_ubLeast2 ubRestrict_well ubUnion_insert ubUnion_well ubWell_single_channel ubUnion_idR)

(* the dom of new bundle after renaming a channel is the union between new channel and the dom of bundle without the renamed channel  *)
lemma ubRenameCh_ubDom: assumes "ch1 \<in> ubDom\<cdot>tb"  and "usOkay ch2 (tb . ch1)"
  shows "ubDom\<cdot>(ubRenameCh tb ch1 ch2) = (ubDom\<cdot>tb - {ch1}) \<union> {ch2}"
  apply (simp add: ubRenameCh_def  ubSetCh_def)
  by (metis assms(2) diff_eq dom_empty dom_fun_upd insert_is_Un option.simps(3) ubRep_ubAbs sup_commute ubSetCh_well ubDom_ubRep_eq ubWell_empty)
  
(* after renaming channel ch1 to ch2, old and new bundles have the same element on those channel  *)  
lemma ubRenameCh_ubGetChI1: assumes "ch1 \<in> ubDom\<cdot>tb" 
                    and "usOkay ch2 (tb . ch1)"
  shows "(ubRenameCh tb ch1 ch2) . ch2 = tb . ch1"
  apply (simp add: ubRenameCh_def  ubSetCh_def)
  apply (subst ubUnion_ubGetchR)
  apply (metis assms(2) dom_empty dom_fun_upd option.simps(3) ubRep_ubAbs singletonI ubSetCh_well ubDom_ubRep_eq ubWell_empty)
  by (metis assms(1) assms(2) fun_upd_same ubRep_ubAbs ubSetCh_well ubGetChE ubGetCh_insert ubWell_empty)

(* renaming channel doesnt effect other channel in a bundle  *)           
lemma ubRenameCh_ubGetChI2: assumes "ch1 \<in> ubDom\<cdot>tb"  and "usOkay ch2 (tb . ch1)" and "ch3 \<in> ubDom\<cdot>tb" and "ch3 \<noteq> ch2" and "ch3 \<noteq> ch1"
  shows "(ubRenameCh tb ch1 ch2) . ch3 = tb . ch3"
  apply (simp add: ubRenameCh_def  ubSetCh_def)
  by (metis ComplI assms(2) assms(4) assms(5) dom_empty dom_fun_upd option.discI ubRep_ubAbs singletonD ubSetCh_well ubDom_ubRep_eq ubGetCh_ubRestrict ubUnion_ubGetchL ubWell_empty)

  subsection \<open>sbUp\<close>
(* ubUp *)
  thm ubUp_def
(* the function returns a ubundle  *)
lemma sbUp_well[simp]: "ubWell (\<lambda> c. if c \<in> ubDom\<cdot>b then (Rep_ubundle b)c else Some \<bottom>)"
  by (simp add: ubWell_def usOkay_bot)

(* helper for the cont proof *)
lemma ubUp_cont_h[simp]: "cont (\<lambda>b. (\<lambda> c. if c \<in> ubDom\<cdot>b then (Rep_ubundle b)c else Some \<bottom>))"
  by (smt contI2 below_ubundle_def eq_imp_below fun_below_iff is_ub_thelub lub_eq lub_fun monofunI
          po_class.chainE po_class.chainI ubRep_lub ubDom_below ubGetChE)

(* cont proof of ubUp *)
lemma ubUp_cont[simp]: "cont (\<lambda>b. Abs_ubundle (\<lambda> c. if (c\<in>ubDom\<cdot>b) then (Rep_ubundle b)c else Some \<bottom>))"
  by (simp add: cont_Abs_ubundle)

(* insert rule of ubUp *)
lemma ubUp_insert: "ubUp\<cdot>b = Abs_ubundle (\<lambda>c. if (c\<in>ubDom\<cdot>b) then (Rep_ubundle b) c else Some \<bottom>)"
  by(simp add: ubUp_def)

(* the dom after applying ubUp is the same as UNIV *)
lemma ubUp_ubDom [simp]: "ubDom\<cdot>(ubUp\<cdot>b) = UNIV"
  apply(simp add: ubDom_insert)
  apply(simp add: ubUp_insert)
  by (smt CollectD Collect_cong UNIV_def dom_def optionLeast_def optionleast_dom ubDom_insert)

(* ubUp doesnt effect existing channel in a bundle *)
lemma ubUp_ubGetCh[simp]: assumes "c \<in> ubDom\<cdot>b"
  shows "(ubUp\<cdot>b) . c = b .c"
  by (simp add: assms ubUp_insert ubGetCh_insert)

(* ubUp changes the channel not in a bundle into \<bottom>  *)
lemma ubUp_ubGetCh2[simp]: assumes "c\<notin>ubDom\<cdot>b"
  shows "(ubUp\<cdot>b) . c = \<bottom>"
  by (simp add: assms ubUp_insert ubGetCh_ubRep_eq)

(* ubUp changes all the channel of ubLeast into \<bottom>  *)
lemma [simp]: "ubUp\<cdot>(ubLeast cs) . c = \<bottom>"
  using ubUp_ubGetCh2 by force


(* ubEqSelected *)
  subsection \<open>ubEqSelected\<close>
 thm ubEqSelected_def    

(* two bundles are eq when an emty set is selected *)
lemma ubEqSelected_empty_set [simp]: "ubEqSelected {} tb1 tb2"
  by (simp add: ubEqSelected_def)  

(*   *)
lemma ubEqSelected_ubGetCh_eq: assumes "ubEqSelected cs tb1 tb2"
  shows "\<forall> c \<in> cs. (tb1 . c) = (tb2 . c)"
  by (metis (mono_tags) assms ubEqSelected_def ubGetCh_ubRestrict)

(* induction rule for ubEqSelected *) 
lemma ubEqSelectedI: assumes "\<forall> c \<in> cs. (tb1 . c) = (tb2 . c)"
                 and "cs \<subseteq> ubDom\<cdot>tb1" and "cs \<subseteq> ubDom\<cdot>tb2"
               shows "ubEqSelected cs tb1 tb2"
  apply (simp add: ubEqSelected_def)
proof -
  obtain cc :: "'a\<^sup>\<omega> \<Rightarrow> 'a\<^sup>\<omega> \<Rightarrow> channel" where
    f1: "\<forall>u ua. UBundle.ubDom\<cdot>u \<noteq> UBundle.ubDom\<cdot>ua \<or> cc ua u \<in> UBundle.ubDom\<cdot>u \<and> u . cc ua u \<noteq> ua . cc ua u \<or> u = ua"
    by (metis (no_types) ubGetChI)
  have f2: "UBundle.ubDom\<cdot>(tb1 \<bar> cs) = UBundle.ubDom\<cdot>(tb2 \<bar> cs)"
    using assms(2) assms(3) by auto
  moreover
  { assume "(tb1 \<bar> cs) . cc (tb2 \<bar> cs) (tb1 \<bar> cs) \<noteq> (tb2 \<bar> cs) . cc (tb2 \<bar> cs) (tb1 \<bar> cs)"
    have "cc (tb2 \<bar> cs) (tb1 \<bar> cs) \<notin> UBundle.ubDom\<cdot>(tb1 \<bar> cs) \<or> (tb1 \<bar> cs) . cc (tb2 \<bar> cs) (tb1 \<bar> cs) = (tb2 \<bar> cs) . cc (tb2 \<bar> cs) (tb1 \<bar> cs)"
      by (metis (no_types) assms(1) assms(2) inf.absorb_iff2 ubGetCh_ubRestrict ubRestrict_dom2)
    then have "tb1 \<bar> cs = tb2 \<bar> cs"
      using f2 f1 by meson }
  ultimately show "tb1 \<bar> cs = tb2 \<bar> cs"
    using f1 by meson
qed


(* ubEqCommon *)
  subsection \<open>ubEqCommon\<close>
 thm ubEqCommon_def   

(* if two bundles dont have same channel then ubEqCommon is true  *)
lemma ubEqCommon_no_inter: assumes "ubDom\<cdot>tb1 \<inter> ubDom\<cdot>tb2 = {}"
  shows "ubEqCommon tb1 tb2"
  by (simp add: assms(1) ubEqCommon_def)

(* a bundle is equal to itself on the common channels  *)
lemma ubEqCommon_id [simp]: "ubEqCommon tb tb"
  using ubEqCommon_def ubEqSelected_def by blast

(* induction rule for ubEqCommon  *)
lemma ubEqCommonI: assumes "\<forall> c \<in> (ubDom\<cdot>tb1 \<inter> ubDom\<cdot>tb2). (tb1 . c) = (tb2 . c)"
  shows "ubEqCommon tb1 tb2"
  by (simp add: assms ubEqSelectedI ubEqCommon_def)

(* ubPrefixSelected *)

(* ubPrefixCommon *)

(* ubMapStream *)
  
  
end