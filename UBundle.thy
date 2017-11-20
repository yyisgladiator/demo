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

abbreviation ubgetch_abbr :: "'m ubundle \<Rightarrow> channel \<Rightarrow> 'm" (infix " . " 65) where 
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

abbreviation ubunion_abbr :: " 'm ubundle \<Rightarrow> 'm ubundle \<Rightarrow> 'm ubundle" (infixl "\<uplus>" 100) where 
"b1 \<uplus> b2 \<equiv> ubUnion\<cdot>b1\<cdot>b2"

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

(*Streambundles are ub_well by definition*)
theorem ubrep_well[simp]: "ubWell (Rep_ubundle x)"
  using Rep_ubundle by auto

(*Rep und Abs - Theorems*)
theorem ubrep_ubabs[simp]: assumes "ubWell f" shows "Rep_ubundle (Abs_ubundle f) = f"
  by (simp add: Abs_ubundle_inverse assms)

theorem ubabs_ubrep[simp]: shows "Abs_ubundle (Rep_ubundle f) = f"
  by (simp add: Rep_ubundle_inverse)


(* a chain of 'm ubundles is also a chain after applying Rep_ubundle *)
lemma ubrep_chain[simp]: assumes "chain S"
  shows "chain (\<lambda>n. Rep_ubundle (S n))"
  by (meson assms below_ubundle_def po_class.chain_def)


lemma ubrep_chain_the[simp]: assumes "chain S" 
  shows "chain (\<lambda>n. the (Rep_ubundle (S n) c))"
  by (metis assms below_ubundle_def fun_belowD monofun_def op_the_mono po_class.chain_def)


(* the lub of a chain after applying rep on each element is also ubWell  *)
lemma ubwell_lub[simp]: assumes "chain S"
  shows "ubWell (\<Squnion>n. Rep_ubundle (S n))"
  by (metis adm_def assms lub_eq ubrep_chain ubrep_well ubWell_adm)


(*   *)
lemma ubrep_lub:assumes "chain Y"
  shows "(\<Squnion>i. Rep_ubundle (Y i)) = Rep_ubundle (\<Squnion>i.  Y i)"
  using assms lub_ubundle by fastforce


(*  *)
lemma ubrep_cont [simp]: "cont Rep_ubundle"
  by (smt Abs_ubundle_inject Cont.contI2 Rep_ubundle Rep_ubundle_inverse adm_def below_ubundle_def 
      lub_eq lub_ubundle mem_Collect_eq monofunI po_eq_conv ubWell_adm)


(*   *)
lemma ubrep_up_lub[simp]: assumes "chain Y"
  shows "range (\<lambda>n. the (Rep_ubundle (Y n) c)) <<| the (\<Squnion>n. Rep_ubundle (Y n) c)"
  by (metis assms cpo_lubI lub_fun part_the_lub ubrep_chain ubrep_chain_the)


(* Equivalence of evaluation of 'm ubundle based on lub of function values. *)
lemma ubrep_lub_eval: assumes "chain S" 
  shows "the (Rep_ubundle (\<Squnion>i. S i) c) = (\<Squnion>j. the (Rep_ubundle (S j) c))"
using assms part_the_lub ubrep_chain ubrep_lub by fastforce


(*   *)
lemma ubrep_chain_lub_dom_eq: assumes "chain S" 
  shows "dom (Rep_ubundle (S i)) = dom (Rep_ubundle (\<Squnion>i. S i))"
  by (meson assms below_ubundle_def is_ub_thelub part_dom_eq)


(*   *)
lemma ubrep_lessI: assumes "dom (Rep_ubundle b1) = dom (Rep_ubundle b2)" 
    and "\<And>c. c\<in>dom (Rep_ubundle b1) \<Longrightarrow>  the ((Rep_ubundle b1) c) \<sqsubseteq> the ((Rep_ubundle b2) c)"
  shows "b1 \<sqsubseteq> b2"
  by (meson assms(1) assms(2) below_ubundle_def part_below)


(*   *)
lemma ubrep_less_lub1: assumes "chain S" 
  shows "the (Rep_ubundle (S i) c) \<sqsubseteq> the (Rep_ubundle (\<Squnion>i. S i) c)"
  by (metis assms(1) is_ub_thelub ubrep_chain_the ubrep_lub_eval)


(*   *)
lemma ubrep_less_lub2: assumes "chain S"  and "range S <| u"
  shows "the (Rep_ubundle (\<Squnion>i. S i) c) \<sqsubseteq> the (Rep_ubundle u c)"
  by (metis assms(1) assms(2) below_option_def below_refl below_ubundle_def fun_below_iff is_lub_thelub)

(* if the function is ubWell then each element in the stream is usOkay  *)
lemma [simp]: assumes "ubWell f" and "c \<in> dom f"
  shows "usOkay c (f\<rightharpoonup>c)"
  using assms(1) assms(2) ubWell_def by auto


(* if each element in the stream is usOkay then the function is ubWell  *)
lemma ubwellI: assumes "\<And> c. c \<in> dom f \<Longrightarrow> usOkay c (f\<rightharpoonup>c)"
  shows "ubWell f"
  using assms ubWell_def by blast


  subsection \<open>ubDom\<close>
(* ubDom *)

  thm ubDom_def

(* the function udom is continuous *)
lemma ubdom_cont[simp]: "cont (\<lambda> ub. dom (Rep_ubundle ub))"
  by (smt Cont.contI2 below_ubundle_def is_ub_thelub monofunI not_below2not_eq part_dom_eq)

(* unfold rule *)
lemma ubdom_insert: "ubDom\<cdot>ub = dom (Rep_ubundle ub)"
  by (simp add: ubDom_def)

(* the dom of the ub is the same as the dom of the lifted function *)
lemma ubdom_ubrep_eq: "ubWell ub \<Longrightarrow> ubDom\<cdot>(Abs_ubundle ub) = dom ub"
  by (simp add: Abs_ubundle_inverse ubdom_insert)

(* if there is a relation between 2 ubs, they two have same dom  *)
lemma ubdom_below: assumes "ub1 \<sqsubseteq> ub2"
  shows "ubDom\<cdot>ub1 = ubDom\<cdot>ub2"
  by (metis assms below_ubundle_def part_dom_eq ubdom_insert)

(* all bundles in a chain have the same dom *)
lemma ubdom_chain_eq3: assumes "chain S"
  shows "ubDom\<cdot>(S i) = ubDom\<cdot>(S j)"
  using assms is_ub_thelub ubdom_below by blast
                      
(* all bundles in a chain have the same dom as the lub *)
lemma ubdom_chain_eq2[simp]: assumes "chain S"
  shows "ubDom\<cdot>(S i) = ubDom\<cdot>(\<Squnion>j. S j)"
  by (simp add: assms is_ub_thelub ubdom_below)

(* see ubdom_chain_eq2 *)
lemma ubdom_lub: assumes "chain Y" and "ubDom\<cdot>(Y i) = cs"
  shows "ubDom\<cdot>(\<Squnion> i. Y i) = cs"
  using assms(1) assms(2) by auto


lemma ubdom_channel_usokay[simp]: assumes "c \<in> ubDom\<cdot>ub"
  shows "usOkay c ((Rep_ubundle ub)\<rightharpoonup>c)"
  using assms ubrep_well ubdom_insert ubWell_def by blast


  subsection \<open>ubGetCh\<close>
(* ubGetCh *)
  thm ubGetCh_def


(* ubGetCh is cont *)
lemma ubgetch_cont [simp]: "cont (\<lambda>ub. ((Rep_ubundle ub) \<rightharpoonup> c))"
  by (smt Prelude.contI2 below_ubundle_def fun_below_iff lub_eq ubrep_lub_eval monofun_def not_below2not_eq op_the_mono)

(* the element in a channel is the same when it's lifted  *)
lemma ubgetch_ubrep_eq: "ubWell ub \<Longrightarrow> (Abs_ubundle ub) . c= ub \<rightharpoonup> c"
  by (simp add: Abs_ubundle_inverse ubGetCh_def)

(* the element in a channel is the same when unlifted  *)
lemma ubgetchE: assumes "c \<in> ubDom\<cdot>ub"
  shows "Some (ub . c) = (Rep_ubundle ub) c"
  by (metis (full_types) Rep_ubundle Rep_ubundle_inverse assms domIff mem_Collect_eq option.exhaust_sel ubgetch_ubrep_eq ubdom_insert)

(* the element in a channel of the lub is the same when applying ubGetCh on each ele  *)
lemma ubgetch_lub: assumes "chain Y" and "c \<in> ubDom\<cdot>(\<Squnion> i. Y i)"
  shows "(\<Squnion>i. Y i) . c = (\<Squnion>i. (Y i) . c)"
  using assms(1) contlub_cfun_arg by auto

(* the element in each channel has the same relation as its bundle  *)
lemma ubgetch_below: assumes "x \<sqsubseteq> y"
  shows "\<forall> c. x . c \<sqsubseteq> y . c"
  by (simp add: assms monofun_cfun_arg)

(* the element in a channel is the same when it's unlifted  *)
lemma ubgetch_insert: "ub . c = (Rep_ubundle ub) \<rightharpoonup> c"
  by (simp add: ubGetCh_def)

(* induction rule for equal proof of two bundle  *)
lemma ubgetchI: assumes "ubDom\<cdot>x = ubDom\<cdot>y" and "\<And>c. c\<in>(ubDom\<cdot>x) \<Longrightarrow> x . c = y . c"
  shows "x = y"
  by (metis Rep_ubundle_inject assms(1) assms(2) part_eq ubdom_insert ubgetch_insert)

(* id function *)
lemma [simp]: "Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>b)\<leadsto> b . c) = b"
  apply (rule ubgetchI, subst ubdom_ubrep_eq)
    apply (smt Rep_ubundle domIff mem_Collect_eq ubgetchE ubWell_def)
   apply simp
  by (smt Abs_cfun_inverse2 Abs_ubundle_inverse Rep_ubundle domIff mem_Collect_eq option.sel ubDom_def ubgetchE ubWell_def ubdom_cont)

  subsection \<open>eq/below\<close>

(* one bundle is below an other if they have the same domain and the below relation is the same on each channel  *)
lemma ub_below: assumes "ubDom\<cdot>x = ubDom\<cdot>y" and "\<And> c. c \<in> ubDom\<cdot>x \<Longrightarrow> x . c \<sqsubseteq> y . c"
  shows "x \<sqsubseteq> y"
  by (metis assms(1) assms(2) ubdom_insert ubgetch_insert ubrep_lessI)

(* one bundle is eq an other if the have the same domain and element in each channel is eq on *)
lemma ub_eq: assumes "ubDom\<cdot>x = ubDom\<cdot>y" and "\<And> c. c\<in>ubDom\<cdot>x \<Longrightarrow> x . c =y . c"
  shows "x=y"
  using assms(1) assms(2) ubgetchI by blast


subsection \<open>ubLeast\<close>
(* ubLeast *)

  thm ubLeast_def

(* the optionLeast of the optionCpo is well-formed  *)
lemma ubleast_well: "ubWell (optionLeast cs)"
  by (simp add: ubWell_def usOkay_bot)

(* our definition of ubLeast is equal optionLeast  *)
lemma ubleast_optionLeast_eq: "ubLeast cs = Abs_ubundle(optionLeast cs)"
  by (simp add: ubLeast_def optionLeast_def)
  
(* the dom of ubLeast is the same as the argument of the function  *)
lemma ubleast_ubdom [simp]: "ubDom\<cdot>(ubLeast cs) = cs"
  apply (simp add: ubDom_def)
  by (metis ubleast_optionLeast_eq optionleast_dom ubdom_insert ubdom_ubrep_eq ubleast_well)

(* the element in each channel is the bottom element  *)
lemma ubleast_ubgetch[simp]:  assumes "c \<in> cs"
  shows "(ubLeast cs) . c = \<bottom>"
  by (simp add: assms ubgetch_ubrep_eq ubleast_optionLeast_eq ubleast_well)

(* the ubLeast bundle is the smallest bundle  *)
lemma ubleast_below [simp]: assumes "cs = ubDom\<cdot>ub"
  shows "ubLeast cs \<sqsubseteq> ub"
  by (metis assms below_ubundle_def minimal part_below ubleast_ubgetch ubdom_insert ubgetch_insert ubleast_ubdom)

(* if ubLeast {} is in an chain, all elements are equal *)
lemma ubundle_allempty: assumes "chain Y" and "ubLeast {} \<in> range Y"
  shows "\<And>i. (Y i) = ubLeast {}"
  by (metis (no_types, lifting) Abs_cfun_inverse2 Rep_ubundle_inverse assms(1) assms(2) empty_iff f_inv_into_f 
        part_eq ubdom_chain_eq2 ubDom_def ubdom_cont ubleast_ubdom)


  subsection \<open>ubRestrict\<close>
(* ubRestrict *)
thm ubRestrict_def

(* the ubRestrict function returns a well-formed ubundle  *)
lemma ubrestrict_well [simp]: "ubWell (Rep_ubundle b |` cs)"
  by (metis (no_types, lifting) Rep_ubundle domIff mem_Collect_eq restrict_in restrict_out ubWell_def)

(* the ubRestrict function is monoton  *)
lemma ubRestrict_monofun[simp]: "monofun  (\<lambda>b. Rep_ubundle b |` cs)"
  by (metis (no_types, lifting) below_ubundle_def monofun_def part_restrict_monofun)

(* the ubRestrict function is continuous  part 1*)
lemma ubrestrict_cont1[simp]: "cont  (\<lambda>b. ((Rep_ubundle b) |` cs))"
  apply (rule contI2)
  apply simp
  by (smt Abs_ubundle_inverse Rep_ubundle adm_def below_option_def domIff fun_below_iff lub_eq lub_fun lub_ubundle mem_Collect_eq 
      part_dom_lub po_class.chain_def ubrep_chain restrict_map_def ubdom_chain_eq2 ubWell_adm)

(* the ubRestrict function is continuous *)
lemma ubrestrict_cont [simp]: "cont (\<lambda>b. Abs_ubundle (Rep_ubundle b |` cs))"
  by (simp add: cont_Abs_ubundle)

(*   *) 
lemma ubrestrict_insert : "ubRestrict cs\<cdot>ub = Abs_ubundle (Rep_ubundle ub |` cs)"
  by (simp add: ubRestrict_def)

(*   *)
lemma ubrestrict_ubrep_eq : "ubWell ub \<Longrightarrow> ubRestrict cs\<cdot>(Abs_ubundle ub) = Abs_ubundle (ub |` cs)"
  by (simp add: Abs_ubundle_inverse ubrestrict_insert)

(* the dom of the bundle after restrict its channel is a subset (or equal) its argument*)
lemma ubrestrict_ubdom [simp]: "ubDom\<cdot>(ubRestrict cs\<cdot>ub) \<subseteq> cs"
  by (simp add: ubdom_ubrep_eq ubrestrict_insert)

(* the dom of the bundle after restrict its channel is the conjunction of dom ub and first argument*)
lemma ubrestrict_ubdom2 [simp]: "ubDom\<cdot>(ubRestrict cs\<cdot>ub) = ubDom\<cdot>ub \<inter> cs"
  by (metis dom_restrict ubdom_insert ubdom_ubrep_eq ubrestrict_insert ubrestrict_well)

(* applying 2 times ubRestriction on a ubundle is eq the application of the function with the union of both channel set as argument  *)
lemma ubRestrict_twice [simp]: "ubRestrict cs2\<cdot>(ubRestrict cs1\<cdot>ub) = ubRestrict (cs1\<inter>cs2)\<cdot>ub"
  by (metis restrict_restrict ubrestrict_insert ubrestrict_ubrep_eq ubrestrict_well)

(* the element in the channel after restriction is equal the unrestrict bundle *)
lemma ubgetch_ubrestrict [simp]: assumes "c \<in> cs"
  shows "(ubRestrict cs\<cdot>ub) . c= ub . c "
  by (metis (no_types, lifting) Abs_cfun_inverse2 assms restrict_in ubGetCh_def ubgetch_cont ubgetch_ubrep_eq ubrestrict_insert ubrestrict_well)

(* the bundles after applying ubRestrict have the same below relation like its second  *)
lemma ubrestrict_belowI1: assumes "(a \<sqsubseteq> b)"
  shows "ubRestrict cs\<cdot>a \<sqsubseteq> ubRestrict cs\<cdot>b"
  using assms monofun_cfun_arg by auto

(* if an empty channel set is the first argument, then ubRestrict return the ubLeast with empty channel set  *)
lemma ubrestrict_ubleast [simp]: "ubRestrict {}\<cdot>ub = ubLeast {}"
  by (metis Rep_ubundle_inverse empty_iff empty_subsetI optionleast_dom part_eq subset_antisym ubleast_optionLeast_eq ubdom_insert ubrestrict_ubdom)

(* if the first argument disjoint with the domain of the bundle then the function return ubLeast with an empty channel set *)
lemma ubrestrict_ubleast2[simp]: assumes "cs \<inter> ubDom\<cdot>ub = {}" 
  shows "ubRestrict cs\<cdot>ub = ubLeast {}"
  by (metis Int_commute Int_empty_right assms dom_restrict ex_in_conv part_eq ubdom_insert ubrestrict_insert ubrestrict_ubleast)


lemma ubrestrict_id [simp]: assumes "ubDom\<cdot>ub \<subseteq> cs" shows "ubRestrict cs\<cdot>ub = ub"
  by (metis (mono_tags, lifting) assms contra_subsetD inf.absorb_iff1 ubgetchI ubgetch_ubrestrict ubrestrict_ubdom2)

    
lemma ubrestrict_ubdom_sub: assumes "ubDom\<cdot>ub \<subseteq> cs"
  shows "ub \<bar> cs = ub \<bar> (ubDom\<cdot>ub)"
  by (simp add: assms)
    
lemma ubrestrict_ubdom_sup_inter: 
  shows "ub \<bar> cs = ub \<bar> (cs \<inter> (ubDom\<cdot>ub))"
  by (metis (no_types, hide_lams) Int_commute inf_le2 ubrestrict_ubdom2 ubrestrict_id ubRestrict_twice)

  subsection \<open>ubLen\<close>
(* ubLen *) 
  thm ubLen_def


  subsection \<open>ubShift\<close>
(* ubShift *) 
  thm ubShift_def

  
(* ubUnion *)


(* ubSetCh *)

(*    
  subsection \<open>ubRemCh\<close>
(* ubRemCh *)

lemma ubremch_insert: "ubRemCh c\<cdot>b =  b \<bar> -{c}"
  by simp

lemma ubremch_ubdom [simp]: "ubDom\<cdot>(ubRemCh c\<cdot>b) = ubDom\<cdot>b - {c}"
  by auto
    
lemma ubremch2ubrestrict: "ubRemCh c\<cdot>b = ubRestrict (ubDom\<cdot>b - {c})\<cdot>b"
  by (metis (no_types, lifting) diff_eq eta_cfun subset_iff ubrestrict_id ubRestrict_twice)


  subsection \<open>ubRenameCh\<close>
(* ubRenameCh *)
  thm ubRenameCh_def
(* a bundle with only one channel based on other bundel is ubWell  *)
lemma ubWell_single_channel: assumes "c \<in> ubDom\<cdot>ub" shows "ubWell [c \<mapsto> Rep_ubundle ub\<rightharpoonup>c]"
  by (metis (full_types) assms ubrep_ubabs ubsetch_well ubdom_channel_usokay ubWell_empty)

(* change a channel to itself returns the same bundle  *)
lemma ubrenamech_id: assumes "c \<in> ubDom\<cdot>ub"
  shows "ubRenameCh ub c c = ub"
  apply (simp add: ubRenameCh_def ubgetch_insert ubSetCh_def ubremch_insert ubrestrict_insert)
  by (smt assms diff_eq dom_empty dom_fun_upd fun_upd_triv fun_upd_upd map_add_upd map_union_restrict restrict_complement_singleton_eq ubWell_single_channel ubabs_ubrep ubgetchE ubgetch_insert ubrep_ubabs ubrestrict_well ubunion_insert)

(* the dom of new bundle after renaming a channel is the union between new channel and the dom of bundle without the renamed channel  *)
lemma ubrenamech_ubdom: assumes "ch1 \<in> ubDom\<cdot>ub"  and "usOkay ch2 (ub . ch1)"
  shows "ubDom\<cdot>(ubRenameCh ub ch1 ch2) = (ubDom\<cdot>ub - {ch1}) \<union> {ch2}"
  apply (simp add: ubRenameCh_def  ubSetCh_def)
  by (metis assms(2) diff_eq dom_empty dom_fun_upd insert_is_Un option.simps(3) ubrep_ubabs sup_commute ubsetch_well ubdom_ubrep_eq ubWell_empty)
  
(* after renaming channel ch1 to ch2, old and new bundles have the same element on those channel  *)  
lemma ubrenamech_ubgetchI1: assumes "ch1 \<in> ubDom\<cdot>ub" 
                    and "usOkay ch2 (ub . ch1)"
  shows "(ubRenameCh ub ch1 ch2) . ch2 = ub . ch1"
  apply (simp add: ubRenameCh_def  ubSetCh_def)
  apply (subst ubunion_ubgetchR)
  apply (metis assms(2) dom_empty dom_fun_upd option.simps(3) ubrep_ubabs singletonI ubsetch_well ubdom_ubrep_eq ubWell_empty)
  by (metis assms(1) assms(2) fun_upd_same ubrep_ubabs ubsetch_well ubgetchE ubgetch_insert ubWell_empty)

(* renaming channel doesnt effect other channel in a bundle  *)           
lemma ubrenamech_ubgetchI2: assumes "ch1 \<in> ubDom\<cdot>ub"  and "usOkay ch2 (ub . ch1)" and "ch3 \<in> ubDom\<cdot>ub" and "ch3 \<noteq> ch2" and "ch3 \<noteq> ch1"
  shows "(ubRenameCh ub ch1 ch2) . ch3 = ub . ch3"
  apply (simp add: ubRenameCh_def  ubSetCh_def)
  by (metis ComplI assms(2) assms(4) assms(5) dom_empty dom_fun_upd option.discI ubrep_ubabs singletonD ubsetch_well ubdom_ubrep_eq ubgetch_ubrestrict ubunion_ubgetchL ubWell_empty)
*)

  subsection \<open>ubUp\<close>
(* ubUp *)
  thm ubUp_def
(* the function returns a ubundle  *)
lemma ubup_well[simp]: "ubWell (\<lambda> c. if c \<in> ubDom\<cdot>b then (Rep_ubundle b)c else Some \<bottom>)"
  by (simp add: ubWell_def usOkay_bot)

(* helper for the cont proof *)
lemma ubup_cont_h[simp]: "cont (\<lambda>b. (\<lambda> c. if c \<in> ubDom\<cdot>b then (Rep_ubundle b)c else Some \<bottom>))"
  by (smt contI2 below_ubundle_def eq_imp_below fun_below_iff is_ub_thelub lub_eq lub_fun monofunI
          po_class.chainE po_class.chainI ubrep_lub ubdom_below ubgetchE)

(* cont proof of ubUp *)
lemma ubup_cont[simp]: "cont (\<lambda>b. Abs_ubundle (\<lambda> c. if (c\<in>ubDom\<cdot>b) then (Rep_ubundle b)c else Some \<bottom>))"
  by (simp add: cont_Abs_ubundle)

(* insert rule of ubUp *)
lemma ubup_insert: "ubUp\<cdot>b = Abs_ubundle (\<lambda>c. if (c\<in>ubDom\<cdot>b) then (Rep_ubundle b) c else Some \<bottom>)"
  by(simp add: ubUp_def)

(* the dom after applying ubUp is the same as UNIV *)
lemma ubup_ubdom [simp]: "ubDom\<cdot>(ubUp\<cdot>b) = UNIV"
  apply(simp add: ubdom_insert)
  apply(simp add: ubup_insert)
  by (smt CollectD Collect_cong UNIV_def dom_def optionLeast_def optionleast_dom ubdom_insert)

(* ubUp doesnt effect existing channel in a bundle *)
lemma ubup_ubgetch[simp]: assumes "c \<in> ubDom\<cdot>b"
  shows "(ubUp\<cdot>b) . c = b .c"
  by (simp add: assms ubup_insert ubgetch_insert)

(* ubUp changes the channel not in a bundle into \<bottom>  *)
lemma ubup_ubgetch2[simp]: assumes "c\<notin>ubDom\<cdot>b"
  shows "(ubUp\<cdot>b) . c = \<bottom>"
  by (simp add: assms ubup_insert ubgetch_ubrep_eq)

(* ubUp changes all the channel of ubLeast into \<bottom>  *)
lemma [simp]: "ubUp\<cdot>(ubLeast cs) . c = \<bottom>"
  using ubup_ubgetch2 by force


(* ubEqSelected *)
  subsection \<open>ubEqSelected\<close>
 thm ubEqSelected_def    

(* two bundles are eq when an emty set is selected *)
lemma ubeqselected_empty_set [simp]: "ubEqSelected {} ub1 ub2"
  by (simp add: ubEqSelected_def)  

(*   *)
lemma ubeqselected_ubgetch_eq: assumes "ubEqSelected cs ub1 ub2"
  shows "\<forall> c \<in> cs. (ub1 . c) = (ub2 . c)"
  by (metis (mono_tags) assms ubEqSelected_def ubgetch_ubrestrict)

(* induction rule for ubEqSelected *) 
lemma ubeqselectedI: assumes "\<forall> c \<in> cs. (ub1 . c) = (ub2 . c)"
                 and "cs \<subseteq> ubDom\<cdot>ub1" and "cs \<subseteq> ubDom\<cdot>ub2"
               shows "ubEqSelected cs ub1 ub2"
  apply (simp add: ubEqSelected_def)
proof -
  obtain cc :: "'a\<^sup>\<omega> \<Rightarrow> 'a\<^sup>\<omega> \<Rightarrow> channel" where
    f1: "\<forall>u ua. UBundle.ubDom\<cdot>u \<noteq> UBundle.ubDom\<cdot>ua \<or> cc ua u \<in> UBundle.ubDom\<cdot>u \<and> u . cc ua u \<noteq> ua . cc ua u \<or> u = ua"
    by (metis (no_types) ubgetchI)
  have f2: "UBundle.ubDom\<cdot>(ub1 \<bar> cs) = UBundle.ubDom\<cdot>(ub2 \<bar> cs)"
    using assms(2) assms(3) by auto
  moreover
  { assume "(ub1 \<bar> cs) . cc (ub2 \<bar> cs) (ub1 \<bar> cs) \<noteq> (ub2 \<bar> cs) . cc (ub2 \<bar> cs) (ub1 \<bar> cs)"
    have "cc (ub2 \<bar> cs) (ub1 \<bar> cs) \<notin> UBundle.ubDom\<cdot>(ub1 \<bar> cs) \<or> (ub1 \<bar> cs) . cc (ub2 \<bar> cs) (ub1 \<bar> cs) = (ub2 \<bar> cs) . cc (ub2 \<bar> cs) (ub1 \<bar> cs)"
      by (metis (no_types) assms(1) assms(2) inf.absorb_iff2 ubgetch_ubrestrict ubrestrict_ubdom2)
    then have "ub1 \<bar> cs = ub2 \<bar> cs"
      using f2 f1 by meson }
  ultimately show "ub1 \<bar> cs = ub2 \<bar> cs"
    using f1 by meson
qed


(* ubEqCommon *)
  subsection \<open>ubEqCommon\<close>
 thm ubEqCommon_def   

(* if two bundles dont have same channel then ubEqCommon is true  *)
lemma ubeqcommon_no_inter: assumes "ubDom\<cdot>ub1 \<inter> ubDom\<cdot>ub2 = {}"
  shows "ubEqCommon ub1 ub2"
  by (simp add: assms(1) ubEqCommon_def)

(* a bundle is equal to itself on the common channels  *)
lemma ubeqcommon_id [simp]: "ubEqCommon ub ub"
  using ubEqCommon_def ubEqSelected_def by blast

(* induction rule for ubEqCommon  *)
lemma ubeqcommonI: assumes "\<forall> c \<in> (ubDom\<cdot>ub1 \<inter> ubDom\<cdot>ub2). (ub1 . c) = (ub2 . c)"
  shows "ubEqCommon ub1 ub2"
  by (simp add: assms ubeqselectedI ubEqCommon_def)

(* ubPrefixSelected *)

(* ubPrefixCommon *)

(* ubMapStream *)
  
  
end