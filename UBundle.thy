(*  Title:        UBundle
    Author:       Sebastian, Jens, Marc

    Description:  Defines stream bundles
*)

theory UBundle
  imports UnivClasses Channel "inc/OptionCpo"
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

cpodef 's::uscl ubundle ("(_\<^sup>\<Omega>)" [1000] 999) = "{b :: channel \<rightharpoonup> 's . ubWell b}"
  using ubWell_empty apply auto[1]
  using ubWell_adm by auto


setup_lifting type_definition_ubundle


(****************************************************)
section\<open>Definitions\<close>
(****************************************************)

  
text {* @{text "ubDom"} returns the domain of the given bundle *}
definition ubDom :: "'M\<^sup>\<Omega> \<rightarrow> channel set" where
"ubDom \<equiv> \<Lambda> b. dom (Rep_ubundle b)"


text {* @{text "ubRestrict"} creates a new bundle with the restricted channel set *}
definition ubRestrict:: "channel set \<Rightarrow> 'M\<^sup>\<Omega> \<rightarrow> 'M\<^sup>\<Omega>" where
"ubRestrict cs  \<equiv> \<Lambda> b. Abs_ubundle (Rep_ubundle b |` cs)"

abbreviation ubRestrict_abbr :: "'M\<^sup>\<Omega> \<Rightarrow> channel set \<Rightarrow> 'M\<^sup>\<Omega>" (infix "\<bar>" 65) where 
"b \<bar> cs \<equiv> ubRestrict cs\<cdot>b"


text {* @{text "ubGetCh"} returns the element of a given channel  *}
definition ubGetCh :: "channel \<Rightarrow> 'M\<^sup>\<Omega> \<rightarrow> 'M"  where
"ubGetCh c = (\<Lambda> b. ((Rep_ubundle b) \<rightharpoonup> c))"

abbreviation ubgetch_abbr :: "'M\<^sup>\<Omega> \<Rightarrow> channel \<Rightarrow> 'M" (infix " . " 65) where 
"b . c \<equiv> ubGetCh c\<cdot>b"


definition ubLen:: "'M\<^sup>\<Omega> \<Rightarrow> lnat " where
"ubLen b \<equiv> if ubDom\<cdot>b \<noteq> {} then (LEAST ln. ln\<in>{(usLen\<cdot>(b . c)) | c. c \<in> ubDom\<cdot>b}) else \<infinity>"  


text {* @{text "ubShift"}  the channel-domains are merged . Thats an easy converter. For example from "tstream USB" to "stream USB" *}
(* Can also be cont *)
definition ubShift :: "('A \<Rightarrow> 'B) \<Rightarrow> 'A\<^sup>\<Omega> \<Rightarrow> 'B\<^sup>\<Omega>" where
"ubShift f ub = Abs_ubundle (\<lambda>c. ((c\<in>ubDom\<cdot>ub) \<leadsto> f (ub . c)))"


text {* @{text "ubUnion"}  the channel-domains are merged *}
definition ubUnion :: "'M\<^sup>\<Omega> \<rightarrow> 'M\<^sup>\<Omega> \<rightarrow> 'M\<^sup>\<Omega>"  where 
"ubUnion \<equiv> \<Lambda> ub1 ub2 . Abs_ubundle ((Rep_ubundle ub1) ++ (Rep_ubundle ub2))"

abbreviation ubunion_abbr :: " 'M\<^sup>\<Omega> \<Rightarrow> 'M\<^sup>\<Omega> \<Rightarrow> 'M\<^sup>\<Omega>" (infixl "\<uplus>" 100) where 
"b1 \<uplus> b2 \<equiv> ubUnion\<cdot>b1\<cdot>b2"


text {* @{text "ubSetCh"} adds a channel or ubReplaces its content *}
definition ubSetCh :: "'M\<^sup>\<Omega> \<rightarrow> channel \<Rightarrow> 'M  \<Rightarrow> 'M\<^sup>\<Omega>" where
"ubSetCh \<equiv> \<Lambda> ub. (\<lambda> c m. ubUnion\<cdot>ub\<cdot>(Abs_ubundle([c \<mapsto> m])))"


text {* @{text "ubRemCh"} removes a channel from a timed stream bundle *}
abbreviation ubRemCh :: "channel \<Rightarrow> 'M\<^sup>\<Omega>  \<rightarrow> 'M\<^sup>\<Omega>" where
"ubRemCh \<equiv> \<lambda> c. \<Lambda> b. ubRestrict (-{c})\<cdot>b"


text {* @{text "ubRenameCh"} renames a channel  in a bundle *}
definition ubRenameCh :: "'M\<^sup>\<Omega> \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> 'M\<^sup>\<Omega>" where
 "ubRenameCh b ch1 ch2 \<equiv> (ubSetCh\<cdot>(ubRemCh ch1\<cdot>b)) ch2 (b . ch1)"


text {* @{text "ubEqSelected"} equality on specific channels *}
definition ubEqSelected:: " channel set \<Rightarrow> 'M\<^sup>\<Omega> => 'M\<^sup>\<Omega> => bool" where
"ubEqSelected cs b1 b2 \<equiv>  (b1\<bar>cs) = (b2\<bar>cs)"


text {* @{text "ubEqCommon"} equality on common channels *}
definition ubEqCommon:: " 'M\<^sup>\<Omega> => 'M\<^sup>\<Omega> => bool" where
"ubEqCommon b1 b2\<equiv> ubEqSelected (ubDom\<cdot>b1 \<inter> ubDom\<cdot>b2) b1 b2"


definition UB :: "channel set \<Rightarrow> 'm ubundle set" where
  "UB cs = {b. ubDom\<cdot>b = cs}"


text {* @{text " ubPrefixSelected"} prefix relation on selected channels *}
definition ubPrefixSelected:: "channel set \<Rightarrow> 'M\<^sup>\<Omega> \<Rightarrow> 'M\<^sup>\<Omega> \<Rightarrow> bool" where
"ubPrefixSelected cs b1 b2 \<equiv> (b1\<bar>cs \<sqsubseteq> b2\<bar>cs)"


text {* @{text " ubPrefixCommon"} prefix relation on common channels *}
definition ubPrefixCommon:: "'M\<^sup>\<Omega> \<Rightarrow> 'M\<^sup>\<Omega> \<Rightarrow> bool" where
"ubPrefixCommon b1 b2 \<equiv> ubPrefixSelected (ubDom\<cdot>b1 \<inter> ubDom\<cdot>b2) b1 b2"


text {* @{text " ubMapStream"} applies function to all streams *}
definition ubMapStream:: "('M \<Rightarrow> 'M) \<Rightarrow>'M\<^sup>\<Omega> \<Rightarrow> 'M\<^sup>\<Omega>" where
"ubMapStream f b =  Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>b) \<leadsto> f (b . c))"

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

lemma cont_Abs_UB[simp]: assumes "cont g" and "\<forall>x. ub_well (g x)"
  shows "cont (\<lambda>x. Abs_ubundle (g x))"
  sorry

(* a chain of 'M\<^sup>\<Omega>s is also a chain after applying Rep_ubundle *)
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

(* Equivalence of evaluation of 'M\<^sup>\<Omega> based on lub of function values. *)
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

lemma less_UBI: assumes "dom (Rep_ubundle b1) = dom (Rep_ubundle b2)"
    and "\<And>c. c \<in> dom (Rep_ubundle b1) \<Longrightarrow> the ((Rep_ubundle b1) c) \<sqsubseteq> the ((Rep_ubundle b2) c)"
  shows "b1 \<sqsubseteq> b2"
  using assms(1) assms(2) ubrep_lessI by blast

lemma less_ubLub1: assumes "chain S"
  shows "the (Rep_ubundle (S i) c) \<sqsubseteq> the (Rep_ubundle (\<Squnion>i. S i) c)"
  by (simp add: assms ubrep_less_lub1)

lemma less_ubLub2: assumes "chain S" and "range S <| u"
  shows "the (Rep_ubundle (\<Squnion>i. S i) c) \<sqsubseteq> the (Rep_ubundle u c)"
  by (simp add: assms(1) assms(2) ubrep_less_lub2)

subsection \<open>ubDom\<close>


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

lemma ubdom_empty [simp]: "ubDom\<cdot>(Abs_ubundle empty) = {}"
  by (simp add: ubWell_empty ubdom_ubrep_eq)
    
subsection \<open>ubGetCh\<close>

  
(* ubGetCh is cont *)
lemma ubgetch_cont [simp]: "cont (\<lambda>ub. ((Rep_ubundle ub) \<rightharpoonup> c))"
  by (smt Prelude.contI2 below_ubundle_def fun_below_iff lub_eq ubrep_lub_eval monofun_def not_below2not_eq op_the_mono)

lemma ubgetch_cont2[simp]: "cont (\<lambda>ub uc. the ((Rep_ubundle ub) uc))"
  by simp

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

      
subsection \<open>ubRestrict\<close>


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
  shows "(ubRestrict cs\<cdot>ub) . c = ub . c "
  by (metis (no_types, lifting) Abs_cfun_inverse2 assms restrict_in ubGetCh_def ubgetch_cont ubgetch_ubrep_eq ubrestrict_insert ubrestrict_well)

(* the bundles after applying ubRestrict have the same below relation like its second  *)
lemma ubrestrict_belowI1: assumes "(a \<sqsubseteq> b)"
  shows "ubRestrict cs\<cdot>a \<sqsubseteq> ubRestrict cs\<cdot>b"
  using assms monofun_cfun_arg by auto

lemma ubrestrict_below: assumes "chain Y" and "cont h"
  shows "(ubRestrict (h (\<Squnion>i. Y i))\<cdot>(g (ubDom\<cdot>(\<Squnion>i. Y i)))) \<sqsubseteq>
         (\<Squnion>i. (ubRestrict (h (Y i))\<cdot>(g (ubDom\<cdot>(\<Squnion>i. Y i)))))"
    sorry

lemma ubrestrict_id [simp]: assumes "ubDom\<cdot>ub \<subseteq> cs" shows "ubRestrict cs\<cdot>ub = ub"
  by (metis (mono_tags, lifting) assms contra_subsetD inf.absorb_iff1 ubgetchI ubgetch_ubrestrict ubrestrict_ubdom2)

lemma ubrestrict_ubdom_sub: assumes "ubDom\<cdot>ub \<subseteq> cs"
  shows "ub \<bar> cs = ub \<bar> (ubDom\<cdot>ub)"
  by (simp add: assms)
    
lemma ubrestrict_ubdom_sup_inter: 
  shows "ub \<bar> cs = ub \<bar> (cs \<inter> (ubDom\<cdot>ub))"
  by (metis (no_types, hide_lams) Int_commute inf_le2 ubrestrict_ubdom2 ubrestrict_id ubRestrict_twice)

    
subsection \<open>ubLen\<close>


  
  
subsection \<open>ubShift\<close>


  

subsection \<open>ubUnion\<close>

  
lemma ubunion_well [simp]: assumes "ubWell b1" and "ubWell b2"
  shows "ubWell (b1 ++ b2)"
  apply (simp add: ubWell_def)
  by (metis (no_types, lifting)
      Un_iff assms(1) assms(2) map_add_dom_app_simps(1) map_add_dom_app_simps(3) ubWell_def)

lemma ubunion_contL [simp]: "cont (\<lambda> b1. (Rep_ubundle b1) ++ (Rep_ubundle b2))"
  using cont_compose part_add_contL ubrep_cont by blast

lemma ubunion_contR [simp]: "cont (\<lambda> b2. (Rep_ubundle b1) ++ (Rep_ubundle b2))"
  using cont_compose part_add_contR ubrep_cont by blast

lemma ubunion_cont [simp]: "cont (\<lambda> b1. \<Lambda> b2. Abs_ubundle (Rep_ubundle b1 ++ Rep_ubundle b2))"
  apply (rule cont2cont_LAM)
  apply (metis (mono_tags)
         Rep_ubundle cont_Abs_ubundle mem_Collect_eq ubunion_contR ubunion_well)
  by (metis (mono_tags)
      Rep_ubundle cont_Abs_ubundle mem_Collect_eq ubunion_contL ubunion_well)

lemma ubunion_insert: "(b1 \<uplus> b2) = Abs_ubundle (Rep_ubundle b1 ++ Rep_ubundle b2)"
  apply (simp add: ubUnion_def)
  using ubunion_contR ubunion_contL ubunion_cont by (simp add: cont_Abs_ubundle)

lemma ubunion_idL [simp]: assumes "ubDom\<cdot>b1 \<subseteq> ubDom\<cdot>b2"
  shows "b1 \<uplus> b2 = b2"
  using assms apply (simp add: ubunion_insert)
  by (simp add: ubdom_insert)

lemma ubunion_commutative: assumes "ubDom\<cdot>b1 \<inter> ubDom\<cdot>b2 = {}"
  shows "b1 \<uplus> b2 = b2 \<uplus> b1"
  using assms apply (simp add: ubunion_insert)
  by (metis map_add_comm ubdom_insert)

lemma ubunion_associative: "b1 \<uplus> (b2 \<uplus> b3) = (b1 \<uplus> b2) \<uplus> b3"
  by (simp add: ubunion_insert)

lemma ubunion_getchR [simp]: assumes "c \<in> ubDom\<cdot>b2"
  shows "b1 \<uplus> b2 . c = b2 . c"
  apply (simp add: ubunion_insert ubgetch_insert)
  by (metis assms map_add_find_right ubgetchE)

lemma ubunion_getchL [simp]: assumes "c \<notin> ubDom\<cdot>b2"
  shows "b1 \<uplus> b2 . c = b1 . c"
  apply (simp add: ubunion_insert ubgetch_insert)
  by (metis assms map_add_dom_app_simps(3) ubdom_insert)

lemma ubunionDom [simp]: "ubDom\<cdot>(b1 \<uplus> b2) = ubDom\<cdot>b1 \<union> ubDom\<cdot>b2"
  by (auto simp add: ubdom_insert ubunion_insert)

lemma ubunion_pref_eq: assumes "a \<sqsubseteq> b" and "c \<sqsubseteq> d"
  shows "a \<uplus> c \<sqsubseteq> b \<uplus> d"
  by (simp add: assms monofun_cfun)

lemma ubunion_pref_eq2: assumes "a \<sqsubseteq> b"
  shows "x \<uplus> a \<sqsubseteq> x \<uplus> b"
  by (metis assms monofun_cfun_arg)

lemma ubunion_assoc2: "(b1 \<uplus> b2) \<uplus> b3 = b1 \<uplus> (b2 \<uplus> b3)"
  by (simp add: ubunion_associative)

lemma ubunion_eqI: assumes "a = b" and "c = d"
  shows "a \<uplus> c = b \<uplus> d"
  by (simp add: assms)


subsection \<open>ubSetCh\<close>

  
lemma ubsetch_cont [simp]: "cont (\<lambda> ub. (\<lambda> c m. ubUnion\<cdot>ub\<cdot>(Abs_ubundle [c \<mapsto> m])))"
  by simp

lemma ubsetch_well [simp]: assumes "usOkay c s"
  shows "ubWell ((Rep_ubundle b) (c \<mapsto> s))"
  by (metis
      assms dom_fun_upd fun_upd_apply insert_iff option.sel option.simps(3) ubrep_well ubWell_def)

lemma ubsetch_insert: assumes "usOkay c s"
  shows "(ubSetCh\<cdot>b) c s = b \<uplus> Abs_ubundle [c \<mapsto> s]"
  by (simp add: ubSetCh_def)


  subsection \<open>ubRemCh\<close>
(* ubRemCh *)

lemma ubremch_insert: "ubRemCh c\<cdot>b =  b \<bar> -{c}"
  by simp

lemma ubremch_ubdom [simp]: "ubDom\<cdot>(ubRemCh c\<cdot>b) = ubDom\<cdot>b - {c}"
  by auto
    
lemma ubremch2ubrestrict: "ubRemCh c\<cdot>b = ubRestrict (ubDom\<cdot>b - {c})\<cdot>b"
  by (metis (no_types, lifting) diff_eq eta_cfun subset_iff ubrestrict_id ubRestrict_twice)

lemma ubres_pref_eq: assumes "(a \<sqsubseteq> b)" shows "(a \<bar> cs) \<sqsubseteq> (b \<bar> cs)"
  by (simp add: assms ubrestrict_belowI1)

lemma ubres_ubdom_supset: assumes "ubDom\<cdot>ub \<subseteq> cs" shows "ub \<bar> cs = ub \<bar> (ubDom\<cdot>ub)"
  by (simp add: assms)

lemma ubres_ubdom_supset_inter: "ub \<bar> cs = ub \<bar> (cs \<inter> (ubDom\<cdot>ub))"
  using ubrestrict_ubdom_sup_inter by blast

lemma ub_ubdom: "ubDom\<cdot>(SOME b. b \<in> UB cs) = cs"
  apply (simp add: UB_def)
  sorry

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

    (*
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



subsection \<open>ubEqSelected\<close>
    
  
(* two bundles are eq when an emty set is selected *)
lemma ubeqselected_empty_set [simp]: "ubEqSelected {} ub1 ub2"
  by (metis (no_types, lifting) bot.extremum_uniqueI empty_iff ubEqSelected_def ub_eq ubrestrict_ubdom)  

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
  obtain cc :: "'a\<^sup>\<Omega> \<Rightarrow> 'a\<^sup>\<Omega> \<Rightarrow> channel" where
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


subsection \<open>ubEqCommon\<close>  

   
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

subsection \<open>ubMapStream\<close>


abbreviation fun_well_type :: "('M \<Rightarrow> 'M) \<Rightarrow> bool" where
"fun_well_type f \<equiv> (\<forall> cs s. (usOkay cs s \<longrightarrow> usOkay cs (f s)))"

lemma ubDom_funtype: assumes "\<forall>c ts. usOkay c ts \<longrightarrow> usOkay c (f ts)"
  shows "fun_well_type f"
  using assms by blast

lemma ubMapStream_well: assumes "fun_well_type f"
  shows "ubWell (\<lambda>c. ((c \<in> ubDom\<cdot>b)\<leadsto>(f (b . c))))"
  by (simp add: assms ubWell_def ubgetch_insert)

lemma ubMapStream_ubDom: assumes "fun_well_type f"
  shows "ubDom\<cdot>(ubMapStream f b) = ubDom\<cdot>b"
  by (simp add: assms ubMapStream_def ubMapStream_well ubdom_ubrep_eq)

lemma ubMapStream_ubGetCh: assumes "fun_well_type f" and "c \<in> ubDom\<cdot>b"
  shows "(ubMapStream f b) . c = f (b . c)"
  by (simp add: assms(1) assms(2) ubMapStream_def ubMapStream_well ubgetch_insert)


lemma ubMapStream_contI1: assumes "cont f" and "fun_well_type f"
  shows "cont (ubMapStream f)"
proof (rule contI2)
  show "monofun (ubMapStream f)"
    using monofunI
    by (smt assms(1) assms(2) monofunE monofun_Rep_cfun2 ubMapStream_ubGetCh ubMapStream_def ubMapStream_ubDom ubMapStream_well ub_below ubdom_below ubgetchE ubrep_ubabs Abs_cfun_inverse2)
  thus "\<forall>Y. chain Y \<longrightarrow> ubMapStream f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. ubMapStream f (Y i))"
 (***)  by (smt assms(1) assms(2) cont2contlubE lub_eq monofun_def not_below2not_eq po_class.chain_def ubMapStream_ubDom ubMapStream_ubGetCh ub_below ubdom_insert ubgetch_insert ubrep_chain_lub_dom_eq ubrep_chain_the ubrep_lub_eval)
(* konnten leider beide nicht per using auf nicht-smt form gebracht werden*) 
qed


lemma ubMapStream_contI2: assumes "cont f" and "\<forall>c ts. usOkay c ts \<longrightarrow> usOkay c (f ts)"
  shows "cont (ubMapStream f)"
  by (simp add: assms(1) assms(2) ubMapStream_contI1)

lemma if_then_ubDom: assumes "d \<in> dom (\<lambda> b. (ubDom\<cdot>b = In) \<leadsto> (F b))"
  shows "ubDom\<cdot>d = In"
  by (smt assms domIff)

(**)
(*
 proof -
  have "\<forall>f. (\<exists>u ua. (u::'a\<^sup>\<Omega>) \<sqsubseteq> ua \<and> (f u::'a\<^sup>\<Omega>) \<notsqsubseteq> f ua) \<or> monofun f"
    by (metis (no_types) monofunI)
  then obtain uu :: "('a\<^sup>\<Omega> \<Rightarrow> 'a\<^sup>\<Omega>) \<Rightarrow> 'a\<^sup>\<Omega>" and uua :: "('a\<^sup>\<Omega> \<Rightarrow> 'a\<^sup>\<Omega>) \<Rightarrow> 'a\<^sup>\<Omega>" where
    f1: "\<forall>f. uu f \<sqsubseteq> uua f \<and> f (uu f) \<notsqsubseteq> f (uua f) \<or> monofun f"
    by (metis (full_types))
  obtain cc :: "'a\<^sup>\<Omega> \<Rightarrow> 'a\<^sup>\<Omega> \<Rightarrow> channel" where
    f2: "\<forall>x0 x1. (\<exists>v2. v2 \<in> UBundle.ubDom\<cdot>x1 \<and> x1 . v2 \<notsqsubseteq> x0 . v2) = (cc x0 x1 \<in> UBundle.ubDom\<cdot>x1 \<and> x1 . cc x0 x1 \<notsqsubseteq> x0 . cc x0 x1)"
    by moura
  have "\<forall>f u. (\<exists>c a. usOkay c (a::'a) \<and> \<not> usOkay c (f a)) \<or> UBundle.ubDom\<cdot>(ubMapStream f u) = UBundle.ubDom\<cdot>u"
    by (metis (no_types) ubMapStream_ubDom)
  then obtain cca :: "('a \<Rightarrow> 'a) \<Rightarrow> channel" and aa :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
    f3: "\<forall>f u. usOkay (cca f) (aa f) \<and> \<not> usOkay (cca f) (f (aa f)) \<or> UBundle.ubDom\<cdot>(ubMapStream f u) = UBundle.ubDom\<cdot>u"
    by moura
  have f4: "\<forall>c a. \<not> usOkay c a \<or> usOkay c (f a)"
    using assms(2) by auto
  then have f5: "UBundle.ubDom\<cdot>(ubMapStream f (uu (ubMapStream f))) = UBundle.ubDom\<cdot>(uu (ubMapStream f))"
    using f3 by metis
  have f6: "UBundle.ubDom\<cdot>(ubMapStream f (uua (ubMapStream f))) = UBundle.ubDom\<cdot>(uua (ubMapStream f))"
    using f4 f3 by metis
  have f7: "UBundle.ubDom\<cdot>(ubMapStream f (uu (ubMapStream f))) = UBundle.ubDom\<cdot>(uu (ubMapStream f))"
    using f4 f3 by metis
  have f8: "\<forall>f u. (\<exists>c a. usOkay c (a::'a) \<and> \<not> usOkay c (f a::'a)) \<or> ubWell (\<lambda>c. (c \<in> UBundle.ubDom\<cdot>u)\<leadsto>f (u . c))"
    using ubMapStream_well by auto
  then have f9: "ubWell (\<lambda>c. (c \<in> UBundle.ubDom\<cdot> (uu (ubMapStream f)))\<leadsto>f (uu (ubMapStream f) . c))"
    using f4 by blast
  have f10: "ubWell (\<lambda>c. (c \<in> UBundle.ubDom\<cdot> (uua (ubMapStream f)))\<leadsto>f (uua (ubMapStream f) . c))"
    using f8 f4 by blast
  have "UBundle.ubDom\<cdot>(ubMapStream f (uua (ubMapStream f))) = UBundle.ubDom\<cdot>(uua (ubMapStream f))"
    using f4 f3 by metis
  then have f11: "UBundle.ubDom\<cdot> (Abs_ubundle (\<lambda>c. (c \<in> UBundle.ubDom\<cdot> (uua (ubMapStream f)))\<leadsto>f (uua (ubMapStream f) . c))) = UBundle.ubDom\<cdot>(uua (ubMapStream f))"
    by (simp add: ubMapStream_def)
  { assume "uu (ubMapStream f) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<sqsubseteq> uua (ubMapStream f) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))"
    { assume "(Abs_cfun f\<cdot> (uu (ubMapStream f) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))) \<sqsubseteq> Abs_cfun f\<cdot> (uua (ubMapStream f) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))))) \<noteq> (ubMapStream f (uu (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<sqsubseteq> ubMapStream f (uua (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))))"
      moreover
      { assume "Abs_cfun f\<cdot> (uu (ubMapStream f) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))) \<noteq> ubMapStream f (uu (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))"
        moreover
        { assume "Some (Abs_ubundle (\<lambda>c. (c \<in> UBundle.ubDom\<cdot> (uu (ubMapStream f)))\<leadsto>f (uu (ubMapStream f) . c)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))) \<noteq> Rep_ubundle (Abs_ubundle (\<lambda>c. (c \<in> UBundle.ubDom\<cdot> (uu (ubMapStream f)))\<leadsto>f (uu (ubMapStream f) . c))) (cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))))"
          then have "cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<notin> UBundle.ubDom\<cdot> (Abs_ubundle (\<lambda>c. (c \<in> UBundle.ubDom\<cdot> (uu (ubMapStream f)))\<leadsto>f (uu (ubMapStream f) . c)))"
            using ubgetchE by force
          then have "cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<notin> UBundle.ubDom\<cdot>(ubMapStream f (uu (ubMapStream f))) \<or> ubMapStream f (uu (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<sqsubseteq> ubMapStream f (uua (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))"
            by (simp add: ubMapStream_def) }
        ultimately have "cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<notin> UBundle.ubDom\<cdot>(ubMapStream f (uu (ubMapStream f))) \<or> ubMapStream f (uu (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<sqsubseteq> ubMapStream f (uua (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))"
          using f9 by (simp add: assms(1) ubMapStream_def) }
      moreover
      { assume "Abs_cfun f\<cdot> (uua (ubMapStream f) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))) \<noteq> ubMapStream f (uua (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))"
        then have "Some (f (uua (ubMapStream f) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))))) \<noteq> Some (ubMapStream f (uua (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))))"
          using assms(1) by force
        then have "Some (f (uua (ubMapStream f) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))))) \<noteq> Some (Abs_ubundle (\<lambda>c. (c \<in> UBundle.ubDom\<cdot> (uua (ubMapStream f)))\<leadsto>f (uua (ubMapStream f) . c)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))))"
          by (simp add: ubMapStream_def)
        then have "Some (Abs_ubundle (\<lambda>c. (c \<in> UBundle.ubDom\<cdot> (uua (ubMapStream f)))\<leadsto>f (uua (ubMapStream f) . c)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))) \<noteq> Rep_ubundle (Abs_ubundle (\<lambda>c. (c \<in> UBundle.ubDom\<cdot> (uua (ubMapStream f)))\<leadsto>f (uua (ubMapStream f) . c))) (cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))) \<or> Some (f (uua (ubMapStream f) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))))) \<noteq> Rep_ubundle (Abs_ubundle (\<lambda>c. (c \<in> UBundle.ubDom\<cdot> (uua (ubMapStream f)))\<leadsto>f (uua (ubMapStream f) . c))) (cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))))"
          by metis
        moreover
        { assume "Some (f (uua (ubMapStream f) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))))) \<noteq> Rep_ubundle (Abs_ubundle (\<lambda>c. (c \<in> UBundle.ubDom\<cdot> (uua (ubMapStream f)))\<leadsto>f (uua (ubMapStream f) . c))) (cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))))"
          then have "(cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<in> UBundle.ubDom\<cdot> (uua (ubMapStream f)))\<leadsto>f (uua (ubMapStream f) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))) \<noteq> Some (f (uua (ubMapStream f) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))))"
            using f10 by force
          then have "UBundle.ubDom\<cdot>(uu (ubMapStream f)) = UBundle.ubDom\<cdot>(uua (ubMapStream f)) \<longrightarrow> cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<notin> UBundle.ubDom\<cdot>(ubMapStream f (uu (ubMapStream f))) \<or> ubMapStream f (uu (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<sqsubseteq> ubMapStream f (uua (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))"
            using f7 by (metis (no_types)) }
        ultimately have "UBundle.ubDom\<cdot>(uu (ubMapStream f)) = UBundle.ubDom\<cdot>(uua (ubMapStream f)) \<longrightarrow> cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<notin> UBundle.ubDom\<cdot>(ubMapStream f (uu (ubMapStream f))) \<or> ubMapStream f (uu (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<sqsubseteq> ubMapStream f (uua (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))"
          using f11 f7 ubgetchE by blast }
      ultimately have "UBundle.ubDom\<cdot>(uu (ubMapStream f)) = UBundle.ubDom\<cdot>(uua (ubMapStream f)) \<longrightarrow> cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<notin> UBundle.ubDom\<cdot>(ubMapStream f (uu (ubMapStream f))) \<or> ubMapStream f (uu (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<sqsubseteq> ubMapStream f (uua (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))"
        by fastforce }
    moreover
    { assume "cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<notin> UBundle.ubDom\<cdot>(ubMapStream f (uu (ubMapStream f))) \<or> ubMapStream f (uu (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<sqsubseteq> ubMapStream f (uua (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f)))"
      then have "UBundle.ubDom\<cdot>(ubMapStream f (uu (ubMapStream f))) = UBundle.ubDom\<cdot>(ubMapStream f (uua (ubMapStream f))) \<longrightarrow> UBundle.ubDom\<cdot>(ubMapStream f (uu (ubMapStream f))) = UBundle.ubDom\<cdot>(ubMapStream f (uua (ubMapStream f))) \<and> (cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<notin> UBundle.ubDom\<cdot>(ubMapStream f (uu (ubMapStream f))) \<or> ubMapStream f (uu (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))) \<sqsubseteq> ubMapStream f (uua (ubMapStream f)) . cc (ubMapStream f (uua (ubMapStream f))) (ubMapStream f (uu (ubMapStream f))))"
        by metis
      moreover
      { assume "UBundle.ubDom\<cdot>(ubMapStream f (uu (ubMapStream f))) \<noteq> UBundle.ubDom\<cdot>(ubMapStream f (uua (ubMapStream f)))"
        then have "UBundle.ubDom\<cdot>(uu (ubMapStream f)) \<noteq> UBundle.ubDom\<cdot>(uua (ubMapStream f))"
          using f6 f5 by blast }
      ultimately have "UBundle.ubDom\<cdot>(uu (ubMapStream f)) = UBundle.ubDom\<cdot>(uua (ubMapStream f)) \<longrightarrow> monofun (ubMapStream f)"
        using f2 f1 by (meson ub_below) }
    ultimately have "monofun (ubMapStream f) \<or> uu (ubMapStream f) \<notsqsubseteq> uua (ubMapStream f) \<or> ubMapStream f (uu (ubMapStream f)) \<sqsubseteq> ubMapStream f (uua (ubMapStream f))"
      by (meson cont_pref_eq1I ubdom_below) }
  then show ?thesis
    using f1 by (metis (no_types) cont_pref_eq1I)
qed
*)


(***)
(*
proof -
obtain cc :: "'a\<^sup>\<Omega> \<Rightarrow> 'a\<^sup>\<Omega> \<Rightarrow> channel" where
f1: "\<forall>x0 x1. (\<exists>v2. v2 \<in> UBundle.ubDom\<cdot>x1 \<and> x1 . v2 \<notsqsubseteq> x0 . v2) = (cc x0 x1 \<in> UBundle.ubDom\<cdot>x1 \<and> x1 . cc x0 x1 \<notsqsubseteq> x0 . cc x0 x1)"
  by moura
  have f2: "\<forall>c a. \<not> usOkay c a \<or> usOkay c (f a)"
    using assms(2) by presburger
  then have f3: "cc (\<Squnion>n. ubMapStream f (v0_0 (n::nat))) (ubMapStream f (Lub v0_0)) \<notin> UBundle.ubDom\<cdot> (v0_0 (v2_1 (\<lambda>n. Rep_ubundle (ubMapStream f (v0_0 n))\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))) (\<lambda>n. f Rep_ubundle (v0_0 n)\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))))) \<or> ubMapStream f (v0_0 (v2_1 (\<lambda>n. Rep_ubundle (ubMapStream f (v0_0 n))\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))) (\<lambda>n. f Rep_ubundle (v0_0 n)\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))))) . cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)) = f (v0_0 (v2_1 (\<lambda>n. Rep_ubundle (ubMapStream f (v0_0 n))\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))) (\<lambda>n. f Rep_ubundle (v0_0 n)\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)))) . cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)))"
using ubMapStream_ubGetCh by blast
have "\<forall>f fa. (\<exists>n. (f (n::nat)::'a) \<noteq> fa n) \<or> Lub f = Lub fa"
  using lub_eq by fastforce
  then obtain nn :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat" where
    f4: "\<forall>f fa. f (nn fa f) \<noteq> fa (nn fa f) \<or> Lub f = Lub fa"
    by meson
  have f5: "\<forall>f fa. (\<not> cont f \<or> \<not> chain fa) \<or> (f (Lub fa::'a)::'a) = (\<Squnion>n. f (fa n))"
    using cont2contlubE by auto
  have "\<forall>f u. (\<exists>c a. usOkay c (a::'a) \<and> \<not> usOkay c (f a)) \<or> UBundle.ubDom\<cdot>(ubMapStream f u) = UBundle.ubDom\<cdot>u"
    by (metis (no_types) ubMapStream_ubDom)
  then obtain cca :: "('a \<Rightarrow> 'a) \<Rightarrow> channel" and aa :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
    f6: "\<forall>f u. usOkay (cca f) (aa f) \<and> \<not> usOkay (cca f) (f (aa f)) \<or> UBundle.ubDom\<cdot>(ubMapStream f u) = UBundle.ubDom\<cdot>u"
    by moura
  then have f7: "UBundle.ubDom\<cdot>(ubMapStream f (Lub v0_0)) = UBundle.ubDom\<cdot>(Lub v0_0)"
    using f2 by metis
  have f8: "ubMapStream f (v0_0 (nn (\<lambda>n. Rep_ubundle (ubMapStream f (v0_0 n))\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))) (\<lambda>n. f Rep_ubundle (v0_0 n)\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))))) . cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)) = Rep_ubundle (ubMapStream f (v0_0 (nn (\<lambda>n. Rep_ubundle (ubMapStream f (v0_0 n))\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))) (\<lambda>n. f Rep_ubundle (v0_0 n)\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))))))\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))"
    by (meson ubgetch_insert)
  have f9: "v0_0 (nn (\<lambda>n. Rep_ubundle (ubMapStream f (v0_0 n))\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))) (\<lambda>n. f Rep_ubundle (v0_0 n)\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)))) . cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)) = Rep_ubundle (v0_0 (nn (\<lambda>n. Rep_ubundle (ubMapStream f (v0_0 n))\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))) (\<lambda>n. f Rep_ubundle (v0_0 n)\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)))))\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))"
    by (meson ubgetch_insert)
  have f10: "\<forall>f n. \<not> chain f \<or> dom (Rep_ubundle (f n::'a\<^sup>\<Omega>)) = dom (Rep_ubundle (Lub f))"
    using ubrep_chain_lub_dom_eq by blast
  have f11: "UBundle.ubDom\<cdot>(ubMapStream f (Lub v0_0)) = UBundle.ubDom\<cdot>(Lub v0_0)"
    using f6 f2 by metis
  have f12: "UBundle.ubDom\<cdot> (ubMapStream f (v0_0 (v2_2 (\<lambda>n. ubMapStream f (v0_0 n)) v0_0))) = UBundle.ubDom\<cdot>(v0_0 (v2_2 (\<lambda>n. ubMapStream f (v0_0 n)) v0_0))"
    using f6 f2 by metis
  { assume "UBundle.ubDom\<cdot>(ubMapStream f (Lub v0_0)) = UBundle.ubDom\<cdot>(\<Squnion>n. ubMapStream f (v0_0 n))"
    moreover
    { assume "cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)) \<in> UBundle.ubDom\<cdot>(ubMapStream f (Lub v0_0)) \<and> ubMapStream f (Lub v0_0) . cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)) \<notsqsubseteq> (\<Squnion>n. ubMapStream f (v0_0 n)) . cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))"
      moreover
      { assume "(cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)) \<in> UBundle.ubDom\<cdot>(ubMapStream f (Lub v0_0)) \<and> ubMapStream f (Lub v0_0) . cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)) \<notsqsubseteq> (\<Squnion>n. ubMapStream f (v0_0 n)) . cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))) \<and> ubMapStream f (v0_0 (nn (\<lambda>n. Rep_ubundle (ubMapStream f (v0_0 n))\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))) (\<lambda>n. f Rep_ubundle (v0_0 n)\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))))) . cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)) = f (v0_0 (nn (\<lambda>n. Rep_ubundle (ubMapStream f (v0_0 n))\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))) (\<lambda>n. f Rep_ubundle (v0_0 n)\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)))) . cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)))"
        then have "(cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)) \<in> UBundle.ubDom\<cdot>(ubMapStream f (Lub v0_0)) \<and> ubMapStream f (Lub v0_0) . cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)) \<notsqsubseteq> (\<Squnion>n. ubMapStream f (v0_0 n)) . cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))) \<and> (\<Squnion>n. f Rep_ubundle (v0_0 n)\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))) = (\<Squnion>n. Rep_ubundle (ubMapStream f (v0_0 n))\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)))"
          using f9 f8 f4 by metis
        moreover
        { assume "(cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)) \<in> UBundle.ubDom\<cdot>(ubMapStream f (Lub v0_0)) \<and> ubMapStream f (Lub v0_0) . cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0)) \<notsqsubseteq> (\<Squnion>n. ubMapStream f (v0_0 n)) . cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))) \<and> (\<Squnion>n. f Rep_ubundle (v0_0 n)\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))) \<noteq> ubMapStream f (Lub v0_0) . cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))"
          moreover
          { assume "(\<Squnion>n. Rep_ubundle (v0_0 n)\<rightharpoonup>cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))) \<noteq> Lub v0_0 . cc (\<Squnion>n. ubMapStream f (v0_0 n)) (ubMapStream f (Lub v0_0))"
            then have "\<not> chain v0_0 \<or> ubMapStream f (Lub v0_0) \<sqsubseteq> (\<Squnion>n. ubMapStream f (v0_0 n))"
              by (metis ubgetch_insert ubrep_lub_eval) }
          ultimately have "\<not> chain v0_0 \<or> ubMapStream f (Lub v0_0) \<sqsubseteq> (\<Squnion>n. ubMapStream f (v0_0 n))"
            using f7 f5 f2 by (metis assms(1) ubMapStream_ubGetCh ubrep_chain_the) }
        ultimately have "chain (\<lambda>n. ubMapStream f (v0_0 n)) \<longrightarrow> \<not> chain v0_0 \<or> ubMapStream f (Lub v0_0) \<sqsubseteq> (\<Squnion>n. ubMapStream f (v0_0 n))"
          by (metis not_below2not_eq ubgetch_insert ubrep_lub_eval) }
      ultimately have "chain (\<lambda>n. ubMapStream f (v0_0 n)) \<longrightarrow> \<not> chain v0_0 \<or> ubMapStream f (Lub v0_0) \<sqsubseteq> (\<Squnion>n. ubMapStream f (v0_0 n))"
        using f7 f3 by force }
    ultimately have "chain (\<lambda>n. ubMapStream f (v0_0 n)) \<longrightarrow> \<not> chain v0_0 \<or> ubMapStream f (Lub v0_0) \<sqsubseteq> (\<Squnion>n. ubMapStream f (v0_0 n))"
      using f1 by (meson ub_below) }
  moreover
  { assume "ubMapStream f (v0_0 (v2_2 (\<lambda>n. ubMapStream f (v0_0 n)) v0_0)) = ubMapStream f (v0_0 (v2_2 (\<lambda>n. ubMapStream f (v0_0 n)) v0_0)) \<and> UBundle.ubDom\<cdot>(ubMapStream f (Lub v0_0)) \<noteq> UBundle.ubDom\<cdot>(\<Squnion>n. ubMapStream f (v0_0 n))"
    then have "dom (Rep_ubundle (ubMapStream f (v0_0 (v2_2 (\<lambda>n. ubMapStream f (v0_0 n)) v0_0)))) \<noteq> dom (Rep_ubundle (\<Squnion>n. ubMapStream f (v0_0 n))) \<or> UBundle.ubDom\<cdot>(ubMapStream f (Lub v0_0)) \<noteq> dom (Rep_ubundle (ubMapStream f (v0_0 (v2_2 (\<lambda>n. ubMapStream f (v0_0 n)) v0_0))))"
      by (simp add: ubdom_insert)
    moreover
    { assume "UBundle.ubDom\<cdot>(ubMapStream f (Lub v0_0)) \<noteq> dom (Rep_ubundle (ubMapStream f (v0_0 (v2_2 (\<lambda>n. ubMapStream f (v0_0 n)) v0_0))))"
      then have "dom (Rep_ubundle (v0_0 (v2_2 (\<lambda>n. ubMapStream f (v0_0 n)) v0_0))) \<noteq> dom (Rep_ubundle (Lub v0_0))"
        using f12 f11 by (simp add: ubdom_insert)
      then have "\<not> chain v0_0 \<or> ubMapStream f (Lub v0_0) \<sqsubseteq> (\<Squnion>n. ubMapStream f (v0_0 n))"
        using f10 by metis }
    ultimately have "chain (\<lambda>n. ubMapStream f (v0_0 n)) \<longrightarrow> \<not> chain v0_0 \<or> ubMapStream f (Lub v0_0) \<sqsubseteq> (\<Squnion>n. ubMapStream f (v0_0 n))"
      using f10 by blast }
  ultimately have "chain (\<lambda>n. ubMapStream f (v0_0 n)) \<longrightarrow> \<not> chain v0_0 \<or> ubMapStream f (Lub v0_0) \<sqsubseteq> (\<Squnion>n. ubMapStream f (v0_0 n))"
    by blast
  then have f13: "\<not> chain v0_0 \<or> ubMapStream f (Lub v0_0) \<sqsubseteq> (\<Squnion>n. ubMapStream f (v0_0 n))"
    by (meson \<open>monofun (ubMapStream (f::'a \<Rightarrow> 'a))\<close> monofun_def po_class.chain_def)
  obtain uu :: "nat \<Rightarrow> 'a\<^sup>\<Omega>" where
    "(\<exists>v0. chain v0 \<and> ubMapStream f (Lub v0) \<notsqsubseteq> (\<Squnion>uua. ubMapStream f (v0 uua))) = (chain uu \<and> ubMapStream f (Lub uu) \<notsqsubseteq> (\<Squnion>uua. ubMapStream f (uu uua)))"
    by moura
  then show ?thesis
    using f13 by blast
qed
*)


(****************************************************)
section\<open>Instantiation\<close>
(****************************************************) 


instantiation ubundle :: (uscl) ubcl
begin
definition ubDom_ubundle_def: "UnivClasses.ubDom \<equiv> ubDom"

definition ubLen_ubundle_def: "UnivClasses.ubLen \<equiv> ubLen"

instance
  apply intro_classes
  sorry

end


end