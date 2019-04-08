(*  Title:        UBundle
    Author:       Sebastian, Jens, Marc

    Description:  Defines stream bundles
*)

theory UBundle
  imports inc.UnivClasses inc.Channel inc.OptionCpo
begin

  
default_sort uscl

  
(****************************************************)
section\<open>Data type\<close>
(****************************************************)  
  
  
definition ubWell :: "(channel \<rightharpoonup> ('s::uscl)) \<Rightarrow> bool" where
"ubWell f \<equiv> \<forall>c \<in> (dom f). (usclOkay c (f\<rightharpoonup>c))" 

lemma ubWell_empty: "ubWell Map.empty"
  by(simp add: ubWell_def)

lemma ubWell_adm: "adm ubWell"
proof - 
  have "\<And>(Y :: nat \<Rightarrow> (channel \<Rightarrow> 'a option)). chain Y \<Longrightarrow> (\<forall>i. \<forall>c\<in>dom (Y i). usclOkay c Y i\<rightharpoonup>c) \<longrightarrow> (\<forall>c\<in>dom (Lub Y). usclOkay c Lub Y\<rightharpoonup>c)"  
  proof -
    fix Y :: "nat \<Rightarrow> (channel \<Rightarrow> 'a option)"
    assume f0: "chain Y"
    have f1: "\<forall>i. dom (Y i) = dom (Lub Y)"
      using f0 part_dom_lub by blast
    have f2: "\<And>c. c\<in>dom (Lub Y) \<Longrightarrow> (\<forall>i. usclOkay c Y i\<rightharpoonup>c) \<longrightarrow> (usclOkay c Lub Y\<rightharpoonup>c)"
    proof - 
      fix c
      assume "c\<in>dom (Lub Y)"
      show "(\<forall>i. usclOkay c Y i\<rightharpoonup>c) \<longrightarrow> (usclOkay c Lub Y\<rightharpoonup>c)"
        using usclOkay_adm adm_def by (metis (mono_tags, lifting) f0 part_the_chain part_the_lub)
    qed
    show "(\<forall>i. \<forall>c\<in>dom (Y i). usclOkay c Y i\<rightharpoonup>c) \<longrightarrow> (\<forall>c\<in>dom (Lub Y). usclOkay c Lub Y\<rightharpoonup>c)"
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
"ubLen b \<equiv> if ubDom\<cdot>b \<noteq> {} then (LEAST ln. ln\<in>{(usclLen\<cdot>(b . c)) | c. c \<in> ubDom\<cdot>b}) else \<infinity>"  


text {* @{text "ubShift"}  the channel-domains are merged . Thats an easy converter. For example from "tstream USB" to "stream USB" *}
(* Can also be cont *)
definition ubShift :: "('A \<Rightarrow> 'B) \<Rightarrow> 'A\<^sup>\<Omega> \<Rightarrow> 'B\<^sup>\<Omega>" where
"ubShift f ub = Abs_ubundle (\<lambda>c. ((c\<in>ubDom\<cdot>ub) \<leadsto> f (ub . c)))"


text {* @{text "ubUnion"}  the channel-domains are merged *}
definition ubUnion :: "'M\<^sup>\<Omega> \<rightarrow> 'M\<^sup>\<Omega> \<rightarrow> 'M\<^sup>\<Omega>"  where 
"ubUnion \<equiv> \<Lambda> ub1 ub2 . Abs_ubundle ((Rep_ubundle ub1) ++ (Rep_ubundle ub2))"


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


text {* @{text "UB"} is the set of bundles over a channel signature}*}
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

lemma cont_Abs_UB[simp]: assumes "cont g" and "\<forall>x. ubWell (g x)"
  shows "cont (\<lambda>x. Abs_ubundle (g x))"
  by (simp add: assms(1) assms(2) cont_Abs_ubundle)

lemma ubabs_lub[simp]: assumes "chain Y" and "\<And> i. ubWell (Y i)"
  shows "(\<Squnion> i. Abs_ubundle (Y i)) = Abs_ubundle (\<Squnion> i. Y i)"
proof -
  have f0: "ubWell (\<Squnion> i. Y i)"
    using adm_def assms(1) assms(2) ubWell_adm by blast
  have f1: "chain (\<lambda> i. Abs_ubundle (Y i))"
    apply (rule chainI)
    by (simp add: assms(1) assms(2) below_ubundle_def po_class.chainE)
  have f2: "Rep_ubundle (\<Squnion> i. Abs_ubundle (Y i)) = Rep_ubundle (Abs_ubundle (\<Squnion> i. Y i))"
    by (metis (mono_tags, lifting) assms(2) f1 lub_eq lub_ubundle ubrep_ubabs)
  show ?thesis
    by (metis f2 ubabs_ubrep)
qed

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
  apply (rule contI2)
  apply (meson below_ubundle_def monofunI)
  by (simp add: ubrep_lub)

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

(* if the function is ubWell then each element in the stream is usclOkay  *)
lemma [simp]: assumes "ubWell f" and "c \<in> dom f"
  shows "usclOkay c (f\<rightharpoonup>c)"
  using assms(1) assms(2) ubWell_def by auto

(* if each element in the stream is usclOkay then the function is ubWell  *)
lemma ubwellI: assumes "\<And> c. c \<in> dom f \<Longrightarrow> usclOkay c (f\<rightharpoonup>c)"
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
  apply (rule contI2)
   apply (rule monofunI)
   apply (simp add: below_ubundle_def part_dom_eq)
  by (simp add: ubrep_chain_lub_dom_eq)


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

lemma ubdom_lub2: assumes "chain Y"
  shows "ubDom\<cdot>(\<Squnion> i. Y i) = (\<Squnion> i. ubDom\<cdot>(Y i))"
  using assms by auto

lemma ubdom_channel_usokay[simp]: assumes "c \<in> ubDom\<cdot>ub"
  shows "usclOkay c ((Rep_ubundle ub)\<rightharpoonup>c)"
  using assms ubrep_well ubdom_insert ubWell_def by blast

lemma ubdom_empty [simp]: "ubDom\<cdot>(Abs_ubundle Map.empty) = {}"
  by (simp add: ubWell_empty ubdom_ubrep_eq)
    
subsection \<open>ubGetCh\<close>

  
(* ubGetCh is cont *)
lemma ubgetch_cont [simp]: "cont (\<lambda>ub. ((Rep_ubundle ub) \<rightharpoonup> c))"
  apply (rule contI2)
   apply (metis (no_types, lifting) below_ubundle_def fun_belowD monofun_def op_the_mono)
  by (simp add: ubrep_lub_eval)

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

lemma ubgetch_below2: assumes "x \<sqsubseteq> y"
  shows "x . c \<sqsubseteq> y . c"
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
proof (rule ubgetchI)
  have f1: "ubWell (\<lambda>c. (c \<in> ubDom\<cdot>b)\<leadsto> b . c)"
    by (simp add: ubWell_def ubgetch_insert)
  show dom_eq: "ubDom\<cdot>(Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>b)\<leadsto>b  .  c)) = ubDom\<cdot>b"
    by (simp add: f1 ubdom_ubrep_eq)
  show "\<And>c::channel. c \<in> ubDom\<cdot>(Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>b)\<leadsto>b  .  c)) \<Longrightarrow> Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>b)\<leadsto>b  .  c)  .  c = b  .  c"
  proof -
    fix c::channel
    assume assm1: "c \<in> ubDom\<cdot>(Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>b)\<leadsto>b  .  c))"
    have f2: "c \<in> ubDom\<cdot>b"
      using assm1 dom_eq by auto
    show "Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>b)\<leadsto>b  .  c)  .  c = b  .  c"
      by (simp add: f1 f2 ubgetch_insert)
  qed
qed

    
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
proof (rule contI2, auto)
  fix Y::"nat \<Rightarrow> 'a\<^sup>\<Omega>"
  assume chain_Y: "chain Y"
  have f00: " chain (\<lambda>(a::nat) b::channel. if b \<in> cs then Rep_ubundle (Y a) b else None)"
    apply (rule chainI)
    apply (simp add: fun_below_iff)
    by (metis below_ubundle_def chain_Y chain_mono_less fun_below_iff lessI)
  have f1: "\<And> x. (\<Squnion>i::nat. (\<lambda>x::channel. if x \<in> cs then Rep_ubundle (Y i) x else None)) x =
                (\<Squnion>i::nat. (\<lambda>x::channel. if x \<in> cs then Rep_ubundle (Y i) x else None) x)"      
    using f00 lub_fun by fastforce
  show "Rep_ubundle (\<Squnion>i::nat. Y i) |` cs \<sqsubseteq> (\<Squnion>i::nat. Rep_ubundle (Y i) |` cs)"
    apply (simp add: restrict_map_def)
    apply (simp add: fun_below_iff, auto)
    by (subst f1, simp add: chain_Y cont2contlubE lub_fun) +
qed


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

lemma ubrestrict_id [simp]: assumes "ubDom\<cdot>ub \<subseteq> cs" shows "ubRestrict cs\<cdot>ub = ub"
  by (metis (mono_tags, lifting) assms contra_subsetD inf.absorb_iff1 ubgetchI ubgetch_ubrestrict ubrestrict_ubdom2)

lemma ubrestrict_ubdom_sub: assumes "ubDom\<cdot>ub \<subseteq> cs"
  shows "ub \<bar> cs = ub \<bar> (ubDom\<cdot>ub)"
  by (simp add: assms)
    
lemma ubrestrict_ubdom_sup_inter: 
  shows "ub \<bar> cs = ub \<bar> (cs \<inter> (ubDom\<cdot>ub))"
  by (metis (no_types, hide_lams) Int_commute inf_le2 ubrestrict_ubdom2 ubrestrict_id ubRestrict_twice)

lemma ubrestrict_below [simp]:  assumes "chain Y" and "cont h"
      shows "(h (\<Squnion>i. Y i) \<bar> g (ubDom\<cdot>(\<Squnion>i. Y i))) \<sqsubseteq> (\<Squnion>i. (h (Y i) \<bar> g (ubDom\<cdot>(Y i)) ))"
proof -
  have f0: "(ubDom\<cdot>(\<Squnion>i. Y i)) = (\<Squnion> i. ubDom\<cdot>(Y i))"
    using assms(1) by auto
  have f1: "g (ubDom\<cdot>(\<Squnion>i. Y i)) = (\<Squnion>i. g (ubDom\<cdot>(Y i)))"
    by (simp add: assms(1))
  have f2: " cont (\<lambda>a. h a \<bar> g (ubDom\<cdot>a))"
    apply (rule contI2)
    apply (rule monofunI)
     apply (simp add: assms(2) cont2monofunE ubdom_below, auto)
    by (metis assms(2) below_refl ch2ch_cont cont2contlubE contlub_cfun_arg)
  then show ?thesis             
    using assms(1) cont2contlubE eq_imp_below by blast
qed

lemma ubrestrict_lub: assumes "chain Y"
  shows "(\<Squnion>i. Y i) \<bar> cs = (\<Squnion>i. (Y i) \<bar> cs)"
  using assms contlub_cfun_arg by auto

lemma ubRestrict_ubGetCh: 
  assumes "{c} \<subseteq> ubDom\<cdot>ub"
  shows "(ubRestrict {c}\<cdot>ub) . c = (ub . c)"
  by simp

subsection \<open>ubLen\<close>
lemma ublen_monofun:"monofun ubLen"
proof (rule monofunI)
  fix x::"'a\<^sup>\<Omega>" and y::"'a\<^sup>\<Omega>"
  assume a1: "x \<sqsubseteq> y"
  show "ubLen x \<sqsubseteq> ubLen y"
  proof (cases "ubDom\<cdot>x = {}")
    case True
    then show ?thesis 
      by (metis a1 eq_imp_below ubLen_def ubdom_below)
  next
    case False
      obtain y_len_set where y_len_set_def: "y_len_set = {usclLen\<cdot>(y . c) | c.  c \<in> ubDom\<cdot>y}" 
        by simp
      have f2: "(LEAST ln. ln\<in> y_len_set) = ubLen y"
      proof -
        have "UBundle.ubDom\<cdot>y \<noteq> {}"
          by (metis (no_types) False a1 empty_iff ubdom_below ubgetchI)
        then show ?thesis
          by (simp add: ubLen_def y_len_set_def)
      qed
      have f7: "y_len_set \<noteq> {}"
      proof - 
        obtain c where "c \<in> ubDom\<cdot>y" 
          using False a1 ubdom_below by blast
        then have "usclLen\<cdot>(y . c) \<in> y_len_set"
          using y_len_set_def by blast
        then show ?thesis
          by auto
      qed
      have f8: "(LEAST ln. ln\<in> y_len_set) \<in> y_len_set"
        by (meson LeastI f7 neq_emptyD)
      obtain y_ln where y_ln_def: "y_ln = (LEAST ln. ln\<in> y_len_set)" by simp
      have f9: "\<forall> len \<in> y_len_set. \<exists> c \<in> ubDom\<cdot>y. usclLen\<cdot>(y . c) = len"  
        using y_len_set_def by blast
      then have f10: "y_ln \<in> y_len_set \<and> (\<exists> c \<in> ubDom\<cdot>y. usclLen\<cdot>(y . c) = y_ln)"
        apply rule
        by (simp add: f8 y_ln_def) +
      then obtain y_c where y_c_def: "y_c \<in> ubDom\<cdot>y \<and> usclLen\<cdot>(y . y_c) = (LEAST ln. ln\<in> y_len_set)"
        using y_ln_def by blast
      have f11: "ubLen x \<sqsubseteq> usclLen\<cdot>(x . y_c)"
      proof -
        have "\<exists>c. usclLen\<cdot>(x . y_c) = usclLen\<cdot>(x . c) \<and> c \<in> UBundle.ubDom\<cdot>x"
          using a1 ubdom_below y_c_def by blast
        then show ?thesis
          by (simp add: False Least_le ubLen_def)
      qed
      have "x . y_c \<sqsubseteq> y . y_c"
        by (simp add: a1 monofun_cfun_arg)
      then have "usclLen\<cdot>(x . y_c) \<sqsubseteq> usclLen\<cdot>(y . y_c)"
        using monofun_cfun_arg by blast
      then show ?thesis
        using f11 f2 y_c_def by auto
    qed
  qed

lemma ublen_least_in_set: assumes "ubDom\<cdot>tb \<noteq> {}"
  shows "(LEAST ln. ln\<in>{(usclLen\<cdot>(tb. c)) | c. c \<in> ubDom\<cdot>tb}) \<in> {(usclLen\<cdot>(tb. c)) | c. c \<in> ubDom\<cdot>tb}"
  by (metis (mono_tags, lifting) LeastI all_not_in_conv assms mem_Collect_eq)
    
lemma ublen_min_on_channel: assumes "ubDom\<cdot>tb \<noteq> {}"
  shows "\<exists> c \<in> ubDom\<cdot>tb. (usclLen\<cdot>(tb. c)) = (LEAST ln. ln\<in>{(usclLen\<cdot>(tb. c)) | c. c \<in> ubDom\<cdot>tb})"
proof -
  obtain least where least_def: "least = (LEAST ln. ln\<in>{(usclLen\<cdot>(tb. c)) | c. c \<in> ubDom\<cdot>tb})"
    by simp
  have f1: "least \<in> {(usclLen\<cdot>(tb. c)) | c. c \<in> ubDom\<cdot>tb}"
    using assms least_def ublen_least_in_set by blast
  show ?thesis
    using f1 least_def by blast
qed

lemma uslen_ubLen_ch1: assumes "ubWell [ch \<mapsto> s]"
  shows "ubLen (Abs_ubundle [ch \<mapsto> s]) = usclLen\<cdot>s"
proof -
  
  have f1: "{ch} = ubDom\<cdot>(Abs_ubundle [ch \<mapsto> s])"
    by (simp add: assms ubdom_ubrep_eq)
  show ?thesis
    by (metis (no_types, lifting) assms f1 fun_upd_same insert_not_empty option.sel 
        singletonD ubLen_def ubgetch_ubrep_eq ublen_min_on_channel)
qed

lemma uslen_ubLen_ch2: assumes "ubWell [ch \<mapsto> s]"
  shows "ubLen (Abs_ubundle [ch \<mapsto> s]) = usclLen\<cdot>((Abs_ubundle [ch \<mapsto> s]) . ch)"
  by (simp add: assms ubgetch_insert uslen_ubLen_ch1)

lemma uslen_ubLen_ch3: assumes "ubDom\<cdot>b = {ch}"
  shows "ubLen b = usclLen\<cdot>(b . ch)"
  by (metis (mono_tags, lifting) assms insert_not_empty singletonD ubLen_def ublen_min_on_channel)

lemma ubLen_geI: assumes "\<forall> c \<in> ubDom\<cdot>tb. n \<le> usclLen\<cdot>(tb . c)"
  shows "n \<le> ubLen tb"
  by (metis (no_types, lifting) assms inf_ub ubLen_def ublen_min_on_channel)

lemma ubLen_geI2: assumes "\<forall> c \<in> ubDom\<cdot>tb. (Fin n) < usclLen\<cdot>(tb . c)"
  shows "(Fin n) < ubLen tb"
  using ubLen_geI assms
  using less_le lnsuc_lnle_emb ubLen_def ublen_min_on_channel
  by (metis (no_types, lifting) notinfI3)

lemma ublen_channel[simp]: "\<And>c. c\<in>ubDom\<cdot>ub \<Longrightarrow> ubLen ub \<le> usclLen\<cdot>(ub . c)"
proof -
fix c :: channel
assume a1: "c \<in> ubDom\<cdot>ub"
then have f2: "ubDom\<cdot>ub \<noteq> {}"
by blast
  have "\<exists>ca. usclLen\<cdot>(ub . c) = usclLen\<cdot>(ub . ca) \<and> ca \<in> ubDom\<cdot>ub"
using a1 by blast
  then show "ubLen ub \<le> usclLen\<cdot>(ub . c)"
using f2 by (simp add: ubLen_def wellorder_Least_lemma(2))
qed

lemma ublen_not_0: assumes "ubLen ub \<noteq> 0" and "c\<in>ubDom\<cdot>ub"
  shows "usclLen\<cdot>(ub . c) \<noteq> 0"
  using assms(1) assms(2) ublen_channel by fastforce

lemma ubLen_min: assumes "ubDom\<cdot>ub \<noteq> {}" and "finite (ubDom\<cdot>ub)"
  shows "ubLen ub = Min {usclLen\<cdot>(ub . c) | c. c \<in> ubDom\<cdot>ub}"
proof-
  have uscllen_ub_set_fin: "finite {usclLen\<cdot>(ub . c) | c. c \<in> ubDom\<cdot>ub}"
    by (simp add: assms(2) Setcompr_eq_image)
  have uscllen_set_nempty: "{usclLen\<cdot>(ub . c) | c. c \<in> ubDom\<cdot>ub} \<noteq> {}"
    using assms(1) by blast
  have "ubLen ub = (LEAST ln. \<exists>c. ln = usclLen\<cdot>(ub  .  c) \<and> c \<in> ubDom\<cdot>ub)"
    by (simp add: assms ubLen_def)
  thus ?thesis
    using Least_Min uscllen_ub_set_fin uscllen_set_nempty by fastforce
qed

lemma ubrestrict_ublen: "ubLen ub \<le> ubLen (ubRestrict cs\<cdot>ub)"
proof -
  have " ubDom\<cdot>(ubRestrict cs\<cdot>ub)\<subseteq> ubDom\<cdot>ub "
    by simp
  then have "\<And>c. c\<in>ubDom\<cdot>(ubRestrict cs\<cdot>ub) \<Longrightarrow> ubLen ub \<le> usclLen\<cdot>((ubRestrict cs\<cdot>ub) . c)"
    by simp
  then show ?thesis
    by (simp add: ubLen_geI)
qed

(* Missing *)
  
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

lemma ubunion_insert: "(ubUnion\<cdot>b1\<cdot>b2) = Abs_ubundle (Rep_ubundle b1 ++ Rep_ubundle b2)"
  by (simp add: ubUnion_def)

lemma ubunion_idL [simp]: assumes "ubDom\<cdot>b1 \<subseteq> ubDom\<cdot>b2"
  shows "ubUnion\<cdot>b1\<cdot>b2 = b2"
  using assms apply (simp add: ubunion_insert)
  by (simp add: ubdom_insert)

lemma ubunion_commutative: assumes "ubDom\<cdot>b1 \<inter> ubDom\<cdot>b2 = {}"
  shows "ubUnion\<cdot>b1\<cdot>b2 = ubUnion\<cdot>b2\<cdot>b1"
  using assms apply (simp add: ubunion_insert)
  by (metis map_add_comm ubdom_insert)

lemma ubunion_associative: "ubUnion\<cdot>b1\<cdot>(ubUnion\<cdot>b2\<cdot>b3) = ubUnion\<cdot>(ubUnion\<cdot>b1\<cdot>b2)\<cdot>b3"
  by (simp add: ubunion_insert)

lemma ubunion_getchR [simp]: assumes "c \<in> ubDom\<cdot>b2"
  shows "ubUnion\<cdot>b1\<cdot>b2 . c = b2 . c"
  apply (simp add: ubunion_insert ubgetch_insert)
  by (metis assms map_add_find_right ubgetchE)

lemma ubunion_getchL [simp]: assumes "c \<notin> ubDom\<cdot>b2"
  shows "ubUnion\<cdot>b1\<cdot>b2 . c = b1 . c"
  apply (simp add: ubunion_insert ubgetch_insert)
  by (metis assms map_add_dom_app_simps(3) ubdom_insert)

lemma ubunionDom [simp]: "ubDom\<cdot>(ubUnion\<cdot>b1\<cdot>b2) = ubDom\<cdot>b1 \<union> ubDom\<cdot>b2"
  by (auto simp add: ubdom_insert ubunion_insert)

lemma ubunion_pref_eq: assumes "a \<sqsubseteq> b" and "c \<sqsubseteq> d"
  shows "ubUnion\<cdot>a\<cdot>c \<sqsubseteq> ubUnion\<cdot>b\<cdot>d"
  by (simp add: assms monofun_cfun)

lemma ubunion_pref_eq2: assumes "a \<sqsubseteq> b"
  shows "ubUnion\<cdot>x\<cdot>a \<sqsubseteq> ubUnion\<cdot>x\<cdot>b"
  by (metis assms monofun_cfun_arg)

lemma ubunion_assoc2: "ubUnion\<cdot>(ubUnion\<cdot>b1\<cdot>b2)\<cdot>b3 = ubUnion\<cdot>b1\<cdot>(ubUnion\<cdot>b2\<cdot>b3)"
  by (simp add: ubunion_associative)

lemma ubunion_eqI: assumes "a = b" and "c = d"
  shows "ubUnion\<cdot>a\<cdot>c = ubUnion\<cdot>b\<cdot>d"
  by (simp add: assms)


lemma ubunion_restrict [simp]: assumes "ubDom\<cdot>b2 = cs"
  shows "(ubUnion\<cdot>b1\<cdot>b2) \<bar> cs = b2"
  apply (simp add: ubunion_insert ubrestrict_insert)
  by (metis assms map_union_restrict2 ubabs_ubrep ubdom_insert)

lemma ubunion_restrict2 [simp]: assumes "ubDom\<cdot>b2 \<inter> cs = {}"
  shows "(ubUnion\<cdot>b1\<cdot>b2) \<bar> cs = b1 \<bar> cs" 
  apply (simp add: ubunion_insert ubrestrict_insert)
  by (metis assms map_union_restrict ubdom_insert)

lemma ubunion_ubrestrict3: "(ubUnion\<cdot>a\<cdot>b) \<bar> cs = ubUnion\<cdot>(a \<bar> cs)\<cdot>(b \<bar> cs)"
  apply (simp add: ubunion_insert ubrestrict_insert)
  by (metis mapadd2if_then restrict_map_def)

lemma ubunion_ubrestrict4:
  assumes " ubDom\<cdot>y \<subseteq> cs"
  and     "ubDom\<cdot>x \<inter> cs = {}"
shows     "ubRestrict cs\<cdot>(ubUnion\<cdot>x\<cdot>y) = ubRestrict cs\<cdot>y"
  by (metis (no_types, lifting) Int_commute Int_empty_right assms ubrestrict_id ubrestrict_ubdom2 
      ubrestrict_ubdom_sup_inter ubunion_restrict ubunion_ubrestrict3)

lemma ub_split_union: 
  assumes "ubDom\<cdot>ub \<subseteq> A \<union> B"
  shows   "ubUnion\<cdot>(ubRestrict A\<cdot>ub)\<cdot>(ubRestrict B\<cdot>ub) = ub"
  apply(rule ub_eq)
  using assms apply auto[1]
  by (metis Int_iff Un_iff ubgetch_ubrestrict ubrestrict_ubdom2 ubunionDom ubunion_getchL 
      ubunion_getchR)

lemma ubunion_ublen_le: 
  assumes "ubLen x \<le> ubLen z"
  shows   "ubLen x \<le> ubLen(ubUnion\<cdot>x\<cdot>z)"
  apply(rule ubLen_geI)
  by (metis Un_iff assms dual_order.trans ublen_channel ubunionDom ubunion_getchL ubunion_getchR)

lemma ubunion_len_le: 
  assumes "ubLen a \<le> ubLen b"
  and     "ubLen a \<le> ubLen c"
shows     "ubLen a \<le> ubLen (ubUnion\<cdot>b\<cdot>c)"
  apply(rule ubLen_geI, simp)
  by (metis Un_iff assms(1) assms(2) dual_order.trans ublen_channel ubunion_getchL ubunion_getchR)

lemma ubunion_len_l: 
  assumes "ubLen a <  ubLen b"
  and     "ubLen a < ubLen c"
shows "ubLen a < ubLen (ubUnion\<cdot>b\<cdot>c)"
  by (metis assms dual_order.strict_iff_order leD le_cases ubunion_len_le)

lemma ubunion_len_l2: 
  assumes "Fin n < ubLen b"
  and     "Fin n < ubLen c"
shows     "Fin n < ubLen (ubUnion\<cdot>b\<cdot>c)"
  by (meson assms dual_order.strict_iff_order leI order.strict_trans1 ubunion_len_l)

lemma ubunion_ubLen_min: 
   assumes "ubDom\<cdot>x \<inter> ubDom\<cdot>y = {}"
  shows   "ubLen (ubUnion\<cdot>x\<cdot>y) = Min {ubLen x, ubLen y}"
  by (metis (no_types) Min_insert Min_singleton assms finite.emptyI finite.insertI insert_not_empty 
      le_cases less2eq min_def ubrestrict_ublen ubunion_commutative ubunion_restrict ubunion_ublen_le)


subsection \<open>ubSetCh\<close>

  
lemma ubsetch_cont [simp]: "cont (\<lambda> ub. (\<lambda> c m. ubUnion\<cdot>ub\<cdot>(Abs_ubundle [c \<mapsto> m])))"
  by simp

lemma ubsetch_well [simp]: assumes "usclOkay c s"
  shows "ubWell ((Rep_ubundle b) (c \<mapsto> s))"
  by (metis
      assms dom_fun_upd fun_upd_apply insert_iff option.sel option.simps(3) ubrep_well ubWell_def)

lemma ubsetch_insert: assumes "usclOkay c s"
  shows "(ubSetCh\<cdot>b) c s = ubUnion\<cdot>b\<cdot>(Abs_ubundle [c \<mapsto> s])"
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


subsection \<open>ubRenameCh\<close>


(* a bundle with only one channel based on other bundel is ubWell  *)
lemma ubWell_single_channel: assumes "c \<in> ubDom\<cdot>ub" shows "ubWell [c \<mapsto> Rep_ubundle ub\<rightharpoonup>c]"
  by (metis (full_types) assms ubrep_ubabs ubsetch_well ubdom_channel_usokay ubWell_empty)

(* change a channel to itself returns the same bundle  *)
lemma ubrenamech_id: assumes "c \<in> ubDom\<cdot>ub"
  shows "ubRenameCh ub c c = ub"
  apply (simp add: ubRenameCh_def ubgetch_insert ubSetCh_def ubremch_insert ubrestrict_insert)
  apply (simp add: ubunion_insert)
  apply (subst ubrep_ubabs)
   apply (simp add: assms ubWell_single_channel)
  by (metis assms fun_upd_upd map_add_empty map_add_upd map_upd_triv restrict_complement_singleton_eq ubabs_ubrep ubgetchE ubgetch_insert)


(* the dom of new bundle after renaming a channel is the union between new channel and the dom of bundle without the renamed channel  *)
lemma ubrenamech_ubdom: assumes "ch1 \<in> ubDom\<cdot>ub"  and "usclOkay ch2 (ub . ch1)"
  shows "ubDom\<cdot>(ubRenameCh ub ch1 ch2) = (ubDom\<cdot>ub - {ch1}) \<union> {ch2}"
  apply (simp add: ubRenameCh_def  ubSetCh_def)
  by (metis assms(2) diff_eq dom_empty dom_fun_upd insert_is_Un option.simps(3) ubrep_ubabs sup_commute ubsetch_well ubdom_ubrep_eq ubWell_empty)

(* after renaming channel ch1 to ch2, old and new bundles have the same element on those channel  *)  
lemma ubrenamech_ubgetchI1: assumes "ch1 \<in> ubDom\<cdot>ub" 
                    and "usclOkay ch2 (ub . ch1)"
  shows "(ubRenameCh ub ch1 ch2) . ch2 = ub . ch1"
  apply (simp add: ubRenameCh_def  ubSetCh_def)
  apply (subst ubunion_getchR)
  apply (metis assms(2) dom_empty dom_fun_upd option.simps(3) ubrep_ubabs singletonI ubsetch_well ubdom_ubrep_eq ubWell_empty)
  by (metis assms(1) assms(2) fun_upd_same ubrep_ubabs ubsetch_well ubgetchE ubgetch_insert ubWell_empty)

(* renaming channel doesnt effect other channel in a bundle  *)           
lemma ubrenamech_ubgetchI2: assumes "ch1 \<in> ubDom\<cdot>ub"  and "usclOkay ch2 (ub . ch1)" and "ch3 \<in> ubDom\<cdot>ub" and "ch3 \<noteq> ch2" and "ch3 \<noteq> ch1"
  shows "(ubRenameCh ub ch1 ch2) . ch3 = ub . ch3"
  apply (simp add: ubRenameCh_def ubSetCh_def)
  by (metis ComplI assms(2) assms(4) assms(5) dom_empty dom_fun_upd option.discI ubrep_ubabs singletonD ubsetch_well ubdom_ubrep_eq ubgetch_ubrestrict ubunion_getchL ubWell_empty)


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


subsection \<open>ubMapStream\<close>


abbreviation fun_well_type :: "('M \<Rightarrow> 'M) \<Rightarrow> bool" where
"fun_well_type f \<equiv> (\<forall> cs s. (usclOkay cs s \<longrightarrow> usclOkay cs (f s)))"

lemma ubDom_funtype: assumes "\<forall>c ts. usclOkay c ts \<longrightarrow> usclOkay c (f ts)"
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
  show mono_proof: "monofun (ubMapStream f)"
  proof (rule monofunI)
    fix x::"'a\<^sup>\<Omega>" and y::"'a\<^sup>\<Omega>"
    assume x_below_y: "x \<sqsubseteq> y"
    show "ubMapStream f x \<sqsubseteq> ubMapStream f y"
      apply (rule ub_below)
       apply (simp add: assms(2) ubMapStream_ubDom ubdom_below x_below_y)
      by (metis (no_types, lifting) Abs_cfun_inverse2 assms(1) assms(2) monofun_Rep_cfun2 
              monofun_def ubMapStream_ubDom ubMapStream_ubGetCh ubdom_below x_below_y)
  qed
  thus "\<forall>Y. chain Y \<longrightarrow> ubMapStream f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. ubMapStream f (Y i))"
  proof auto
    fix Y:: "nat \<Rightarrow> 'a\<^sup>\<Omega>"
    assume chain_Y: "chain Y"
    have f00: "ubDom\<cdot>(ubMapStream f (\<Squnion>i::nat. Y i)) = ubDom\<cdot>(\<Squnion>i::nat. ubMapStream f (Y i))"
      by (metis (mono_tags, lifting) assms(2) chain_Y mono_proof monofunE po_class.chain_def ubMapStream_ubDom ubdom_chain_eq2)
    have f0: "\<forall> c \<in> ubDom\<cdot>(ubMapStream f (\<Squnion>i::nat. Y i)). 
                      ubMapStream f (\<Squnion>i::nat. Y i)  .  c = f ((\<Squnion>i::nat. Y i)  .  c)"
      using assms(2) ubMapStream_ubDom ubMapStream_ubGetCh by blast
    have f1: "\<forall> c \<in> ubDom\<cdot>(ubMapStream f (\<Squnion>i::nat. Y i)).
                  (\<Squnion>i::nat. ubMapStream f (Y i))  .  c = (\<Squnion>i::nat. ubMapStream f (Y i) . c)"
      by (simp add: ch2ch_monofun chain_Y contlub_cfun_arg mono_proof)
    have f2: "\<And> i. \<forall> c  \<in> ubDom\<cdot>(ubMapStream f (\<Squnion>i::nat. Y i)). 
                  ubMapStream f (Y i) . c = f ((Y i) . c)"
      by (simp add: assms(2) chain_Y ubMapStream_ubDom ubMapStream_ubGetCh)
    show "ubMapStream f (\<Squnion>i::nat. Y i) \<sqsubseteq> (\<Squnion>i::nat. ubMapStream f (Y i))"
      apply (rule ub_below)
       apply (simp add: f00)
      apply (subst f0, simp, subst f1, simp, subst f2, simp)
      by (simp add: assms(1) chain_Y cont2contlubE)
  qed
qed


lemma ubMapStream_contI2: assumes "cont f" and "\<forall>c ts. usclOkay c ts \<longrightarrow> usclOkay c (f ts)"
  shows "cont (ubMapStream f)"
  by (simp add: assms(1) assms(2) ubMapStream_contI1)

lemma if_then_ubDom: assumes "d \<in> dom (\<lambda> b. (ubDom\<cdot>b = In) \<leadsto> (F b))"
  shows "ubDom\<cdot>d = In"
  by (metis (mono_tags) assms domIff2)

(*
lemma ub_lub [simp]: fixes S :: "nat \<Rightarrow> 'm ubundle" assumes "chain S"
  shows "Abs_ubundle (\<lambda> c. (c \<in> ubDom\<cdot>(S i)) \<leadsto> (\<Squnion>j. (S j) . c)) = (\<Squnion>i. S i)" (is "?L = ?R")
proof (rule ub_eq)
  show "ubDom\<cdot>?L = ubDom\<cdot>?R"
    sorry
  fix c
  assume "c \<in> ubDom\<cdot>?L"
  show "?L . c = ?R . c"
  proof -
    have "?R . c = (\<Squnion>i. (S i) . c)"
      using assms contlub_cfun_arg by blast
    thus ?thesis
      sorry
  qed
qed
*)

lemma usclLen_all_channel_bigger: assumes "cLen \<in> ubDom\<cdot>b \<and> ubLen b = usclLen\<cdot>(b  .  cLen)" shows "\<And>c::channel. c \<in> ubDom\<cdot>b \<Longrightarrow> usclLen\<cdot>(b  .  cLen) \<le> usclLen\<cdot>(b  .  c)"
proof -
  fix c
  assume a1: "c \<in> ubDom\<cdot>b"
  then have "ubDom\<cdot>b \<noteq> {}"
    by force
  then have f2: "ubLen b = (LEAST l. l \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b})"
    by (simp add: ubLen_def)
  have "\<exists>ca. usclLen\<cdot>(b . c) = usclLen\<cdot>(b . ca) \<and> ca \<in> ubDom\<cdot>b"
    using a1 by auto
  then have "(LEAST l. l \<in> {usclLen\<cdot>(b . c) |c. c \<in> ubDom\<cdot>b}) \<le> usclLen\<cdot>(b . c)"
    by (simp add: Least_le)
  then show "c \<in> ubDom\<cdot>b \<Longrightarrow> usclLen\<cdot>(b  .  cLen) \<le> usclLen\<cdot>(b  .  c)"
    using f2 assms by simp
qed

lemma ubLen_smallereq_all: "\<And> c . c \<in> ubDom\<cdot>ub \<Longrightarrow> ubLen ub \<le> usclLen\<cdot>(ub . c)"
proof -
  fix c
  assume cindom: "c \<in> ubDom\<cdot>ub"
  show "ubLen ub \<le> usclLen\<cdot>(ub . c)"
    by (metis (no_types, lifting) cindom empty_iff ubLen_def ublen_min_on_channel usclLen_all_channel_bigger)
qed

subsection \<open>More general lemmas\<close>

lemma ub_id_single: "ubDom\<cdot>ub = {c} \<Longrightarrow> Abs_ubundle [c \<mapsto> ub  .  c] = ub"
  apply(rule ub_eq)
  apply simp
  by (simp add: ubWell_single_channel ubdom_ubrep_eq ubgetch_insert)+


(****************************************************)
section\<open>Instantiation\<close>
(****************************************************) 


instantiation ubundle :: (uscl) ubcl
begin
definition ubclDom_ubundle_def [simp]: "ubclDom \<equiv> ubDom"
definition ubclLen_ubundle_def: "ubclLen \<equiv> ubLen"

lemma ubundle_ex: "\<And>C::channel set. \<exists>x::'a\<^sup>\<Omega>. ubclDom\<cdot>x = C"
proof -
  fix C::"channel set"
  obtain set_bla::"'a set" where set_bla_def: "set_bla = {a . \<exists> c \<in> C. usclOkay c a}"
    by simp
  obtain ub where ub_def: "ub = (\<lambda> c. (c \<in> C) \<leadsto> (SOME a. a \<in> set_bla \<and> usclOkay c a))"
    by simp
  have "ubWell ub"
    apply (simp add: ubWell_def)
    by (metis (mono_tags, lifting) usclOkay_ex domIff mem_Collect_eq option.sel set_bla_def tfl_some ub_def)
  then show "\<exists>x::'a\<^sup>\<Omega>. ubclDom\<cdot>x = C"
    using ubclDom_ubundle_def ub_def ubdom_ubrep_eq by fastforce
qed

instance
  apply intro_classes
     apply (simp add:  ubdom_below)
    apply (simp add: ubundle_ex)
  using ubundle_ex apply auto[1]
   apply (simp add: ubclLen_ubundle_def ublen_monofun)
  by (metis (mono_tags) domIff empty_iff equalityI subsetI ubLen_def ubclLen_ubundle_def ubWell_empty ubdom_ubrep_eq)

end


end