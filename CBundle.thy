(*  Title:        UnivClasses
    Author:       Sebastian, Jens, Marc

    Description:  All "Universal Classes". Later used to define bundles/pfun 
*)

theory CBundle
  imports UnivClasses
begin

(****************************************************)
section\<open>Data type\<close>
(****************************************************)  
  
  
definition cbWell :: "(channel \<rightharpoonup> ('s::us)) \<Rightarrow> bool" where
"cbWell f \<equiv> \<forall>c \<in> (dom f). (usOkay c (f\<rightharpoonup>c))" 

lemma cbWell_empty: "cbWell empty"
  by(simp add: cbWell_def)

lemma cbWell_adm: "adm cbWell"
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
        using usokay_adm adm_def by (metis (mono_tags, lifting) f0 part_the_chain part_the_lub)
    qed
    show "(\<forall>i. \<forall>c\<in>dom (Y i). usOkay c Y i\<rightharpoonup>c) \<longrightarrow> (\<forall>c\<in>dom (Lub Y). usOkay c Lub Y\<rightharpoonup>c)"
      by (simp add: f1 f2)
  qed
  then show ?thesis
    by(simp add: adm_def cbWell_def)
qed

cpodef 's::us cbundle ("(_\<^sup>\<omega>)" [1000] 999) = "{b :: channel \<rightharpoonup> 's . cbWell b}"
  using cbWell_empty apply auto[1]
  using cbWell_adm by auto


setup_lifting type_definition_cbundle


(****************************************************)
section\<open>Definitions\<close>
(****************************************************)


default_sort us

(* This function can be used in "'m stream USB" and "'m tstream USB" *)
(* and by the way, look at the "'m\<^sup>\<omega>" shorcode for 'm USB *)
definition cbDom :: "'m\<^sup>\<omega> \<rightarrow> channel set" where
"cbDom \<equiv> \<Lambda> b. dom (Rep_cbundle b)"

definition cbRestrict:: "channel set \<Rightarrow> 'm cbundle \<rightarrow> 'm cbundle" where
"cbRestrict cs  \<equiv> \<Lambda> b. Abs_cbundle (Rep_cbundle b |` cs)"

definition cbGetCh :: "channel \<Rightarrow> 'm cbundle \<rightarrow> 'm"  where
"cbGetCh c = (\<Lambda> b. ((Rep_cbundle b) \<rightharpoonup> c))"

definition cbLeast :: "channel set \<Rightarrow> 'm cbundle"  where
"cbLeast cs \<equiv> Abs_cbundle (\<lambda>c. (c \<in> cs) \<leadsto> \<bottom> )"

(* Interesting function, uses the "len" operator over 'm *)
definition cbLen:: " 'm cbundle \<Rightarrow> lnat " where
"cbLen b \<equiv> if cbDom\<cdot>b \<noteq> {} then (LEAST ln. ln\<in>{(usLen\<cdot>(cbGetCh c\<cdot>b)) | c. c \<in> cbDom\<cdot>b}) else \<infinity>"  

(* Thats an easy converter. For example from "tstream USB" to "stream USB" *)
(* Can also be cont *)
definition cbShift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a cbundle \<Rightarrow> 'b cbundle" where
"cbShift f sb = Abs_cbundle (\<lambda>c. ((c\<in>cbDom\<cdot>sb) \<leadsto> f (cbGetCh c\<cdot>sb)))"


(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)

  
end