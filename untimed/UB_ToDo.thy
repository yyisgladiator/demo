theory UB_ToDo
imports "../UBundle" Streams

begin
default_sort uscl

(* marcs job *)
definition ubConc :: "'m ubundle \<Rightarrow> 'm ubundle \<rightarrow> 'm ubundle" where
"ubConc sb1 \<equiv>undefined "

definition ubConcEq:: "'m ubundle \<Rightarrow> 'm ubundle \<rightarrow> 'm ubundle" where
"ubConcEq sb1 \<equiv> \<Lambda> sb2.  (ubConc sb1\<cdot>sb2) \<bar> ubDom\<cdot>sb2 "


lemma ubconceq_cont [simp]: "cont (\<lambda> sb2.  (ubConc sb1\<cdot>sb2) \<bar> ubDom\<cdot>sb2)"
  apply(rule contI)
  by (smt ch2ch_Rep_cfunR contlub_cfun_arg cpo_lubI image_cong ubdom_chain_eq2)

lemma ubconceq_insert [simp]: "ubConcEq sb1\<cdot>sb2 = (ubConc sb1\<cdot>sb2) \<bar> ubDom\<cdot>sb2"
  by(simp add: ubConcEq_def)

lemma ubconceq_dom [simp]: "ubDom\<cdot>(ubConcEq sb1\<cdot>sb2) = ubDom\<cdot>sb2"
  apply(simp add: ubConcEq_def)
  sorry

end