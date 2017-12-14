
theory SB_SWS
imports UBundle

begin

definition ubConcEq:: "'m ubundle \<Rightarrow> 'm ubundle \<rightarrow> 'm ubundle" where
"ubConcEq sb1 \<equiv> \<Lambda> sb2.  (ubConc sb1\<cdot>sb2) \<bar> ubDom\<cdot>sb2 "


lemma sbconceq_cont [simp]: "cont (\<lambda> sb2.  (ubConc sb1\<cdot>sb2) \<bar> ubDom\<cdot>sb2)"
  apply(rule contI)
  by (smt ch2ch_Rep_cfunR contlub_cfun_arg image_cong sbChain_dom_eq2 thelubE)

lemma sbConcEq [simp]: "ubDom\<cdot>(ubConcEq sb1\<cdot>sb2) = ubDom\<cdot>sb2"
  apply(simp add: ubConcEq_def)
  by blast

end