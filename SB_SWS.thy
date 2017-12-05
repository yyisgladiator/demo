
theory SB_SWS
imports SB

begin

definition sbConcEq:: "'m SB \<Rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbConcEq sb1 \<equiv> \<Lambda> sb2.  (sbConc sb1\<cdot>sb2) \<bar> sbDom\<cdot>sb2 "


lemma sbconceq_cont [simp]: "cont (\<lambda> sb2.  (sbConc sb1\<cdot>sb2) \<bar> sbDom\<cdot>sb2)"
  apply(rule contI)
  by (smt ch2ch_Rep_cfunR contlub_cfun_arg image_cong sbChain_dom_eq2 thelubE)

lemma sbConcEq [simp]: "sbDom\<cdot>(sbConcEq sb1\<cdot>sb2) = sbDom\<cdot>sb2"
  apply(simp add: sbConcEq_def)
  by blast

end