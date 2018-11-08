theory UFun_SerComp
  imports UFun bundle.UBundle_Pcpo
begin



definition ufSerComp2 :: "('in ubundle,'m ubundle) ufun \<rightarrow> ('m ubundle,'out ubundle) ufun \<rightarrow> ('in ubundle,'out ubundle) ufun" where
"ufSerComp2 \<equiv> \<Lambda> f1 f2. Abs_cufun (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(ubUp\<cdot>(f1 \<rightleftharpoons> x)))))"

(*
definition ufSerComp3_h :: "('in ubundle,'m ubundle) ufun \<Rightarrow> ('m ubundle,'out ubundle) ufun \<rightarrow> ('in ubundle,'out ubundle) ufun" where
"ufSerComp3_h f1 \<equiv> (\<Lambda> f2. Abs_cufun (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1) \<leadsto> 
  (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(ubUp\<cdot>(f1 \<rightleftharpoons> x))))))"

lift_definition ufSerComp3_h2 :: "('in ubundle,'m ubundle) ufun \<rightarrow> ('m ubundle,'out ubundle) ufun \<rightarrow> ('in ubundle,'out ubundle) ufun" is
  "ufSerComp3_h"
  apply rule+
  apply(simp_all add: cfun_def)
  sorry

lemma ufSerComp2_cont1: "cont (\<lambda> f1. Abs_cufun (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1) \<leadsto> 
  (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(ubUp\<cdot>(f1 \<rightleftharpoons> x))))))"
  sorry

lemma ufSerComp2_cont2: "cont (\<lambda> f2. Abs_cufun (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1) \<leadsto> 
  (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(ubUp\<cdot>(f1 \<rightleftharpoons> x))))))"
  sorry


lemma ufsercomp2_insert: "ufSerComp2\<cdot>f1\<cdot>f2 = Abs_cufun (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(ubUp\<cdot>(f1 \<rightleftharpoons> x)))))"
  sorry

lemma assumes "ubDom\<cdot>sb = ufDom\<cdot>f1" shows "(ufSerComp2\<cdot>f1\<cdot>f2)\<rightleftharpoons>sb = (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(ubUp\<cdot>(f1 \<rightleftharpoons> sb))))" 
  sorry

*)

end