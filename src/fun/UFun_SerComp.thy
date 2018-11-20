theory UFun_SerComp
  imports UFun bundle.UBundle_Pcpo
begin



definition ufSerComp2 :: "('in ubundle,'m ubundle) ufun \<rightarrow> ('m ubundle,'out ubundle) ufun \<rightarrow> ('in ubundle,'out ubundle) ufun" where
"ufSerComp2 \<equiv> \<Lambda> f1 f2. Abs_cufun (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(ubUp\<cdot>(f1 \<rightleftharpoons> x)))))"



declare[[show_types]]
lemma h3: "cont (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(ubUp\<cdot>(f1 \<rightleftharpoons> x)))))"
proof -
  have h01: "cont (\<lambda> x. (f2 \<rightleftharpoons> x))"
    by (simp add: cont_compose)
  then have h02: "\<And> f :: 'a\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<Omega>. cont f \<Longrightarrow> cont (\<lambda> x. (f2 \<rightleftharpoons> f x))"
    apply(subst contI2)
    apply (meson cont2mono monofun_def)
    apply (simp add: ch2ch_cont cont2contlubE)
    by simp
  have h03: "cont (\<lambda> x. (ubRestrict (ufDom\<cdot>f2)\<cdot>(ubUp\<cdot>(f1 \<rightleftharpoons> x))))"
    by (simp add: cont_compose)
  then have "cont (\<lambda> x. (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(ubUp\<cdot>(f1 \<rightleftharpoons> x)))))"
    by (simp add: h01 h02)
  then have "cont (\<lambda>u. (ubclDom\<cdot>u = ufDom\<cdot> f1)\<leadsto>f2 \<rightleftharpoons> ubUp\<cdot>(f1 \<rightleftharpoons> u) \<bar> ufDom\<cdot>f2)"
    using UFun.if_then_cont by blast
  then show "?thesis"
    by (simp add: ubclDom_ubundle_def)
qed

lemma h4: "ufWell (Abs_cfun (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(ubUp\<cdot>(f1 \<rightleftharpoons> x))))))"
  sorry



lemma h0: "cont (\<lambda> f2. Abs_cufun (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(ubUp\<cdot>(f1 \<rightleftharpoons> x))))))"
  apply(subst contI2)
  sorry

lemma h1: "cont (\<lambda> f1. \<Lambda> f2. Abs_cufun (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(ubUp\<cdot>(f1 \<rightleftharpoons> x))))))"
  apply(rule contI2)
  sorry

lemma ufsercomp_insert: "ufSerComp2\<cdot>f1\<cdot>f2 = (Abs_cufun (\<lambda> x. (ubDom\<cdot>x = ufDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(ubUp\<cdot>(f1 \<rightleftharpoons> x))))))"
  by(simp add: ufSerComp2_def h0 h1)



lemma test: assumes "ubDom\<cdot>sb = ufDom\<cdot>f1" shows "(ufSerComp2\<cdot>f1\<cdot>f2)\<rightleftharpoons>sb = (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(ubUp\<cdot>(f1 \<rightleftharpoons> sb))))" 
  by(simp add: ufsercomp_insert h3 h4 assms)



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