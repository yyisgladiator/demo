theory SpsStep

imports "../USpec" "SpfStep"

begin

default_sort type
type_synonym 'm SPS = "'m SPF uspec"

definition spsStep_h_test::"((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS) \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF) set"where
"spsStep_h_test= (\<lambda> h. {(\<lambda>e. spf) |spf e. spf \<in> (Rep_rev_uspec (h e))})"

definition spsStep_h::"((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS)\<rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF) set"where
"spsStep_h= (\<Lambda> h. {(\<lambda>e. spf) |spf e. spf \<in> (Rep_rev_uspec (h e))})"

lemma spsStep_h_mono[simp]:"monofun (\<lambda>h::(channel \<Rightarrow> 'a::message option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec. {\<lambda>e::channel \<Rightarrow> 'a option. spf |spf::('a stream\<^sup>\<Omega>) ufun. \<exists>e::channel \<Rightarrow> 'a option. spf \<in> Rep_rev_uspec (h e)})"
proof(rule monofunI)
  fix x y::"(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec"
  assume a1:"x \<sqsubseteq> y"
  show "{\<lambda>e::channel \<Rightarrow> 'a option. spf |spf::('a stream\<^sup>\<Omega>) ufun. \<exists>e::channel \<Rightarrow> 'a option. spf \<in> Rep_rev_uspec (x e)} \<sqsubseteq>
       {\<lambda>e::channel \<Rightarrow> 'a option. spf |spf::('a stream\<^sup>\<Omega>) ufun. \<exists>e::channel \<Rightarrow> 'a option. spf \<in> Rep_rev_uspec (y e)}"
    sorry
qed
  
    
    
lemma spsStep_h_test_cont[simp]:"cont(spsStep_h_test)"
proof(simp add: spsStep_h_test_def, rule Cont.contI2, simp)
  fix Y::"nat \<Rightarrow> (channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. {\<lambda>e::channel \<Rightarrow> 'a option. spf |spf::('a stream\<^sup>\<Omega>) ufun. \<exists>e::channel \<Rightarrow> 'a option. spf \<in> Rep_rev_uspec (Y i e)})"
  show "{\<lambda>e::channel \<Rightarrow> 'a option. spf |spf::('a stream\<^sup>\<Omega>) ufun. \<exists>e::channel \<Rightarrow> 'a option. spf \<in> Rep_rev_uspec ((\<Squnion>i::nat. Y i) e)} \<sqsubseteq>
       (\<Squnion>i::nat. {\<lambda>e::channel \<Rightarrow> 'a option. spf |spf::('a stream\<^sup>\<Omega>) ufun. \<exists>e::channel \<Rightarrow> 'a option. spf \<in> Rep_rev_uspec (Y i e)})"
    sorry
qed
  
lemma spsStep_h_cont[simp]:"cont (\<lambda> (h::((channel \<Rightarrow> 'm::message option) \<Rightarrow> ('m stream\<^sup>\<Omega>) ufun uspec)). {(\<lambda>e::(channel\<rightharpoonup>'m::message). spf) |(spf::('m stream\<^sup>\<Omega>) ufun) (e::channel \<Rightarrow> 'm option). spf \<in> (Rep_rev_uspec (h e))})"
  by(insert spsStep_h_test_cont, simp add:spsStep_h_test_def)

lemma spsStep_h_insert:"spsStep_h\<cdot> f = {(\<lambda>e. spf) |spf e. spf \<in> (Rep_rev_uspec (f e))}"
  apply (simp add: spsStep_h_def, subst beta_cfun, auto)
  by(insert spsStep_h_cont, simp)

(* like spfStep, copy & pasteonly on SPS *)
fun spsStep :: "channel set discr \<Rightarrow> channel set discr \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS) \<rightarrow> 'm SPS" where
"spsStep (Discr In) (Discr Out) = (\<Lambda> h. Abs_rev_uspec {spfStep In Out\<cdot>g | g. g \<in>(spsStep_h\<cdot>h)})"

lemma spsStep_mono[simp]:"monofun (\<lambda>h::(channel \<Rightarrow> 'a::message option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec. Abs_rev_uspec {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> spsStep_h\<cdot>h})"
  sorry

lemma spsStep_h_elem:"f \<in> (\<Squnion>i::nat. spsStep_h\<cdot>(Y i)) \<Longrightarrow> f \<in> (spsStep_h\<cdot>(Y i))"
  sorry    

lemma spsStep_cont[simp]:"cont (\<lambda>h. Abs_rev_uspec {spfStep In Out\<cdot>g | g. g \<in>(spsStep_h\<cdot>h)})"
proof(rule Cont.contI2, simp)
  fix Y::"nat \<Rightarrow> (channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. Abs_rev_uspec {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> spsStep_h\<cdot>(Y i)})"
  show "Abs_rev_uspec {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> spsStep_h\<cdot>(\<Squnion>i::nat. Y i)} \<sqsubseteq>
       (\<Squnion>i::nat. Abs_rev_uspec {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> spsStep_h\<cdot>(Y i)})"
  apply(simp add: a1 contlub_cfun_fun contlub_cfun_arg spsStep_h_elem)
    sorry
qed
  
end
  