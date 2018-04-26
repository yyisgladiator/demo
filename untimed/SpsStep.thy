theory SpsStep

imports "../USpec" "SpfStep"

begin

default_sort type
type_synonym 'm SPS = "'m SPF uspec"

definition spsStep_h::"((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS)\<rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF) set rev"where
"spsStep_h= (\<Lambda> h. (Rev {(\<lambda>e. if e = x then spf else ufLeast (ufDom\<cdot> spf) (ufDom\<cdot> spf)) | spf x. spf \<in> (Rep_rev_uspec (h x))}))"

lemma spsStep_h_mono[simp]:"monofun (\<lambda> h. Rev {(\<lambda>e::(channel\<rightharpoonup>'m::message). if e = z then spf else ufLeast (ufDom\<cdot> spf) (ufDom\<cdot> spf)) |(spf::'m SPF) z. spf \<in> (Rep_rev_uspec (h z))})"
proof(rule monofunI)
  fix x y::"(channel \<Rightarrow> 'm option) \<Rightarrow> 'm SPS"
  assume a1:"x \<sqsubseteq> y"
  have "\<And>z. Rep_rev_uspec (y z) \<subseteq> Rep_rev_uspec (x z)"
    by (metis less_set_def rep_uspec_belowI a1 fun_belowD inv_rev_rep_upsec_below)
  then have "\<And>z spf. spf \<in> Rep_rev_uspec (y z) \<Longrightarrow> spf \<in> Rep_rev_uspec (x z)"
    by blast
  then have "{\<lambda>e. if e = z then spf else ufLeast (ufDom\<cdot>spf) (ufDom\<cdot>spf) |spf z. spf \<in> Rep_rev_uspec (y z)} \<subseteq>
             {\<lambda>e. if e = z then spf else ufLeast (ufDom\<cdot>spf) (ufDom\<cdot>spf) |spf z. spf \<in> Rep_rev_uspec (x z)}"
    by blast
  then show "Rev {\<lambda>e. if e = z then spf else ufLeast (ufDom\<cdot>spf) (ufDom\<cdot>spf) |spf z. spf \<in> Rep_rev_uspec (x z)} \<sqsubseteq>
       Rev {\<lambda>e. if e = z then spf else ufLeast (ufDom\<cdot>spf) (ufDom\<cdot>spf) |spf z. spf \<in> Rep_rev_uspec (y z)}"
    by(simp add: less_set_def)
qed
  
      
lemma spsStep_h_cont[simp]:"cont (\<lambda> h. (Rev {(\<lambda>e::(channel\<rightharpoonup>'m::message). if e = x then spf else ufLeast (ufDom\<cdot> spf) (ufDom\<cdot> spf)) | (spf::'m SPF) x. spf \<in> (Rep_rev_uspec (h x))}))"
  sorry

lemma spsStep_h_insert:"spsStep_h\<cdot> f = (Rev {(\<lambda>e. if e = x then spf else ufLeast (ufDom\<cdot> spf) (ufDom\<cdot> spf)) | spf x. spf \<in> (Rep_rev_uspec (f x))})"
  by(simp add: spsStep_h_def)
    
(* like spfStep, copy & pasteonly on SPS *)
fun spsStep :: "channel set discr \<Rightarrow> channel set discr \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS) \<rightarrow> 'm SPS" where
"spsStep (Discr In) (Discr Out) = (\<Lambda> h. Abs_rev_uspec {spfStep In Out\<cdot>g | g. g \<in> inv Rev (spsStep_h\<cdot>h)})"

lemma spsStep_mono[simp]:"monofun (\<lambda>h::(channel \<Rightarrow> 'a::message option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec. Abs_rev_uspec {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h)})"
proof(rule monofunI)
  fix x y::"(channel \<Rightarrow> 'm::message option) \<Rightarrow> 'm SPS" 
  assume a1: "x \<sqsubseteq> y"
  have "(spsStep_h\<cdot>x) \<sqsubseteq> (spsStep_h\<cdot>y)" 
    by (simp add: a1 monofun_cfun_arg)
  then have "inv Rev(spsStep_h\<cdot>y) \<subseteq> inv Rev (spsStep_h\<cdot>x)"
    by (metis (full_types) SetPcpo.less_set_def below_rev.elims(2) inv_rev_rev)
  then have "\<And>g. g \<in> inv Rev(spsStep_h\<cdot>y) \<Longrightarrow> g \<in> inv Rev (spsStep_h\<cdot>x)"
    by blast
  then have h1:"{spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>y)} \<sqsubseteq>{spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>x)}"
    by (smt Collect_mono SetPcpo.less_set_def)
  have h2:"uspecWell {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'm option) \<Rightarrow> ('m stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>x)}"
    sorry
  have h3:"uspecWell {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'm option) \<Rightarrow> ('m stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>y)}"
    sorry
  show "Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>x)} \<sqsubseteq>
       Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>y)}"
    by (metis (mono_tags, lifting) h1 h2 h3 rep_abs_rev_simp uspec_belowI)
qed
  
lemma spsStep_cont[simp]:"cont (\<lambda>h. Abs_rev_uspec {spfStep In Out\<cdot>g | g. g \<in>inv Rev (spsStep_h\<cdot>h)})"
proof(rule Cont.contI2, simp)
  fix Y::"nat \<Rightarrow> ((channel \<Rightarrow> 'm::message option) \<Rightarrow> 'm SPS)"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))})"
  show "Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(\<Squnion>i::nat. Y i))} \<sqsubseteq>
       (\<Squnion>i::nat. Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))})"
  apply(simp add: a1 contlub_cfun_fun contlub_cfun_arg)
    sorry
qed
  
end
  