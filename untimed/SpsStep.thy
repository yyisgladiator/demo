theory SpsStep

imports "../USpec" "SpfStep"

begin

default_sort type
type_synonym 'm SPS = "'m SPF uspec"
  
definition spsStep_h::"((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS)\<rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF) set rev"where
"spsStep_h= (\<Lambda> h. setify\<cdot>(\<lambda>e. fst(Rep_uspec(h e))))"

lemma spsStep_h_mono[simp]:"monofun (\<lambda> h::((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS). setify\<cdot>(\<lambda>e. fst(Rep_uspec(h e))))"
proof(rule monofunI)
  fix x y::"(channel \<Rightarrow> 'm::message option) \<Rightarrow> 'm SPS"
  assume a1:"x \<sqsubseteq> y"
  then show "setify\<cdot>(\<lambda>e. fst (Rep_uspec (x e))) \<sqsubseteq> setify\<cdot>(\<lambda>e. fst (Rep_uspec (y e)))"
    by (simp add: below_fun_def fst_monofun monofun_cfun_arg rep_uspec_belowI)
qed
   
lemma spsStep_h_cont[simp]:"cont (\<lambda> h::((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS). setify\<cdot>(\<lambda>e. fst(Rep_uspec(h e))))"
proof(rule Cont.contI2,simp)
  fix Y::"nat \<Rightarrow> (channel \<Rightarrow> 'm::message option) \<Rightarrow> 'm SPS"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. setify\<cdot>(\<lambda>e. fst (Rep_uspec (Y i e))))"
  have a3:"\<forall>e. (\<Squnion>i. Y i) e = (\<Squnion>i. Y i e)"
    by (simp add: a1 lub_fun)
  have a4:"\<forall>e. (Rep_uspec (\<Squnion>i. Y i e)) = (\<Squnion>i. (Rep_uspec ( Y i e)))"
    by (metis a1 ch2ch_fun cont2contlubE uspec_rep_cont)
  have a5:"\<forall>e. fst (\<Squnion>i. (Rep_uspec ( Y i e))) = (\<Squnion>i. fst (Rep_uspec ( Y i e)))"
    by (smt a1 a4 ch2ch_fun contlub_cfun_arg lub_eq uspecrevset_insert)
  have a6:" (\<lambda>e. (\<Squnion>i. fst (Rep_uspec ( Y i e)))) = (\<Squnion>i. (\<lambda>e. fst (Rep_uspec ( Y i e))))"
    apply(subst lub_fun, auto)
    by (metis (mono_tags, lifting) a1 fst_monofun fun_below_iff po_class.chain_def rep_uspec_belowI)
  show "setify\<cdot>(\<lambda>e. fst (Rep_uspec ((\<Squnion>i. Y i) e))) \<sqsubseteq> (\<Squnion>i. setify\<cdot>(\<lambda>e. fst (Rep_uspec (Y i e))))"
    apply(simp add: a1 lub_fun a2 a4 a5 a6)
    apply(subst contlub_cfun_arg)
    apply (metis (mono_tags, lifting) a1 below_fun_def fst_monofun po_class.chain_def rep_uspec_belowI)
    by simp
qed
  

lemma spsStep_h_insert:"spsStep_h\<cdot>f = setify\<cdot>(\<lambda>e. fst(Rep_uspec(f e)))"
  by(simp add: spsStep_h_def)
    
(* like spfStep, copy & pasteonly on SPS *)
fun spsStep :: "channel set \<Rightarrow> channel set \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS) \<rightarrow> 'm SPS" where
"spsStep In Out = (\<Lambda> h. Abs_rev_uspec {spfStep In Out\<cdot>g | g. g \<in> inv Rev (spsStep_h\<cdot>h)} In Out)"

lemma spsStep_mono[simp]:"monofun (\<lambda>h::(channel \<Rightarrow> 'a::message option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec. Abs_rev_uspec {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h)} In Out)"
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
  have h2:"\<And>g. ufclDom\<cdot>(spfStep In Out\<cdot>g) = In"
    by (simp add: ufclDom_ufun_def)
  have h3:"\<And>g. ufclRan\<cdot>(spfStep In Out\<cdot>g) = Out" 
    by (simp add: ufclRan_ufun_def)
  have h4:"\<And>f h. f\<in>{spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'm option) \<Rightarrow> ('m stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h)} \<Longrightarrow> \<exists>g. f = spfStep In Out\<cdot>g"
    by auto
  have h2:"uspecWell (Rev {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'm option) \<Rightarrow> ('m stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>x)}) (Discr In) (Discr Out)"
    using h2 h3 by auto
  have h3:"uspecWell (Rev {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'm option) \<Rightarrow> ('m stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>y)}) (Discr In) (Discr Out)"
    by (metis (no_types, lifting) SetPcpo.less_set_def h1 h2 subsetCE uspecWell.simps)
  show "Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>x)} In  Out\<sqsubseteq>
       Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>y)} In Out"
    by (metis (no_types, lifting) Pair_below_iff below_refl below_rev.simps below_uspec_def h1 h2 h3 rep_abs_uspec)
qed
  
lemma spsStep_cont[simp]:assumes "finite In" shows"cont (\<lambda>h. Abs_rev_uspec {spfStep In Out\<cdot>g | g. g \<in>inv Rev (spsStep_h\<cdot>h)} In Out)"
proof(rule Cont.contI2, simp)
  fix Y::"nat \<Rightarrow> ((channel \<Rightarrow> 'a option) \<Rightarrow> 'a SPS)"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i. Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))} In Out)"
  have h1:"\<forall>i. uspecWell (Rev {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))}) (Discr In) (Discr Out)"
    by (smt finite mem_Collect_eq spfstep_dom spfstep_ran ufclDom_ufun_def ufclRan_ufun_def uspecWell.simps)
  have h2:"uspecWell (Rev {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (\<Squnion>i::nat. spsStep_h\<cdot>(Y i))}) (Discr In) (Discr Out)"
    by (smt finite mem_Collect_eq spfstep_dom spfstep_ran ufclDom_ufun_def ufclRan_ufun_def uspecWell.simps)
  have h3:"Rep_uspec (Abs_uspec (\<Squnion>i::nat. (Rev {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>(Y i))}, Discr In, Discr Out)))
        =  (\<Squnion>i::nat. (Rev {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>(Y i))}, Discr In, Discr Out))"
    by (metis (mono_tags, lifting) a2 cont2contlubE h1 lub_eq lub_uspec rep_abs_uspec uspec_rep_cont)
  have h4:"chain (\<lambda>i::nat. Rev {g. \<forall>m. g m \<in> Rep_rev_uspec (Y i m)})"
    by (smt Collect_mono SetPcpo.less_set_def a1 below_fun_def below_rev.elims(2) below_rev.simps fst_monofun inv_rev_rev po_class.chain_def rep_uspec_belowI subsetCE) 
  have h5:"(\<Squnion>i. (Rev {spfStep In Out\<cdot>g |g. \<forall>m. g m \<in> Rep_rev_uspec (Y i m)}, Discr In, Discr Out)) = ((\<Squnion>i. Rev{spfStep In Out\<cdot>g |g. \<forall>m. g m \<in> Rep_rev_uspec (Y i m)}), Discr In, Discr Out )"
    sorry
  have h6:"chain (\<lambda>i::nat. Rev {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. \<forall>m::channel \<Rightarrow> 'a option. g m \<in> Rep_rev_uspec (Y i m)})"
    by (smt Collect_mono SetPcpo.less_set_def a1 below_rev.elims(2) below_rev.simps fst_monofun fun_below_iff inv_rev_rev po_class.chain_def rep_uspec_belowI subsetCE)
  show "Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(\<Squnion>i. Y i))} In Out \<sqsubseteq>
       (\<Squnion>i. Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))} In Out)"
    apply(simp add: a1 contlub_cfun_fun contlub_cfun_arg)
    apply(simp add: below_uspec_def)
    apply(simp only: h2 rep_abs_uspec)
    apply(simp add: lub_uspec a2)
    apply(simp only: h1 rep_abs_uspec h3)
    apply(simp add: a1 spsStep_h_insert)
    apply(simp add: setify_def inv_rev_rev h5)
    apply(subst setrevLubEqInterII, simp add: h4)
    apply(subst setrevLubEqInter, simp add: h6 ,simp add:inv_rev_rev rev_inv_rev)
    apply(simp add: less_set_def)
    apply(simp add: assms spfstep_insert)
    apply auto 
    apply(simp add: assms spfstep_insert)
    sorry
qed
  
end
  