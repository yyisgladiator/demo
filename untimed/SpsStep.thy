theory SpsStep

imports "../USpec" "SpfStep"

begin

default_sort type
type_synonym 'm SPS = "'m SPF uspec"
    
definition spsStep_h::"((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS)\<rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF) set rev"where
"spsStep_h= (\<Lambda> h. setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(h e)))"

lemma spsStep_h_mono[simp]:"monofun (\<lambda> h::((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS). setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(h e)))"
proof(rule monofunI, simp add: uspecRevSet_def)
  fix x y::"(channel \<Rightarrow> 'm::message option) \<Rightarrow> 'm SPS"
  assume a1:"x \<sqsubseteq> y"
  then show "setify\<cdot>(\<lambda>e. fst (Rep_uspec (x e))) \<sqsubseteq> setify\<cdot>(\<lambda>e. fst (Rep_uspec (y e)))"
    by (simp add: below_fun_def fst_monofun monofun_cfun_arg rep_uspec_belowI)
qed
   
lemma spsStep_h_cont[simp]:"cont (\<lambda> h::((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS). setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(h e)))"
proof(rule Cont.contI2,simp)
  fix Y::"nat \<Rightarrow> (channel \<Rightarrow> 'm::message option) \<Rightarrow> 'm SPS"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. setify\<cdot>(\<lambda>e::channel \<Rightarrow> 'm option. uspecRevSet\<cdot>(Y i e)))"
  have a3:"(\<lambda>e. \<Squnion>i. uspecRevSet\<cdot>(Y i e)) =  (\<Squnion>i.(\<lambda>e. uspecRevSet\<cdot>(Y i e)))"
    apply(subst lub_fun,auto)
    by (metis (mono_tags, lifting) a1 cont_pref_eq1I fun_below_iff po_class.chain_def)
  show "setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>((\<Squnion>i::nat. Y i) e)) \<sqsubseteq> (\<Squnion>i. setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))"
    apply(simp add: a1 lub_fun)
    apply (simp add: contlub_cfun_arg a1 ch2ch_fun a3)
    apply(subst contlub_cfun_arg, auto)
    by (metis (mono_tags, lifting) a1 fun_below_iff monofun_cfun_arg po_class.chain_def)
qed
  

lemma spsStep_h_insert:"spsStep_h\<cdot>f = setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(f e))"
  by(simp add: spsStep_h_def)
    
(* like spfStep, copy & pasteonly on SPS *)
fun spsStep :: "channel set \<Rightarrow> channel set \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS) \<rightarrow> 'm SPS" where
"spsStep In Out = (\<Lambda> h. Abs_rev_uspec {spfStep In Out\<cdot>g | g. g \<in> inv Rev (spsStep_h\<cdot>h)} In Out)"

lemma spsStep_mono[simp]:assumes "finite In" shows"monofun (\<lambda>h::(channel \<Rightarrow> 'a::message option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec. Abs_rev_uspec {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h)} In Out)"
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
    by (simp add: ufclDom_ufun_def assms)
  have h3:"\<And>g. ufclRan\<cdot>(spfStep In Out\<cdot>g) = Out"
    by (simp add: ufclRan_ufun_def assms)
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
 
lemma uspec_lub_insert:assumes "chain (Y::nat \<Rightarrow> 'm::ufuncl set rev)" shows "(\<Squnion>i. (Y i, Discr In, Discr Out)) = ((\<Squnion>i. Y i), Discr In, Discr Out)"
  sorry

lemma spsStep_cont[simp]:assumes "finite In" shows"cont (\<lambda>h. Abs_rev_uspec {spfStep In Out\<cdot>g | g. g \<in>inv Rev (spsStep_h\<cdot>h)} In Out)"
proof(rule Cont.contI2, simp add: assms)
  fix Y::"nat \<Rightarrow> ((channel \<Rightarrow> 'a option) \<Rightarrow> 'a SPS)"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i. Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))} In Out)"
  have a3:"chain (\<lambda>i::nat. setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))"
    by (metis (mono_tags, lifting) a1 fun_below_iff monofun_cfun_arg po_class.chain_def)
  have a4:"chain (\<lambda>i::nat. Rev {spfStep In Out\<cdot>g |g. g \<in> inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))})"
    by (smt Collect_mono SetPcpo.less_set_def a3 below_rev.elims(2) below_rev.simps inv_rev_rev po_class.chain_def subsetCE)
  have h1:"\<forall>i. uspecWell (Rev {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))}) (Discr In) (Discr Out)"
    by (smt finite mem_Collect_eq spfstep_dom spfstep_ran ufclDom_ufun_def ufclRan_ufun_def uspecWell.simps assms)
  have h2:"uspecWell (Rev {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (\<Squnion>i::nat. spsStep_h\<cdot>(Y i))}) (Discr In) (Discr Out)"
    by (smt finite mem_Collect_eq spfstep_dom spfstep_ran ufclDom_ufun_def ufclRan_ufun_def uspecWell.simps assms)
  have h3:"Rep_uspec (Abs_uspec (\<Squnion>i::nat. (Rev {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>(Y i))}, Discr In, Discr Out)))
        =  (\<Squnion>i::nat. (Rev {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>(Y i))}, Discr In, Discr Out))"
    by (metis (mono_tags, lifting) a2 cont2contlubE h1 lub_eq lub_uspec rep_abs_uspec uspec_rep_cont)
  have h4:"\<And>x.
       \<forall>xa.
          (\<exists>i. xa = {spfStep In Out\<cdot>g |g. g \<in> inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))}) \<longrightarrow> x \<in> xa \<Longrightarrow>
       \<exists>g. x = spfStep In Out\<cdot>g \<and>
          (\<forall>x. (\<exists>i. x = inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))) \<longrightarrow> g \<in> x)"
  proof-
    fix x::"'a SPF"
    have h1:"(\<forall>xa.
          (\<exists>i. xa = {spfStep In Out\<cdot>g |g. g \<in> inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))}) \<longrightarrow> x \<in> xa) = (\<forall>i. x\<in>{spfStep In Out\<cdot>g |g. g \<in> inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))})"
      by auto
    have h2:"(\<exists>g. x = spfStep In Out\<cdot>g \<and> (\<forall>x. (\<exists>i. x = inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))) \<longrightarrow> g \<in> x)) = (\<exists>g. x = spfStep In Out\<cdot>g \<and> (\<forall>i. g\<in> inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))))"
      by auto
    have "(\<forall>i. \<exists>g.  (\<forall>m. g m \<in> Rep_rev_uspec (Y i m)) \<and> x = spfStep In Out\<cdot>g) =  (\<exists>g.\<forall>i.  (\<forall>m. g m \<in> Rep_rev_uspec (Y i m)) \<and> x = spfStep In Out\<cdot>g)"
    proof(auto)
      assume a1:"\<forall>i::nat. \<exists>g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. (\<forall>m::channel \<Rightarrow> 'a option. g m \<in> Rep_rev_uspec (Y i m)) \<and> x = spfStep In Out\<cdot>g"
      obtain g where g_def:"\<exists>i. (\<forall>m. g m \<in> Rep_rev_uspec (Y i m)) \<and> x = spfStep In Out\<cdot>g"
        using a1 by blast(*
      have problem:"\<And>u w x. ufRestrict In Out\<cdot>(u x) = (u x) \<Longrightarrow> ufRestrict In Out\<cdot>(w x) = (w x) \<Longrightarrow>  spfStep In Out\<cdot>u = spfStep In Out\<cdot>w \<Longrightarrow> u=w"
        sorry*)
      have h1:"(\<forall>i m. g m \<in> Rep_rev_uspec (Y i m)) \<and> x = spfStep In Out\<cdot>g"
      proof(cases "\<exists>i m. uspecDom\<cdot>(Y i m) \<noteq>In \<or> uspecRan\<cdot>(Y i m) \<noteq>Out")
        case True
        then show ?thesis sorry
      next
        case False
        then show ?thesis sorry
      qed
      then show "\<exists>g. (\<forall>i m. g m \<in> Rep_rev_uspec (Y i m)) \<and> x = spfStep In Out\<cdot>g"
        by blast
    qed
    then have h3_h:"\<forall>i. \<exists>g.  (\<forall>m. g m \<in> Rep_rev_uspec (Y i m)) \<and> x = spfStep In Out\<cdot>g \<Longrightarrow>
    \<exists>g.  (\<forall>i m. g m \<in> Rep_rev_uspec (Y i m)) \<and> x = spfStep In Out\<cdot>g"
      by simp
    have h3:"\<forall>i. \<exists>g. x = spfStep In Out\<cdot>g \<and> g \<in> inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e))) \<Longrightarrow>
    \<exists>g. x = spfStep In Out\<cdot>g \<and> (\<forall>i. g \<in> inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e))))"
      apply(simp add: setify_def inv_rev_rev uspecrevset_insert) using h3_h by blast
    show"\<forall>xa.
          (\<exists>i. xa = {spfStep In Out\<cdot>g |g. g \<in> inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))}) \<longrightarrow> x \<in> xa \<Longrightarrow>
       \<exists>g.
          x = spfStep In Out\<cdot>g \<and>
          (\<forall>x. (\<exists>i. x = inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))) \<longrightarrow> g \<in> x)"
    by(simp add: h1 h2 h3)
  qed
  show "Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(\<Squnion>i. Y i))} In Out \<sqsubseteq>
       (\<Squnion>i. Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))} In Out)"
    apply(simp add: a1 contlub_cfun_fun contlub_cfun_arg)
    apply(simp add: below_uspec_def)
    apply(simp only: h2 rep_abs_uspec)
    apply(simp add: lub_uspec a2)
    apply(simp only: h1 rep_abs_uspec h3)
    apply(simp add: a1 spsStep_h_insert)
    apply(simp add: setrevLubEqInterII a3)
    apply(simp add: uspec_lub_insert setrevLubEqInter a4)
    apply(simp add: less_set_def inv_rev_rev rev_inv_rev)
    apply auto
    by(simp add: h4)
qed
  
end
  