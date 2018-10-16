theory SpsStep

(* imports "../USpec" "NewSpfStep" "../USpec_Comp" *)
imports NewSpfStep spec.USpec 

begin

default_sort type
type_synonym 'm SPS = "('m,'m) SPF uspec"
  
  
section \<open>Definition\<close> 

subsection \<open>Helper\<close>
(*  convert input function to a set rev *)    
definition spsStep_h::"('m::message sbElem \<Rightarrow> 'm SPS)\<rightarrow> ('m sbElem \<Rightarrow> ('m,'m) SPF) set"where
"spsStep_h= (\<Lambda> h. setify (\<lambda>e. uspecSet\<cdot>(h e)))"

(* Pradicate to filter those interesting function  *)
definition spsStep_P:: "channel set \<Rightarrow> channel set \<Rightarrow> ('m::message sbElem \<Rightarrow> ('m,'m) SPF)  \<Rightarrow> bool" where
 "spsStep_P In Out \<equiv> \<lambda> g. (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)"
(* "spsStep_P In Out \<equiv> \<lambda> g. (\<forall>m. ((dom (Rep_sbElem m) = In ) \<longrightarrow> ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out) 
\<and> ((dom (Rep_sbElem m) \<noteq> In ) \<longrightarrow> (g m) = ufLeast In Out))" *)

(* DD: monofun only version of spsStep  *)
definition spsStep_m::"channel set \<Rightarrow> channel set \<Rightarrow> ('m::message sbElem \<Rightarrow> 'm SPS) \<Rightarrow> 'm SPS" where
"spsStep_m In Out \<equiv> \<lambda> H. Abs_uspec (((\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) ` 
                                      (Set.filter (spsStep_P In Out) (spsStep_h\<cdot>H))), Discr  In, Discr Out)"

definition spsStep ::"channel set \<Rightarrow> channel set \<Rightarrow> ('m::message sbElem \<Rightarrow> 'm SPS) \<rightarrow> 'm SPS" where
"spsStep In Out \<equiv> (\<Lambda> h. spsStep_m In Out h)"

(* ----------------------------------------------------------------------- *)
section \<open>Lemma\<close>
(* ----------------------------------------------------------------------- *)

subsection \<open>spsStep_h\<close>

lemma spsStep_h_mono[simp]:"monofun (\<lambda> h::('m::message sbElem \<Rightarrow> 'm SPS). setify (\<lambda>e. uspecSet\<cdot>(h e)))"
proof(rule monofunI, simp add: uspecSet_def)
  fix x y::"'m sbElem \<Rightarrow> 'm SPS"
  assume a1:"x \<sqsubseteq> y"
  then show "setify (\<lambda>e. fst (Rep_uspec (x e))) \<sqsubseteq> setify (\<lambda>e. fst (Rep_uspec (y e)))"
  proof -
    have f1: "\<forall>s. x s \<sqsubseteq> y s"
by (meson a1 fun_below_iff)
  obtain uu :: "('m sbElem \<Rightarrow> 'm stream\<^sup>\<Omega>\<Rrightarrow> 'm stream\<^sup>\<Omega>) set \<Rightarrow> ('m sbElem \<Rightarrow> 'm stream\<^sup>\<Omega>\<Rrightarrow> 'm stream\<^sup>\<Omega>) set \<Rightarrow> 'm sbElem \<Rightarrow> 'm stream\<^sup>\<Omega>\<Rrightarrow> 'm stream\<^sup>\<Omega>" where
    "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (uu x0 x1 \<in> x1 \<and> uu x0 x1 \<notin> x0)"
    by moura
  then have f2: "\<forall>F Fa. (\<not> F \<subseteq> Fa \<or> (\<forall>f. f \<notin> F \<or> f \<in> Fa)) \<and> (F \<subseteq> Fa \<or> uu Fa F \<in> F \<and> uu Fa F \<notin> Fa)"
    by blast
  obtain ss :: "('m sbElem \<Rightarrow> 'm stream\<^sup>\<Omega>\<Rrightarrow> 'm stream\<^sup>\<Omega>) \<Rightarrow> ('m sbElem \<Rightarrow> ('m stream\<^sup>\<Omega>\<Rrightarrow> 'm stream\<^sup>\<Omega>) set) \<Rightarrow> 'm sbElem" where
    "\<forall>x0 x1. (\<exists>v2. x0 v2 \<notin> x1 v2) = (x0 (ss x0 x1) \<notin> x1 (ss x0 x1))"
    by moura
  then have f3: "(\<not> (\<forall>s. uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s)))) s \<in> fst (Rep_uspec (y s))) \<or> (\<forall>s. uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s)))) s \<in> fst (Rep_uspec (y s)))) \<and> ((\<forall>s. uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s)))) s \<in> fst (Rep_uspec (y s))) \<or> uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s)))) (ss (uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s))))) (\<lambda>s. fst (Rep_uspec (y s)))) \<notin> fst (Rep_uspec (y (ss (uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s))))) (\<lambda>s. fst (Rep_uspec (y s)))))))"
    by blast
  have "fst (Rep_uspec (x (ss (uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s))))) (\<lambda>s. fst (Rep_uspec (y s)))))) \<subseteq> fst (Rep_uspec (y (ss (uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s))))) (\<lambda>s. fst (Rep_uspec (y s))))))"
    using f1 by (metis SetPcpo.less_set_def fst_monofun rep_uspec_belowI)
  moreover
  { assume "fst (Rep_uspec (x (ss (uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s))))) (\<lambda>s. fst (Rep_uspec (y s)))))) \<subseteq> fst (Rep_uspec (y (ss (uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s))))) (\<lambda>s. fst (Rep_uspec (y s)))))) \<and> uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s)))) (ss (uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s))))) (\<lambda>s. fst (Rep_uspec (y s)))) \<notin> fst (Rep_uspec (y (ss (uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s))))) (\<lambda>s. fst (Rep_uspec (y s))))))"
    then have "\<exists>s. uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s)))) s \<notin> fst (Rep_uspec (x s))"
      by (meson rev_subsetD)
    then have "uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s)))) \<notin> setify (\<lambda>s. fst (Rep_uspec (x s))) \<or> uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s)))) \<in> setify (\<lambda>s. fst (Rep_uspec (y s)))"
      by (simp add: SetPcpo.setify_def) }
  moreover
  { assume "uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s)))) (ss (uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s))))) (\<lambda>s. fst (Rep_uspec (y s)))) \<in> fst (Rep_uspec (y (ss (uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s))))) (\<lambda>s. fst (Rep_uspec (y s))))))"
    then have "uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s)))) \<notin> setify (\<lambda>s. fst (Rep_uspec (x s))) \<or> uu (setify (\<lambda>s. fst (Rep_uspec (y s)))) (setify (\<lambda>s. fst (Rep_uspec (x s)))) \<in> setify (\<lambda>s. fst (Rep_uspec (y s)))"
      using f3 by (simp add: SetPcpo.setify_def) }
  ultimately have "setify (\<lambda>s. fst (Rep_uspec (x s))) \<subseteq> setify (\<lambda>s. fst (Rep_uspec (y s)))"
    using f2 by meson
  then show ?thesis
    by (simp add: SetPcpo.less_set_def)
qed
qed

lemma spsStep_h_cont[simp]:"cont (\<lambda> h::('m::message sbElem \<Rightarrow> 'm SPS). setify (\<lambda>e. uspecSet\<cdot>(h e)))"
proof(rule Cont.contI2,simp)
  fix Y::"nat \<Rightarrow> 'm sbElem \<Rightarrow> 'm SPS"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. setify (\<lambda>e. uspecSet\<cdot>(Y i e)))"
  have a3:"(\<lambda>e. \<Squnion>i. uspecSet\<cdot>(Y i e)) =  (\<Squnion>i.(\<lambda>e. uspecSet\<cdot>(Y i e)))"
    apply(subst lub_fun,auto)
    by (metis (mono_tags, lifting) a1 cont_pref_eq1I fun_below_iff po_class.chain_def)
  show "setify (\<lambda>e. uspecSet\<cdot>((\<Squnion>i::nat. Y i) e)) \<sqsubseteq> (\<Squnion>i. setify (\<lambda>e. uspecSet\<cdot>(Y i e)))"
    apply(simp add: a1 lub_fun)
    apply (simp add: contlub_cfun_arg a1 ch2ch_fun a3)
    apply(subst contlub_cfun_arg, auto)
    by (metis (mono_tags, lifting) a1 fun_below_iff monofun_cfun_arg po_class.chain_def)
qed
  
lemma spsStep_h_insert:"spsStep_h\<cdot>f = setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(f e))"
  by(simp add: spsStep_h_def)

lemma spsstep_h_ele: assumes "g \<in> inv Rev (spsStep_h\<cdot>H)"
  shows "\<And> sbe. uspec_in (g sbe) (H sbe)"
  by (metis (no_types, lifting) assms mem_Collect_eq rev.inject rev_inv_rev setify_insert spsStep_h_insert)

lemma spsstep_h_ele2: assumes "spsStep_h\<cdot>H \<noteq> Rev {}"
  shows "\<And> sbe. \<exists> g \<in> inv Rev (spsStep_h\<cdot>H). uspec_in (g sbe) (H sbe)"
  by (metis assms ex_in_conv rev_inv_rev spsstep_h_ele)

lemma spsstep_h_ele3: assumes "spsStep_h\<cdot>H \<noteq> Rev {}"
  shows "\<And> sbe. (H sbe) \<noteq> uspecMax (uspecDom\<cdot>(H sbe)) (uspecRan\<cdot>(H sbe))"
  by (metis assms equals0D inv_rev_rev prod.sel(1) spsstep_h_ele2 uspecMax.rep_eq uspecrevset_insert)

lemma spsstep_h_ele4: assumes "spsStep_h\<cdot>H \<noteq> Rev {}" and "uspec_in f (H sbe)"
  shows  "\<exists> h \<in> inv Rev (spsStep_h\<cdot>H). h sbe = f"
  by (metis (no_types, lifting) assms SetRev.setify_empty SetRev.setify_final spsStep_h_insert)

lemma spsstep_h_inI: "(\<forall> sbe. uspec_in (g sbe) (H sbe)) \<Longrightarrow> g \<in> inv Rev (spsStep_h\<cdot>H)"
  by (simp add: setify_insert spsStep_h_insert)

lemma spstep_h_P_obtain_h: assumes "spsStep_h\<cdot>H \<noteq> Rev {}" and "\<And> sbe. P sbe \<Longrightarrow> uspec_in f (H sbe)"
  shows "\<exists> g \<in> inv Rev (spsStep_h\<cdot>H). \<forall> sbe. P sbe \<longrightarrow> g sbe = f"
proof  (rule ccontr)
  assume a1: "\<not>(\<exists> g \<in> inv Rev (spsStep_h\<cdot>H). \<forall> sbe. P sbe \<longrightarrow> g sbe = f)"
  obtain g where g_def: "g \<equiv> (\<lambda> sbe. if P sbe then f else (SOME f. uspec_in f (H sbe)))"
    by simp
  have "\<forall> sbe. uspec_in (g sbe) (H sbe)"
    apply rule
    apply (case_tac "P sbe")
     apply (simp_all add: g_def)
     apply (simp add: assms(2))
    using assms(1) some_in_eq spsstep_h_ele2 by fastforce
  then have "g \<in> inv Rev (spsStep_h\<cdot>H)"
    by (simp add: spsstep_h_inI)
  then show False
    using a1 g_def by auto
qed

lemma spstep_h_P_obtain_h2: assumes "spsStep_h\<cdot>H \<noteq> Rev {}" and "\<And> sbe. P sbe \<Longrightarrow> uspec_in f (H sbe)"
  shows "\<exists> g \<in> inv Rev (spsStep_h\<cdot>H). \<forall> sbe. (P sbe \<longrightarrow> g sbe = f) \<and> 
        (\<not> (P sbe) \<longrightarrow> uspec_in (g sbe) (H sbe))"
proof  (rule ccontr)
  assume a1: "\<not>(\<exists> g \<in> inv Rev (spsStep_h\<cdot>H). \<forall> sbe. (P sbe \<longrightarrow> g sbe = f) \<and> 
        (\<not> (P sbe) \<longrightarrow> uspec_in (g sbe) (H sbe)))"
  obtain g where g_def: "g \<equiv> (\<lambda> sbe. if P sbe then f else (SOME f. uspec_in f (H sbe)))"
    by simp
  have "\<forall> sbe. uspec_in (g sbe) (H sbe)"
    apply rule
    apply (case_tac "P sbe")
     apply (simp_all add: g_def)
     apply (simp add: assms(2))
    using assms(1) some_in_eq spsstep_h_ele2 by fastforce
  then have "g \<in> inv Rev (spsStep_h\<cdot>H)"
    by (simp add: spsstep_h_inI)
  then show False
    using a1 g_def spsstep_h_ele by fastforce
qed

lemma spstep_h_P_obtain: assumes "spsStep_h\<cdot>H \<noteq> Rev {}" and "\<And> sbe. P sbe \<Longrightarrow> uspec_in f (H sbe)"
  obtains g where "g \<in> inv Rev (spsStep_h\<cdot>H)" and "\<forall> sbe. (P sbe \<longrightarrow> g sbe = f) \<and> 
        (\<not> (P sbe) \<longrightarrow> uspec_in (g sbe) (H sbe))"
  by (metis assms(1) assms(2) spsstep_h_ele spstep_h_P_obtain_h)
    
(*NewSpsStep Lemma*)    
    
subsection \<open>spsStep_P\<close>

lemma spsStep_P_uspecwell_h: "\<And>H. \<forall> g \<in> (inv Rev (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H))). 
  (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)"
proof rule
  fix H:: "'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun uspec"
  fix g::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun"
  assume a1: "g \<in> inv Rev (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H))"
  have f1: "spsStep_P In Out g"
    by (metis a1 setrevFilter_gdw)
  then show "\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out"
    by (metis (no_types, lifting) spsStep_P_def ufleast_ufRan ufleast_ufdom)
qed

lemma spsStep_P_uspecwell_h2: 
  "\<And>H. \<forall> g \<in> (inv Rev (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H)))). 
    (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)"
proof rule
  fix H:: "'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun uspec"
  fix g::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun"
  assume a1: "g \<in> inv Rev (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H)))"
  obtain h where h_def: "g = (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h" 
     and h_def_2: "h \<in> inv Rev (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H))"
    by (metis (mono_tags, lifting) a1 image_iff inv_rev_rev setrevImage_def)
  have f1: "spsStep_P In Out h"
    by (metis h_def_2 setrevFilter_gdw)
  then have f2: "spsStep_P In Out  (\<lambda> sbEl. spfRtIn\<cdot>(h sbEl))"
    by (simp add: spfrt_ufleast spsStep_P_def)
  then show "\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out"
    using h_def h_def_2 spfRtIn_dom spfRtIn_ran spsStep_P_uspecwell_h by blast
qed

lemma spsStep_P_uspecwell_h3: 
  "\<And>H. \<forall> g \<in> (inv Rev (setrevImage (\<lambda> h. spfStep_inj In Out h)
                        (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) 
                          (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H))))). 
    (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)"
  by (simp add: inv_rev_rev setrevImage_def spfStep_inj_def)

lemma spsStep_P_uspecwell_h4: assumes "finite In" shows
  "\<And>H. \<forall> g \<in> (inv Rev (setrevImage (\<lambda> h. spfStep In Out\<cdot>h)
                        (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) 
                          (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H))))). 
     ufDom\<cdot>g = In \<and> ufRan\<cdot>g = Out"
proof rule
  fix H:: "'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun uspec"
  fix g:: "('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun"
  assume a1: "g \<in> (inv Rev (setrevImage (\<lambda> h. spfStep In Out\<cdot>h)
                        (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) 
                          (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H)))))"
  obtain h where h_def: "g =  (\<lambda> h. spfStep In Out\<cdot>h) h \<and>
    h \<in> (inv Rev ((setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) 
                          (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H)))))"
    by (metis (no_types, lifting) a1 setrevimage_mono_obtain3)
  show "ufDom\<cdot>g = In \<and> ufRan\<cdot>g = Out"
    by (simp add: assms h_def)
qed

subsection \<open>injectivity\<close>

lemma spsStep_image_simp: "setrevImage (\<lambda> h. spfStep In Out\<cdot>h)
                        (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) H) = 
setrevImage (\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) H"
  using setrevimage_image by auto

lemma spsStep_uspecWell_h: assumes "finite In" shows
"uspecWell (setrevImage (\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) H) (Discr In) (Discr Out)"
  by (simp add: assms setrevImage_def ufclDom_ufun_def ufclRan_ufun_def)

lemma spsStep_uspecWell[simp]: assumes "finite In" shows
"uspecWell (setrevImage (\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H))) (Discr In) (Discr Out)"
  by (simp add: assms setrevImage_def ufclDom_ufun_def ufclRan_ufun_def)


lemma spsStep_mono_h: assumes "x \<sqsubseteq> y" shows "setrevImage (\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) x \<sqsubseteq>
setrevImage (\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) y"
  by (simp add: assms image_mono_rev monofunE)

lemma spsStep_mono_h2: assumes "finite In" shows
"monofun (\<lambda> H. Abs_uspec 
((setrevImage (\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) H), Discr  In, Discr Out))"
  apply (rule monofunI)
  apply (simp add: below_uspec_def)
  by (simp add: assms spsStep_mono_h spsStep_uspecWell_h)

lemma spsStep_mono: assumes "finite In" shows
"monofun
     (\<lambda>H . Abs_uspec (setrevImage (\<lambda>h . spfStep In Out\<cdot>(\<lambda>sbEl. spfRtIn\<cdot>(h sbEl))) 
            (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H)), Discr In, Discr Out))"
  apply (rule monofunI)
  apply (simp add: below_uspec_def assms spsStep_uspecWell)
  by (simp add: monofun_cfun_arg spsStep_mono_h)

lemma spsStep_mono_2: assumes "finite In" shows "x \<sqsubseteq> y \<Longrightarrow> spsStep_m In Out x \<sqsubseteq> spsStep_m In Out y"
  unfolding spsStep_m_def
  apply (simp add: below_uspec_def assms)
  by (simp add: monofun_cfun_arg spsStep_mono_h)


(*
lemma spsStep_m_cont[simp]: assumes "finite In" shows
"cont (\<lambda> H. Abs_uspec ((setrevImage (\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) 
    (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H))), Discr  In, Discr Out))"
proof (rule Cont.contI2, simp add: assms spsStep_mono)
  fix Y::"nat \<Rightarrow> 'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun uspec"

  let ?H = "(\<lambda> H. (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H)))"

  assume a1: "chain Y"
  assume a2: "chain (\<lambda>i::nat. Abs_uspec (setrevImage (\<lambda>h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun. spfStep In Out\<cdot>(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl))) (?H (Y i)), Discr In, Discr Out))"
  have inj_on_i: "\<forall>i::nat. inj_on (\<lambda>h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun. spfStep In Out\<cdot>(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl))) (inv Rev (?H (Y i)))"
  proof (rule, rule inj_onI, rule ccontr)
    fix i ::nat
    fix x::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun"
    fix y::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun"
    assume assm_x: "x \<in> inv Rev (?H (Y i))"
    assume assm_y: "y \<in> inv Rev (?H (Y i))"
    assume assm_result_eq: "spfStep In Out\<cdot>(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(x sbEl)) = spfStep In Out\<cdot>(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(y sbEl))"
    assume assm_dif: "x \<noteq> y"
    then have x_y_dom_ran: "\<And> m.  ufDom\<cdot>(x m) = In \<and> ufDom\<cdot>(y m) = In \<and> ufRan\<cdot>(x m) = Out \<and> ufRan\<cdot>(y m) = Out"
      using assm_x assm_y spsStep_P_uspecwell_h by blast
    obtain sbEl where sbEl_def: "x sbEl \<noteq> y sbEl"
      by (meson assm_dif ext)
(* NOTE: it only works if we use the more restricted spsStep_P, otherwise spsStep is not cont 
  but we dont need that for gfp or in rev set the lfp*)
    have sbEl_dom: "dom (Rep_sbElem sbEl) = In"
(*      by (metis (no_types, hide_lams) assm_x assm_y sbEl_def setrevFilter_gdw spsStep_P_def) *)
      sorry
    obtain da_sb where da_sb_def: "x sbEl \<rightleftharpoons> da_sb \<noteq> y sbEl  \<rightleftharpoons> da_sb"
      by (metis sbEl_def spf_eq x_y_dom_ran)
    obtain the_sb where the_sb_def:"((inv convDiscrUp (sbHdElem\<cdot>the_sb))) =  (Rep_sbElem sbEl) 
                                                \<and> sbHdElemWell the_sb 
                                                \<and> ubDom\<cdot>the_sb = dom (Rep_sbElem sbEl)"
      by (metis (full_types) Abs_sbElem_inverse mem_Collect_eq sbElem_surj sbHdElemWell_def sbHdElem_sbElemWell)
    have the_sb_dom: "ubDom\<cdot>the_sb = In"
      by (simp add: sbEl_dom the_sb_def)
    have da_sb_dom: "ubDom\<cdot>da_sb =In"
    proof (rule ccontr)
      assume dom_not: "ubDom\<cdot>da_sb \<noteq> In"
      then have "x sbEl \<rightleftharpoons> da_sb = y sbEl \<rightleftharpoons> da_sb"
        by (metis test2 ufRestrict_apply x_y_dom_ran)
      then show False
        using da_sb_def by auto
    qed
    have x_y_spfrt_dif: "(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(x sbEl)) \<noteq> 
                              (\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(y sbEl))"
      by (metis da_sb_def sbrt_conc_hd spfRtIn_step)
    have the_sb_hd_well: "sbHdElemWell ((sbHd\<cdot>the_sb))"
    proof (simp add: sbHdElemWell_def, rule)
      fix c::channel
      assume c_in_dom: "c \<in> ubDom\<cdot>the_sb"
      have "the_sb . c \<noteq> \<epsilon>"
        by (meson c_in_dom sbHdElemWell_def the_sb_def)
      then show " stake (Suc (0::nat))\<cdot>(the_sb  .  c) \<noteq> \<epsilon>"
        by (metis stream.con_rews(2) stream.exhaust stream.take_rews)
    qed
    have f1: "(ubRestrict ( ubDom\<cdot>da_sb)\<cdot>(ubConc (sbHd\<cdot>the_sb)\<cdot>da_sb))= (ubConc (sbHd\<cdot>the_sb)\<cdot>da_sb)"
      by (simp add: da_sb_dom the_sb_dom)
    have da_conc_sbhdel_well: "sbHdElemWell (ubConcEq (sbHd\<cdot>the_sb)\<cdot>da_sb)"
      apply (simp add: sbHdElemWell_def, rule)
      apply (simp add: the_sb_dom da_sb_dom)
      by (metis One_nat_def sbHdElemWell_def sbhd_getch sbhd_sbdom sconc_snd_empty strictI 
          the_sb_dom the_sb_hd_well usclConc_stream_def)
    have da_conc_sbhdel_well2: "sbHdElemWell (ubConc (sbHd\<cdot>the_sb)\<cdot>da_sb)"
      using da_conc_sbhdel_well f1 by auto
    have da_conc_hd: "sbHd\<cdot>(ubConcEq (sbHd\<cdot>the_sb)\<cdot>da_sb) = sbHd\<cdot>the_sb"
    proof -
      have the_dom: " ubDom\<cdot>(sbHd\<cdot>(ubConcEq (sbHd\<cdot>the_sb)\<cdot>da_sb)) = In"
        using da_sb_dom by auto

      show ?thesis
        apply (rule ub_eq)
         apply (simp add: da_sb_dom the_sb_dom)
        apply (simp only: the_dom)
        apply (subst sbHd_def)
        apply (simp add: f1)
        apply (subst sbtake_sbgetch)
         apply (simp add: the_sb_dom)
        apply (simp add: sbHd_def)
        apply (subst ubConc_usclConc_eq)
          apply (simp add: the_sb_dom)
         apply (simp add: da_sb_dom)
        by (smt One_nat_def sbHdElemWell_def sbHd_def sbtake_sbdom sbtake_sbgetch sconc_snd_empty sdrop_0 sdrop_back_rt sdropostake stake_Suc surj_scons the_sb_dom the_sb_hd_well usclConc_stream_def)
    qed

    have da_conc_hd2: "sbHd\<cdot>(ubConc (sbHd\<cdot>the_sb)\<cdot>da_sb) = sbHd\<cdot>the_sb"
      using da_conc_hd f1 by auto
    have da_conc_rt: "sbRt\<cdot>(ubConcEq (sbHd\<cdot>the_sb)\<cdot>da_sb) = da_sb"
      apply (simp add: f1)
      apply(rule ub_eq)
       apply (simp_all add: da_sb_dom the_sb_dom) 
      by (smt One_nat_def Rep_cfun_strict1 \<open>sbHd\<cdot> (ubConcEq (sbHd\<cdot>(the_sb::'a stream\<^sup>\<Omega>))\<cdot> (da_sb::'a stream\<^sup>\<Omega>)) = sbHd\<cdot>the_sb\<close> da_sb_dom f1 inject_scons sbHdElemWell_def sbhd_getch sbhd_sbdom sconc_snd_empty stake_Suc 
          stream.take_0 strictI surj_scons the_sb_dom the_sb_hd_well ubConc_usclConc_eq ubconceq_insert usclConc_stream_def)
    have da_conc_rt2: "sbRt\<cdot>(ubConc (sbHd\<cdot>the_sb)\<cdot>da_sb) = da_sb"
      using da_conc_rt f1 by auto
    have "inv convDiscrUp (sbHdElem\<cdot>(ubConc (sbHd\<cdot>the_sb)\<cdot>da_sb)) = Rep_sbElem sbEl"
    proof -
      have "\<And> x. x \<in> dom (Rep_sbElem sbEl) \<Longrightarrow> 
            (inv convDiscrUp (sbHdElem\<cdot>(ubConc (sbHd\<cdot>the_sb)\<cdot>da_sb)))\<rightharpoonup>x = (Rep_sbElem sbEl) \<rightharpoonup> x"
      proof -
        fix x
        assume assms_x_in_dom: "x \<in> dom (Rep_sbElem sbEl)"
        have "x \<in> dom (inv convDiscrUp (sbHdElem\<cdot>(ubConc (sbHd\<cdot>the_sb)\<cdot>da_sb)))"
          by (metis assms_x_in_dom convdiscrup_inv_dom_eq da_conc_hd2 da_conc_sbhdel_well2 
              sbHdElemWell_def sbHdElem_channel sbHdElem_dom sbhd_sbdom the_sb_def)
        show "(inv convDiscrUp (sbHdElem\<cdot>(ubConc (sbHd\<cdot>the_sb)\<cdot>da_sb)))\<rightharpoonup>x = (Rep_sbElem sbEl) \<rightharpoonup> x"
          apply (subst sbHdElem_2_shd)
            apply (meson da_conc_sbhdel_well2 sbHdElemWell_def)
           apply (simp add: assms_x_in_dom the_sb_def)
          by (metis (no_types, lifting) One_nat_def assms_x_in_dom da_conc_hd2 da_conc_sbhdel_well2 
              sbHdElemWell_def sbHdElem_2_shd sbhd_getch sbhd_sbdom shd1 stake_Suc surj_scons the_sb_def)
      qed
      then show ?thesis 
        by (metis convdiscrup_inv_dom_eq da_conc_hd2 da_conc_sbhdel_well2 part_eq sbHdElemWell_def 
            sbHdElem_channel sbHdElem_dom sbhd_sbdom the_sb_def)
    qed
    then have "(Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(ubConc (sbHd\<cdot>the_sb)\<cdot>da_sb)))) = sbEl"
      by (simp add: Rep_sbElem_inverse the_sb_def)
    then  have spfStep_dif: "spfStep In Out\<cdot>(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(x sbEl)) \<rightleftharpoons> (ubConcEq (sbHd\<cdot>the_sb)\<cdot>da_sb) \<noteq> 
                    spfStep In Out\<cdot>(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(y sbEl)) \<rightleftharpoons> (ubConcEq (sbHd\<cdot>the_sb)\<cdot>da_sb)"
      apply (simp add: spfStep_2_spfStep_inj assms the_sb_dom da_sb_dom)
      apply (simp add: spfStep_inj_def da_conc_sbhdel_well2)
      apply (subst ufRestrict_apply)
        apply (simp add: x_y_dom_ran) +
      apply (simp add: da_conc_rt2)
      by (simp add: da_sb_def)
    then have "spfStep In Out\<cdot>(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(x sbEl)) \<noteq> 
                    spfStep In Out\<cdot>(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(y sbEl))"
      apply (simp add: spfStep_def assms)
      using assm_result_eq spfStep_dif by auto
    then show False
      by (simp add: assm_result_eq)
  qed
  (* chain *)
  have setfilter_chain: "chain (\<lambda> i. ?H (Y i))"
    apply (rule chainI)
    by (simp add: a1 monofun_cfun_arg po_class.chainE)
  have setfilter_lub: "?H (Lub Y) = (\<Squnion> i. ?H (Y i))"
    by (simp add: a1 contlub_cfun_arg)
  have chain_big: "chain (\<lambda> i::nat. Abs_uspec (setrevImage (\<lambda>h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun. spfStep In Out\<cdot>(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl))) (?H (Y i)), Discr In, Discr Out))"
    apply (rule chainI)
    by (metis (no_types, lifting) a2 po_class.chain_def)
  have rep_lub: "Rep_uspec (\<Squnion>i::nat. Abs_uspec (setrevImage (\<lambda>h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun. spfStep In Out\<cdot>(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl))) (?H (Y i)), Discr In, Discr Out)) = 
     (\<Squnion>i::nat. (setrevImage (\<lambda>h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun. spfStep In Out\<cdot>(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl))) (?H (Y i)), Discr In, Discr Out))"
    apply (simp add: chain_big cont2contlubE)
    by (simp add: assms spsStep_uspecWell)
  have pair_lub_rev: "(\<Squnion>i::nat. (setrevImage (\<lambda>h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun. spfStep In Out\<cdot>(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl))) (?H (Y i)), Discr In, Discr Out)) = 
((\<Squnion>i::nat. (setrevImage (\<lambda>h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun. spfStep In Out\<cdot>(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl))) (?H (Y i)))), (Discr In), (Discr Out))"
  proof (subst lub_Pair, simp_all)
    have "\<forall>n. setrevFilter (spsStep_P In Out)\<cdot> (spsStep_h\<cdot>(Y n)) \<sqsubseteq> setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y (Suc n)))"
      by (metis (no_types) po_class.chain_def setfilter_chain)
    then show "chain (\<lambda>n. setrevImage (\<lambda>f. spfStep In Out\<cdot>(\<lambda>s. spfRtIn\<cdot>(f s))) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y n))))"
      using po_class.chain_def spsStep_mono_h by blast
  qed
  show "Abs_uspec (setrevImage (\<lambda>h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun. spfStep In Out\<cdot>(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl))) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(\<Squnion>i::nat. Y i))), Discr In, Discr Out) \<sqsubseteq>
       (\<Squnion>i::nat. Abs_uspec (setrevImage (\<lambda>h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun. spfStep In Out\<cdot>(\<lambda>sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl))) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i))), Discr In, Discr Out))"
    apply (simp add: below_uspec_def)
    apply (simp add: assms spsStep_uspecWell)
    apply (subst rep_lub)
    apply (simp add: pair_lub_rev setfilter_lub)
    apply (subst setreImage_lub_inj_on)
    by (simp_all add: a1 inj_on_i)
qed

lemma spsStep_cont[simp]: assumes "finite In" 
  shows "cont (\<lambda> h. spsStep_m In Out h)"
  by (simp add: spsStep_m_def assms)

*)


(*NewSpsStep Lemma End*)
(*******************************************************************)
subsection \<open>spsStep_m  utils\<close>
(*******************************************************************)
lemma spstep_m_dom[simp]: assumes "finite In" shows "uspecDom\<cdot>(spsStep_m In Out H) = In"
  by (simp add: spsStep_m_def assms uspecdom_insert)

lemma spstep_m_ran[simp]: assumes "finite In" shows "uspecRan\<cdot>(spsStep_m In Out H) = Out"
  by (simp add: spsStep_def spsStep_m_def  uspecran_insert assms)

lemma spsstep_m_insert:
  "spsStep_m In Out H = 
    Abs_uspec ((setrevImage (\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) 
          (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H))), Discr  In, Discr Out)"
  by (simp add: spsStep_m_def)

lemma spsstep_m_not_empty: assumes "spsStep_m In Out h \<noteq> uspecMax In Out"
  shows "spsStep_h\<cdot>h \<noteq> Rev {}"
  by (metis (no_types, lifting) assms ex_in_conv image_iff inv_rev_rev setrevImage_def 
        setrevfilter_included setrevfilter_insert spsStep_m_def uspecMax.abs_eq)

lemma spsstep_m_ele: "\<And> H f. finite In \<Longrightarrow> f \<in> (inv Rev (spsStep_h\<cdot>H)) \<Longrightarrow> spsStep_P In Out f \<Longrightarrow>
  uspec_in ((\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) f) (spsStep_m In Out H)"
proof - 
  fix H::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun uspec"
  fix f::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun"
  assume a1: "finite In"
  assume a2: "f \<in> (inv Rev (spsStep_h\<cdot>H))"
  assume a3: "spsStep_P In Out f"
  have f1: "f \<in> (inv Rev (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H)))"
    by (simp add: a2 a3 setrevfilter_reversed)
  show "uspec_in ((\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) f) (spsStep_m In Out H)"
    apply (simp add: spsstep_m_insert a1)
    apply (simp add: uspecrevset_insert a1)
    by (simp add: f1 inv_rev_rev setrevImage_def)
qed

lemma spsstep_ele_rev:  "\<And> H f. finite In \<Longrightarrow> 
uspec_in g (spsStep_m In Out H) \<Longrightarrow>
\<exists> f \<in> (inv Rev (spsStep_h\<cdot>H)). spsStep_P In Out f 
  \<and> g = ((\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) f) "
proof -
  fix H :: "'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun uspec" and f :: 'b
  assume a1: "uspec_in g (spsStep_m In Out H)"
  assume a2: "finite In"
  obtain uu :: "('a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun) set \<Rightarrow> (('a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun) \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun) 
  \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun \<Rightarrow> 'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun" where
    f3: "\<forall>x0 x1 x2. (\<exists>v3. x2 = x1 v3 \<and> v3 \<in> x0) = (x2 = x1 (uu x0 x1 x2) \<and> uu x0 x1 x2 \<in> x0)"
    by moura
  have f4: "Set.filter (spsStep_P In Out) (inv Rev (spsStep_h\<cdot>H)) = inv Rev (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H))"
    by (simp add: inv_rev_rev setrevfilter_insert)
  have "spsStep_m In Out H = Abs_uspec (setrevImage (\<lambda>f. spfStep In Out\<cdot>(\<lambda>s. spfRtIn\<cdot>(f s))) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H)), Discr In, Discr Out)"
    using a2 by (simp add: spsstep_m_insert)
  then have "g \<in> (\<lambda>f. spfStep In Out\<cdot>(\<lambda>s. spfRtIn\<cdot>(f s))) ` Set.filter (spsStep_P In Out) (inv Rev (spsStep_h\<cdot>H))"
    using f4 a2 a1 by (metis (no_types) rep_abs_rev_simp setrevImage_def spsStep_uspecWell_h uspecrevset_insert)
  then have f5: "g = spfStep In Out\<cdot> (\<lambda>s. spfRtIn\<cdot> (uu (Set.filter (spsStep_P In Out) (inv Rev (spsStep_h\<cdot>H))) (\<lambda>f. spfStep In Out\<cdot>(\<lambda>s. spfRtIn\<cdot>(f s))) g s)) \<and> uu (Set.filter (spsStep_P In Out) (inv Rev (spsStep_h\<cdot>H))) (\<lambda>f. spfStep In Out\<cdot>(\<lambda>s. spfRtIn\<cdot>(f s))) g \<in> Set.filter (spsStep_P In Out) (inv Rev (spsStep_h\<cdot>H))"
using f3 by (meson imageE)
have "\<forall>f p F. ((f::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun) \<in> Set.filter p F) = (f \<in> F \<and> p f)"
  using member_filter by blast
then show "\<exists>f\<in>inv Rev (spsStep_h\<cdot>H). spsStep_P In Out f \<and> g = spfStep In Out\<cdot>(\<lambda>s. spfRtIn\<cdot>(f s))"
    using f5 by meson
qed

(*******************************************************************)
subsection \<open>spsStep utils\<close>
(*******************************************************************)
(*
lemma spstep_dom[simp]: assumes "finite In" shows "uspecDom\<cdot>(spsStep In Out\<cdot>H) = In"
  by (simp add: spsStep_def spsStep_m_def uspecdom_insert assms)

lemma spstep_ran[simp]: assumes "finite In" shows "uspecRan\<cdot>(spsStep In Out\<cdot>H) = Out"
  by (simp add: spsStep_def spsStep_m_def uspecran_insert assms)

lemma spstep_m_dom[simp]: assumes "finite In" shows "uspecDom\<cdot>(spsStep_m In Out H) = In"
  by (simp add: spsStep_m_def assms uspecdom_insert)

lemma spstep_m_ran[simp]: assumes "finite In" shows "uspecRan\<cdot>(spsStep_m In Out H) = Out"
  by (simp add: spsStep_def spsStep_m_def  uspecran_insert assms)

lemma spsstep_2_spsstep_m: assumes "finite In" 
  shows "spsStep In Out\<cdot>H = spsStep_m In Out H"
  by (simp add: spsStep_def assms)



lemma spsstep_ele: "\<And> H f. finite In \<Longrightarrow> f \<in> (inv Rev (spsStep_h\<cdot>H)) \<Longrightarrow> spsStep_P In Out f \<Longrightarrow>
  uspec_in ((\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) f) (spsStep In Out\<cdot>H)"
proof - 
  fix H::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun uspec"
  fix f::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun"
  assume a1: "finite In"
  assume a2: "f \<in> (inv Rev (spsStep_h\<cdot>H))"
  assume a3: "spsStep_P In Out f"
  have f1: "f \<in> (inv Rev (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H)))"
    by (simp add: a2 a3 setrevfilter_reversed)
  show "uspec_in ((\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) f) (spsStep In Out\<cdot>H)"
    apply (simp add: spsstep_insert a1)
    apply (simp add: uspecrevset_insert a1)
    by (simp add: f1 inv_rev_rev setrevImage_def)
qed

lemma spsstep_ele_rev:  "\<And> H f. finite In \<Longrightarrow> 
uspec_in g (spsStep In Out\<cdot>H) \<Longrightarrow>
\<exists> f \<in> (inv Rev (spsStep_h\<cdot>H)). spsStep_P In Out f 
  \<and> g = ((\<lambda> h. spfStep In Out\<cdot>((\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) h)) f) "
proof -
  fix H :: "'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun uspec" and f :: 'b
  assume a1: "uspec_in g (spsStep In Out\<cdot>H)"
  assume a2: "finite In"
  obtain uu :: "('a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun) set \<Rightarrow> (('a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun) \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun) 
  \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun \<Rightarrow> 'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun" where
    f3: "\<forall>x0 x1 x2. (\<exists>v3. x2 = x1 v3 \<and> v3 \<in> x0) = (x2 = x1 (uu x0 x1 x2) \<and> uu x0 x1 x2 \<in> x0)"
    by moura
  have f4: "Set.filter (spsStep_P In Out) (inv Rev (spsStep_h\<cdot>H)) = inv Rev (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H))"
    by (simp add: inv_rev_rev setrevfilter_insert)
  have "spsStep In Out\<cdot>H = Abs_uspec (setrevImage (\<lambda>f. spfStep In Out\<cdot>(\<lambda>s. spfRtIn\<cdot>(f s))) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H)), Discr In, Discr Out)"
    using a2 by (simp add: spsstep_insert)
  then have "g \<in> (\<lambda>f. spfStep In Out\<cdot>(\<lambda>s. spfRtIn\<cdot>(f s))) ` Set.filter (spsStep_P In Out) (inv Rev (spsStep_h\<cdot>H))"
    using f4 a2 a1 by (metis (no_types) rep_abs_rev_simp setrevImage_def spsStep_uspecWell_h uspecrevset_insert)
  then have f5: "g = spfStep In Out\<cdot> (\<lambda>s. spfRtIn\<cdot> (uu (Set.filter (spsStep_P In Out) (inv Rev (spsStep_h\<cdot>H))) (\<lambda>f. spfStep In Out\<cdot>(\<lambda>s. spfRtIn\<cdot>(f s))) g s)) \<and> uu (Set.filter (spsStep_P In Out) (inv Rev (spsStep_h\<cdot>H))) (\<lambda>f. spfStep In Out\<cdot>(\<lambda>s. spfRtIn\<cdot>(f s))) g \<in> Set.filter (spsStep_P In Out) (inv Rev (spsStep_h\<cdot>H))"
using f3 by (meson imageE)
have "\<forall>f p F. ((f::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>,'a stream\<^sup>\<Omega>) ufun) \<in> Set.filter p F) = (f \<in> F \<and> p f)"
  using member_filter by blast
then show "\<exists>f\<in>inv Rev (spsStep_h\<cdot>H). spsStep_P In Out f \<and> g = spfStep In Out\<cdot>(\<lambda>s. spfRtIn\<cdot>(f s))"
    using f5 by meson
qed

*)

end
  