theory NDA_functions
  
imports dAutomaton spec.USpec spec.USpec_Comp
    
begin
  
default_sort type
type_synonym 'm SPS = "'m SPF uspec"

(* ToDo: Move to SetPcpo *)
definition setflat :: "'a set set \<rightarrow> 'a set" where
"setflat = (\<Lambda> S. {K  | Z K. K\<in>Z \<and> Z \<in>S} )"

lemma setflat_mono: "monofun (\<lambda> S. {K  | Z K. K\<in>Z \<and> Z \<in>S} )"
  apply(rule monofunI)
  apply auto
  by (smt SetPcpo.less_set_def mem_Collect_eq subsetCE subsetI)

lemma setflat_cont: "cont (\<lambda> S. {K  | Z K. K\<in>Z \<and> Z \<in>S} )"
  apply(rule contI2)
  using setflat_mono apply simp
  apply auto
  unfolding  SetPcpo.less_set_def
  unfolding lub_eq_Union
  by blast

lemma setflat_insert: "setflat\<cdot>S = {K  | Z K. K\<in>Z \<and> Z \<in>S}"
  unfolding setflat_def
  by (metis (mono_tags, lifting) Abs_cfun_inverse2 setflat_cont)  
    
lemma setflat_empty:"(setflat\<cdot>S = {}) \<longleftrightarrow> (\<forall>x\<in>S. x = {})"
  by(simp add: setflat_insert, auto)
  
lemma image_mono[simp]:"monofun (\<lambda> S.  f ` S)"
  apply(rule monofunI)
  by (simp add: SetPcpo.less_set_def image_mono)

lemma image_cont[simp]:"cont (\<lambda> S.  f ` S)"
  apply(rule contI2, simp)
  apply auto
  unfolding  SetPcpo.less_set_def
  unfolding lub_eq_Union
  by blast           
        (*
definition setflat_sps_rev:: "channel set \<Rightarrow> channel set \<Rightarrow> 'm::message SPS set rev \<rightarrow> 'm SPS" where (*Problem if SPS is not consistent*)
"setflat_sps_rev In Out = (\<Lambda> spss. (if (\<forall>sps\<in>(inv Rev spss). uspecDom sps = In \<and> uspecRan sps = Out) then Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` (inv Rev spss))) else uspecLeast In Out))"

lemma setflat_sps_rev_mono[simp]:"monofun(\<lambda> spss::'m::message SPS set rev. (if (\<forall>sps\<in>(inv Rev spss). uspecDom sps = In \<and> uspecRan sps = Out) then Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` (inv Rev spss))) else uspecLeast In Out))" 
proof(rule monofunI)
  fix x y:: "'m::message SPS set rev"
  assume a1:"x\<sqsubseteq>y"
  have h1:"inv Rev y \<subseteq> inv Rev x"
    by (metis SetPcpo.less_set_def a1 below_rev.elims(2) inv_rev_rev) 
  have h2:"(Rep_rev_uspec `(inv Rev y)) \<subseteq> (Rep_rev_uspec `(inv Rev x))"
    using h1 by blast
  have h3:"(setflat\<cdot>(Rep_rev_uspec `(inv Rev y))) \<sqsubseteq> (setflat\<cdot>(Rep_rev_uspec `(inv Rev x)))"
    by (metis SetPcpo.less_set_def cont_pref_eq1I h2)
  then show"(if \<forall>sps::('m stream\<^sup>\<Omega>) ufun uspec\<in>inv Rev x. uspecDom sps = In \<and> uspecRan sps = Out then Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` inv Rev x)) else uspecLeast In Out) \<sqsubseteq>
       (if \<forall>sps::('m stream\<^sup>\<Omega>) ufun uspec\<in>inv Rev y. uspecDom sps = In \<and> uspecRan sps = Out then Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` inv Rev y)) else uspecLeast In Out)"
  proof(cases "\<forall>sps::('m stream\<^sup>\<Omega>) ufun uspec\<in>inv Rev x. uspecDom sps = In \<and> uspecRan sps = Out")
    case True
    then have True_2:"\<forall>sps::('m stream\<^sup>\<Omega>) ufun uspec\<in>inv Rev y. uspecDom sps = In \<and> uspecRan sps = Out"
      using h1 by blast
    have h4:"uspecWell (setflat\<cdot>(Rep_rev_uspec `(inv Rev y)))"
      apply(simp add: uspecWell_def)
      apply(rule_tac x="In" in exI)
      apply(rule_tac x="Out" in exI)
      by (smt Abs_cfun_inverse2 True_2 f_inv_into_f inv_into_into mem_Collect_eq setflat_cont setflat_def uspec_dom_eq uspec_ran_eq)
    have h5:"uspecWell (setflat\<cdot>(Rep_rev_uspec `(inv Rev x)))"
          apply(simp add: uspecWell_def)
      apply(rule_tac x="In" in exI)
      apply(rule_tac x="Out" in exI)
      by (smt Abs_cfun_inverse2 True f_inv_into_f inv_into_into mem_Collect_eq setflat_cont setflat_def uspec_dom_eq uspec_ran_eq)
    then show ?thesis 
      by (smt True True_2 h3 h4 rep_abs_rev_simp uspec_belowI)
  next
    case False
    then show ?thesis
    proof(cases "\<forall>sps::('m stream\<^sup>\<Omega>) ufun uspec\<in>inv Rev y. uspecDom sps = In \<and> uspecRan sps = Out")
      case True
      have f1:"\<forall>f\<in>(setflat\<cdot>(Rep_rev_uspec ` inv Rev y)). ufclDom\<cdot>f = In \<and> ufclRan\<cdot>f = Out"
        by (smt Abs_cfun_inverse2 True f_inv_into_f inv_into_into mem_Collect_eq setflat_cont setflat_def uspec_dom_eq uspec_ran_eq)
      then have uspecWelly:"uspecWell (setflat\<cdot>(Rep_rev_uspec ` inv Rev y))"
        by(simp add: uspecWell_def)
      then show ?thesis
        apply(cases "(setflat\<cdot>(Rep_rev_uspec ` inv Rev y)) = {}")
        apply (smt True empty_max)
        by (smt CollectI False SetPcpo.less_set_def f1 rep_abs_rev_simp subsetI uspecLeast_def uspecLeast_well uspec_belowI)
    next
      case False
      then show ?thesis
        by (smt h1 po_eq_conv subsetCE)
    qed
  qed
qed
  
lemma setflat_sps_rev_cont_helper:assumes "chain (Y::nat \<Rightarrow> 'm::message SPS set rev)" shows "\<forall>sps\<in>inv Rev (Y n). uspecDom sps = In \<and> uspecRan sps = Out \<Longrightarrow> \<forall>i\<ge>n. \<forall>sps\<in>inv Rev (Y i). uspecDom sps = In \<and> uspecRan sps = Out"
proof-
  assume a1:"\<forall>sps\<in>inv Rev (Y n). uspecDom sps = In \<and> uspecRan sps = Out"
  have "\<forall>i\<ge>n. inv Rev (Y i) \<sqsubseteq> inv Rev (Y n)"
    by (metis assms below_rev.simps inv_rev_rev po_class.chain_mono rev.exhaust)
  then have "\<forall>i\<ge>n. inv Rev (Y i) \<subseteq> inv Rev (Y n)"
    by (simp add: SetPcpo.less_set_def)
  then show "\<forall>i\<ge>n. \<forall>sps\<in>inv Rev (Y i). uspecDom sps = In \<and> uspecRan sps = Out"
    by (meson a1 set_mp)
qed
  
  
lemma setflat_sps_rev_cont[simp]:"cont(\<lambda> spss::'m::message SPS set rev. (if (\<forall>sps\<in>(inv Rev spss). uspecDom sps = In \<and> uspecRan sps = Out) then Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` (inv Rev spss))) else uspecLeast In Out))" 
proof(rule Cont.contI2, simp)
  fix Y ::"nat \<Rightarrow> 'm SPS set rev"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. if \<forall>sps::('m stream\<^sup>\<Omega>) ufun uspec\<in>inv Rev (Y i). uspecDom sps = In \<and> uspecRan sps = Out then Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` inv Rev (Y i)))
                       else uspecLeast In Out)"
  have "\<forall>i. inv Rev (\<Squnion>i.  Y i) \<subseteq> inv Rev (Y i)"
    by (metis SetPcpo.less_set_def a1 below_rev.elims(2) inv_rev_rev is_ub_thelub)
  then have a3:"\<exists>i. \<forall>sps\<in>inv Rev (Y i). uspecDom sps = In \<and> uspecRan sps = Out  \<Longrightarrow> \<forall>sps\<in>inv Rev (\<Squnion>i. Y i). uspecDom sps = In \<and> uspecRan sps = Out"
    by blast
  show "(if \<forall>sps\<in>inv Rev (\<Squnion>i. Y i). uspecDom sps = In \<and> uspecRan sps = Out then Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` inv Rev (\<Squnion>i. Y i)))
        else uspecLeast In Out) \<sqsubseteq>
       (\<Squnion>i. if \<forall>sps\<in>inv Rev (Y i). uspecDom sps = In \<and> uspecRan sps = Out then Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` inv Rev (Y i)))
                  else uspecLeast In Out)"
  proof(cases "\<exists>i. \<forall>sps\<in>inv Rev (Y i). uspecDom sps = In \<and> uspecRan sps = Out")
    case True
    then have "(if \<forall>sps\<in>inv Rev (\<Squnion>i. Y i). uspecDom sps = In \<and> uspecRan sps = Out then Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` inv Rev (\<Squnion>i::nat. Y i)))
        else uspecLeast In Out) = Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` inv Rev (\<Squnion>i. Y i)))"
      using a3 by presburger
    obtain n where n_def:"\<forall>sps\<in>inv Rev (Y n). uspecDom sps = In \<and> uspecRan sps = Out"
      using True by auto
    have h1:"\<forall>i\<ge>n. (if \<forall>sps\<in>inv Rev (Y i). uspecDom sps = In \<and> uspecRan sps = Out then Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` inv Rev (Y i)))
                  else uspecLeast In Out) = (Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` inv Rev (Y i))))"
      by (meson a1 n_def setflat_sps_rev_cont_helper)
    then have "\<forall>i\<ge>n.(if \<forall>sps\<in>inv Rev (Y i). uspecDom sps = In \<and> uspecRan sps = Out then Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` inv Rev (Y i)))
                  else uspecLeast In Out) \<sqsubseteq> (\<Squnion>i. if \<forall>sps\<in>inv Rev (Y i). uspecDom sps = In \<and> uspecRan sps = Out then Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` inv Rev (Y i)))
                  else uspecLeast In Out)"
      using a2 is_ub_thelub by blast
    then have "\<forall>i\<ge>n. (Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` inv Rev (Y i)))) \<sqsubseteq> (\<Squnion>i. if \<forall>sps\<in>inv Rev (Y i). uspecDom sps = In \<and> uspecRan sps = Out then Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` inv Rev (Y i)))
                  else uspecLeast In Out)"
      by (simp add: h1)
    then show ?thesis
      sorry
  next
    case False
    then show ?thesis sorry
  qed
qed*)
  
    
    
(*                                                             
definition spsConc_set::"('m::message SB) set rev \<Rightarrow> 'm SPS \<rightarrow> 'm SPS"where (*or with 'm SB set input and with out inv Rev in function*)
"spsConc_set s = (\<Lambda> sps. setflat_sps\<cdot>{spsConc sb\<cdot>sps | sb. sb \<in> (inv Rev s)})"

definition spsRt_set:: "'m::message SPS set rev \<rightarrow> 'm SPS" where
"spsRt_set = (\<Lambda> spss. Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec`(inv Rev spss))))"

definition set_snd::"(('s \<times> 'm::message SB) set rev) \<rightarrow> (('m::message SB) set rev)" where
"set_snd \<equiv> \<Lambda> x. Rev (snd`(inv Rev x))"

definition set_fst::"(('s \<times> 'm::message SB) set rev) \<rightarrow> ('s set rev)" where
"set_fst \<equiv> \<Lambda> x. Rev (fst`(inv Rev x))"
*)  
(*proof(rule Cont.contI2, subst test_mono,auto)
  fix Y::"nat \<Rightarrow> 's \<times> 'e \<Rightarrow> ('s \<times> 'm::message stream\<^sup>\<Omega>) set rev"
  assume a1:"chain Y"
  assume a2:" chain (\<lambda>i::nat. Rev {\<lambda>e::'s \<times> 'e. if e = (aa, ba) then (a, b) else (fst (a, b), ubLeast (ubDom\<cdot>(snd (a, b)))) |(a::'s) (b::'m stream\<^sup>\<Omega>) (aa::'s) ba::'e.
                            (a, b) \<in> inv Rev (Y i (aa, ba))})"
  have a3:"\<And>i aa ba. inv Rev (Lub Y (aa, ba)) \<subseteq> inv Rev (Y i (aa, ba))"
    by (smt SetPcpo.less_set_def a1 below_rev.elims(2) fun_below_iff inv_rev_rev is_ub_thelub)
  then have a4:"\<And>i. {\<lambda>e. if e = (aa, ba) then (a, b) else (fst (a, b), ubLeast (ubDom\<cdot>(snd (a, b)))) |a b aa ba.
            (a, b) \<in> inv Rev (Lub Y (aa, ba))} \<subseteq> {\<lambda>e. if e = (aa, ba) then (a, b) else (fst (a, b), ubLeast (ubDom\<cdot>(snd (a, b)))) |a b aa ba.
                       (a, b) \<in> inv Rev (Y i (aa, ba))}"
    by blast
  show "Rev {\<lambda>e. if e = (aa, ba) then (a, b) else (fst (a, b), ubLeast (ubDom\<cdot>(snd (a, b)))) |a b aa ba.
            (a, b) \<in> inv Rev (Lub Y (aa, ba))} \<sqsubseteq>
       (\<Squnion>i. Rev {\<lambda>e. if e = (aa, ba) then (a, b) else (fst (a, b), ubLeast (ubDom\<cdot>(snd (a, b)))) |a b aa ba.
                       (a, b) \<in> inv Rev (Y i (aa, ba))})"
    sorry
qed
  *)
  
  
definition test2::"('s \<Rightarrow> 'm::message SPS) \<rightarrow> ('s \<Rightarrow> 'm SPF)set rev"where
"test2 = (\<Lambda> spsf. setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(spsf e)))"
(*
lemma test2_mono[simp]:"monofun (\<lambda> spsf::('s \<Rightarrow> 'm::message SPS). (Rev {(\<lambda>e. if e = x then spf else ufLeast (ufDom\<cdot> spf) (ufDom\<cdot> spf)) | spf x. spf \<in> (Rep_rev_uspec (spsf x))}))"
  apply(rule rev_monoI)
  by (smt Collect_mono SetPcpo.less_set_def fun_below_iff )
 
    
    
lemma test2_cont[simp]:"cont (\<lambda> spsf::('s \<Rightarrow> 'm::message SPS). (Rev {(\<lambda>e. if e = x then spf else ufLeast (ufDom\<cdot> spf) (ufDom\<cdot> spf)) | spf x. spf \<in> (Rep_rev_uspec (spsf x))}))"
proof(rule Cont.contI2,simp)
  fix Y::"nat \<Rightarrow> 's \<Rightarrow> 'm SPS"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. Rev {\<lambda>e::'s. if e = x then spf else ufLeast (ufDom\<cdot>spf) (ufDom\<cdot>spf) |(spf::('m stream\<^sup>\<Omega>) ufun) x::'s. spf \<in> Rep_rev_uspec (Y i x)})"
  have a3:"\<And>x. chain (\<lambda>i. Y i x)"
    by (simp add: a1 ch2ch_fun)
  then have h1:"Rev {\<lambda>e::'s. if e = x then spf else ufLeast (ufDom\<cdot>spf) (ufDom\<cdot>spf) |(spf::('m stream\<^sup>\<Omega>) ufun) x::'s. spf \<in> Rep_rev_uspec ((\<Squnion>i::nat. Y i) x)}
             = Rev {\<lambda>e::'s. if e = x then spf else ufLeast (ufDom\<cdot>spf) (ufDom\<cdot>spf) |(spf::('m stream\<^sup>\<Omega>) ufun) x::'s. spf \<in> Rep_rev_uspec ((\<Squnion>i::nat. Y i x))}"
    by (smt Collect_cong a1 lub_eq lub_fun rev.inject)
  show "Rev {\<lambda>e::'s. if e = x then spf else ufLeast (ufDom\<cdot>spf) (ufDom\<cdot>spf) |(spf::('m stream\<^sup>\<Omega>) ufun) x::'s. spf \<in> Rep_rev_uspec ((\<Squnion>i::nat. Y i) x)} \<sqsubseteq>
       (\<Squnion>i::nat. Rev {\<lambda>e::'s. if e = x then spf else ufLeast (ufDom\<cdot>spf) (ufDom\<cdot>spf) |(spf::('m stream\<^sup>\<Omega>) ufun) x::'s. spf \<in> Rep_rev_uspec (Y i x)})"  
    apply(simp add: h1)
  sorry
qed
  *)
end
  