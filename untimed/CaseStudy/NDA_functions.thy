theory NDA_functions
  
imports Automaton "../../USpec"
    
begin
  
default_sort type
type_synonym 'm SPS = "'m SPF uspec"

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
  
lemma image_mono[simp]:"monofun (\<lambda> S.  f ` S)"
  apply(rule monofunI)
  by (simp add: SetPcpo.less_set_def image_mono)

lemma image_cont[simp]:"cont (\<lambda> S.  f ` S)"
  apply(rule contI2, simp)
  apply auto
  unfolding  SetPcpo.less_set_def
  unfolding lub_eq_Union
  by blast           
        
definition setflat_sps_rev:: "'m::message SPS set rev \<rightarrow> 'm SPS" where (*only in mono iff all SPS have the same Dom and Range, can be changed later with if then else*)
"setflat_sps_rev = (\<Lambda> spss. Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec ` (inv Rev spss))))"

lemma setflat_sps_rev_mono[simp]:"monofun(\<lambda> spss::'m::message SPS set rev. Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec `(inv Rev spss))))" 
proof(rule monofunI)
  fix x y:: "'m::message SPS set rev"
  assume a1:"x\<sqsubseteq>y"
  have h1:"inv Rev y \<subseteq> inv Rev x"
    by (metis SetPcpo.less_set_def a1 below_rev.elims(2) inv_rev_rev) 
  have h2:"(Rep_rev_uspec `(inv Rev y)) \<subseteq> (Rep_rev_uspec `(inv Rev x))"
    using h1 by blast
  have h3:"(setflat\<cdot>(Rep_rev_uspec `(inv Rev y))) \<sqsubseteq> (setflat\<cdot>(Rep_rev_uspec `(inv Rev x)))"
    by (metis SetPcpo.less_set_def cont_pref_eq1I h2)
  have h4:"uspecWell (setflat\<cdot>(Rep_rev_uspec `(inv Rev y)))"
    sorry
  have h5:"uspecWell (setflat\<cdot>(Rep_rev_uspec `(inv Rev x)))"
    sorry
  then show"Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec `(inv Rev x))) \<sqsubseteq> Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec `(inv Rev y)))"
    by (metis h3 h4 rep_abs_rev_simp uspec_belowI)
qed
  
lemma setflat_sps_rev_cont[simp]:"cont(\<lambda> spss::'m::message SPS set rev. Abs_rev_uspec (setflat\<cdot>(Rep_rev_uspec `(inv Rev spss))))"  
  sorry
    
    
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

(*Dunno... ist komisch*)
definition test::"(('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) set rev) \<rightarrow> (('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB)) set rev" where
"test = (\<Lambda> f. (Rev {(\<lambda>e. if e = x then s else (fst(s),ubLeast (ubDom\<cdot>(snd s)))) | s x. s \<in> (inv Rev (f x))}))"

lemma test_mono[simp]:"monofun (\<lambda> f::(('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) set rev). (Rev {(\<lambda>e. if e = x then s else (fst(s),ubLeast (ubDom\<cdot>(snd s)))) | s x. s \<in> (inv Rev (f x))}))"
  apply(rule rev_monoI)
  by (smt Collect_mono_iff SetPcpo.less_set_def below_rev.elims(2) fun_below_iff inv_rev_rev subsetCE)

lemma test_cont[simp]:"cont (\<lambda> f::(('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) set rev). (Rev {(\<lambda>e. if e = x then s else (fst(s),ubLeast (ubDom\<cdot>(snd s)))) | s x. s \<in> (inv Rev (f x))}))"
  sorry
  
  
definition test2::"('s \<Rightarrow> 'm::message SPS) \<rightarrow> ('s \<Rightarrow> 'm SPF)set rev"where
"test2 = (\<Lambda> spsf. (Rev {(\<lambda>e. if e = x then spf else ufLeast (ufDom\<cdot> spf) (ufDom\<cdot> spf)) | spf x. spf \<in> (Rep_rev_uspec (spsf x))}))"

lemma test2_mono[simp]:"monofun (\<lambda> spsf::('s \<Rightarrow> 'm::message SPS). (Rev {(\<lambda>e. if e = x then spf else ufLeast (ufDom\<cdot> spf) (ufDom\<cdot> spf)) | spf x. spf \<in> (Rep_rev_uspec (spsf x))}))"
  apply(rule rev_monoI)
  by (smt Collect_mono SetPcpo.less_set_def fun_below_iff uspec_ele_below)
  
lemma test2_cont[simp]:"cont (\<lambda> spsf::('s \<Rightarrow> 'm::message SPS). (Rev {(\<lambda>e. if e = x then spf else ufLeast (ufDom\<cdot> spf) (ufDom\<cdot> spf)) | spf x. spf \<in> (Rep_rev_uspec (spsf x))}))"
  sorry
    
end
  