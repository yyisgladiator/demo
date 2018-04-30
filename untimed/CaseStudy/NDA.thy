(* Draft for Non-Deterministic Automaton *)

theory NDA

imports Automaton "../../USpec"

begin

default_sort type
type_synonym 'm SPS = "'m SPF uspec"



section \<open>Non Deterministic Case \<close>

(* FYI: Non-deterministic version *)
cpodef ('state::type, 'm::message) NDA = 
  "{f::(('state \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> (('state \<times> 'm SB) set rev)) \<times> ('state \<times> 'm SB) set rev \<times> channel set discr \<times> channel set discr. True}"
  by auto

setup_lifting type_definition_NDA

(*
(* relation based on transition function and initial set *)
instantiation NDA :: (type, message) po
begin
  fun below_NDA :: "('a, 'b) NDA \<Rightarrow> ('a, 'b) NDA \<Rightarrow> bool" where
  "below_NDA n1 n2 = ((fst (Rep_NDA n2) \<sqsubseteq>  fst (Rep_NDA n1))  (* Transition function is subset. NOTICE: Reversed *)
                  \<and>   (fst (snd (Rep_NDA n2)) \<sqsubseteq>  fst (snd (Rep_NDA n1)))  (* Initial states subset. NOTICE: Reversed *)
                  \<and>   (fst (snd (snd (Rep_NDA n1))) =  fst (snd (snd (Rep_NDA n2))))  (* input domain identical *)
                  \<and>   (     (snd (snd (snd (Rep_NDA n1)))) =  (snd (snd (snd (Rep_NDA n2))))) )" (* output domain identical *)

instance
  apply(intro_classes)
    apply simp
  apply simp
  apply (meson below_trans)
  by (meson Rep_NDA_inject below_NDA.elims(2) below_antisym prod.expand)
end  

instance NDA :: (type, message) cpo 
  apply(intro_classes)
  apply (rule, rule is_lubI)
  sorry

*)


definition ndaTransition :: "('s, 'm::message) NDA \<rightarrow> (('s \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> (('s \<times> 'm SB) set rev))" where
"ndaTransition \<equiv> \<Lambda> nda. fst (Rep_NDA nda)"

definition ndaInitialState :: "('s, 'm::message) NDA \<rightarrow> ('s \<times> 'm SB) set rev" where
"ndaInitialState = (\<Lambda> nda. fst (snd (Rep_NDA nda)))"

definition ndaDom :: "('s, 'm::message) NDA \<rightarrow> channel set discr" where
"ndaDom = (\<Lambda> nda. fst (snd (snd (Rep_NDA nda))))"

definition ndaRan :: "('s, 'm::message) NDA \<rightarrow> channel set discr" where
"ndaRan =  (\<Lambda> nda. snd (snd (snd (Rep_NDA nda))))" 


(* See: https://git.rwth-aachen.de/montibelle/automaton/core/issues/59 *)
definition spsFix :: "('a \<rightarrow> 'a) \<rightarrow> 'a" where
"spsFix = undefined"  (* Die ganze function ist natürlich grober unsinn *)



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

(* Test it *)
lemma "setflat\<cdot>{{1,2::nat},{3,4::nat}} = {1,2,3,4}"
  unfolding setflat_insert
  apply blast (* Dauert ein bisschen, lösche das lemma wenn es nervt *)
  done



(* like spfStep, copy & pasteonly on SPS *)
fun spsStep :: "channel set discr \<Rightarrow> channel set discr \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPS) \<rightarrow> 'm SPS" where
"spsStep (Discr cin) (Discr cout) = undefined"




(* See: https://git.rwth-aachen.de/montibelle/automaton/core/issues/70 *)
definition spsConc:: "'m SB \<Rightarrow> 'm SPS \<rightarrow> 'm SPS" where
"spsConc = undefined"

(* See: https://git.rwth-aachen.de/montibelle/automaton/core/issues/70 *)
definition spsRt:: "'m SPS \<rightarrow> 'm SPS" where
"spsRt = undefined"

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
(* ToDo *)
(* Very Very similar to helper over automaton *)
thm helper_def

(* Es klappt aber nicht.... Der nichtdeterminismus wird nicht berücksichtigt! 
  und ich laufe immer wieder in das problem: https://git.rwth-aachen.de/montibelle/automaton/core/issues/68 *)

definition spsHelper:: "'s \<Rightarrow> (('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) set rev) \<rightarrow> ('s \<Rightarrow> 'm SPS) \<rightarrow> ('e \<Rightarrow> 'm SPS)" where(*Other Idea*)
"spsHelper s \<equiv> \<Lambda> f. \<Lambda> h. (\<lambda> e. Abs_rev_uspec((\<lambda>x. x e)`{Automaton.helper (spf) s\<cdot>x| spf x. spf\<in>(inv Rev (test\<cdot>f)) \<and> x \<in> (inv Rev (test2\<cdot>h))}))"

lemma spsHelpter_mono_inner:"monofun(\<lambda> h::('s \<Rightarrow> 'm::message SPS). (\<lambda> e. Abs_rev_uspec((\<lambda>x. x e)`{Automaton.helper (spf) s\<cdot>x| spf x. spf\<in>(inv Rev (test\<cdot>f)) \<and> x \<in> (inv Rev (test2\<cdot>h))})))"
proof(rule monofunI)
  fix x y::"('s \<Rightarrow> 'm::message SPS)"
  assume a1:"x \<sqsubseteq> y"
  have h1:"\<And>e. uspecWell ((\<lambda>x. x e)`
                  {helper spf s\<cdot>xa |(spf::'s \<times> 'a \<Rightarrow> 's \<times> 'm stream\<^sup>\<Omega>) xa::'s \<Rightarrow> ('m stream\<^sup>\<Omega>) ufun. spf \<in> inv Rev (test\<cdot>f) \<and> xa \<in> inv Rev (test2\<cdot>x)})"
    sorry
  have h2:"\<And>e. uspecWell ((\<lambda>x. x e)`
                  {helper spf s\<cdot>xa |(spf::'s \<times> 'a \<Rightarrow> 's \<times> 'm stream\<^sup>\<Omega>) xa::'s \<Rightarrow> ('m stream\<^sup>\<Omega>) ufun. spf \<in> inv Rev (test\<cdot>f) \<and> xa \<in> inv Rev (test2\<cdot>y)})"
    sorry
  have h3:"inv Rev (test2\<cdot>y)\<subseteq> inv Rev (test2\<cdot>x)"
    by (smt Abs_cfun_inverse2 SetPcpo.less_set_def a1 below_rev.simps inv_rev_rev monofun_cfun_arg test2_cont test2_def)
  then have h4:"{helper spf s\<cdot>x |spf x. spf \<in> inv Rev (test\<cdot>f) \<and> x \<in> inv Rev (test2\<cdot>y)} \<sqsubseteq> {helper spf s\<cdot>xa |spf xa. spf \<in> inv Rev (test\<cdot>f) \<and> xa \<in> inv Rev (test2\<cdot>x)}"
    by (smt Collect_mono SetPcpo.less_set_def subsetCE)    
  then have h5:"\<And>e. ((\<lambda>x. x e)`
                  {helper spf s\<cdot>xa |spf xa. spf \<in> inv Rev (test\<cdot>f) \<and> xa \<in> inv Rev (test2\<cdot>y)})\<sqsubseteq> ((\<lambda>x. x e)`
                  {helper spf s\<cdot>xa |spf xa. spf \<in> inv Rev (test\<cdot>f) \<and> xa \<in> inv Rev (test2\<cdot>x)})"
    by (simp add: Set.image_mono SetPcpo.less_set_def)
  show "(\<lambda>e. Abs_rev_uspec
                 ((\<lambda>x. x e)`
                  {helper spf s\<cdot>xa |spf xa. spf \<in> inv Rev (test\<cdot>f) \<and> xa \<in> inv Rev (test2\<cdot>x)})) \<sqsubseteq>
       (\<lambda>e. Abs_rev_uspec
                 ((\<lambda>x. x e)`
                  {helper spf s\<cdot>x |spf x. spf \<in> inv Rev (test\<cdot>f) \<and> x \<in> inv Rev (test2\<cdot>y)}))"
    by (smt fun_below_iff h1 h2 h4 h5 monofun_cfun_arg rep_abs_rev_simp uspec_belowI)
qed
  
  
    

lemma spsHelpter_cont_inner:"cont(\<lambda> h::('s \<Rightarrow> 'm::message SPS). (\<lambda> e. Abs_rev_uspec((\<lambda>x. x e)`{Automaton.helper (spf) s\<cdot>x| spf x. spf\<in>(inv Rev (test\<cdot>f)) \<and> x \<in> (inv Rev (test2\<cdot>h))})))"
  sorry
    
    
lemma spsHelpter_mono:"monofun(\<lambda>f::(('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) set rev). \<Lambda> h. (\<lambda> e. Abs_rev_uspec((\<lambda>x. x e)`{Automaton.helper (spf) s\<cdot>x| spf x. spf\<in>(inv Rev (test\<cdot>f)) \<and> x \<in> (inv Rev (test2\<cdot>h))})))"
proof(rule monofunI)
  fix x y::"(('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) set rev)"
  assume a1:"x \<sqsubseteq> y"
  have "test\<cdot>x \<sqsubseteq> test\<cdot>y"
    using a1 monofun_cfun_arg by blast
  then have h0:"inv Rev (test\<cdot>y) \<sqsubseteq> inv Rev (test\<cdot>x)"
    by (metis (no_types, lifting) below_rev.elims(2) inv_rev_rev)
  then have h1:"\<And>h f. f `{helper spf s\<cdot>xa |spf xa. spf \<in> inv Rev (test\<cdot>y) \<and> xa \<in> inv Rev (test2\<cdot>h)} \<sqsubseteq> f `{helper spf s\<cdot>xa |spf xa. spf \<in> inv Rev (test\<cdot>x) \<and> xa \<in> inv Rev (test2\<cdot>h)}"
    by (smt Collect_mono Set.image_mono SetPcpo.less_set_def subset_eq)
  have h2:"\<And>h e. uspecWell ((\<lambda>x. x e) `
                      {helper spf s\<cdot>xa |spf xa. spf \<in> inv Rev (test\<cdot>x) \<and> xa \<in> inv Rev (test2\<cdot>h)})"
    sorry
  have h3:"\<And>h e. uspecWell ((\<lambda>x. x e)`
                      {helper spf s\<cdot>xa |spf xa. spf \<in> inv Rev (test\<cdot>y) \<and> xa \<in> inv Rev (test2\<cdot>h)})"
    sorry
  have h4:"\<And>h . (\<lambda>e. Abs_rev_uspec
                     ((\<lambda>x. x e)`
                      {helper spf s\<cdot>xa |spf xa. spf \<in> inv Rev (test\<cdot>x) \<and> xa \<in> inv Rev (test2\<cdot>h)})) \<sqsubseteq> (\<lambda>e. Abs_rev_uspec
                     ((\<lambda>x. x e)`
                      {helper spf s\<cdot>xa |spf xa. spf \<in> inv Rev (test\<cdot>y) \<and> xa \<in> inv Rev (test2\<cdot>h)}))"
    by (smt fun_belowI h1 h2 h3 rep_abs_rev_simp uspec_belowI)
  show "(\<Lambda> h.
           (\<lambda>e. Abs_rev_uspec
                     ((\<lambda>x. x e)`
                      {helper spf s\<cdot>xa |spf xa. spf \<in> inv Rev (test\<cdot>x) \<and> xa \<in> inv Rev (test2\<cdot>h)}))) \<sqsubseteq>
       (\<Lambda> h.
           (\<lambda>e. Abs_rev_uspec
                     ((\<lambda>x. x e)`
                      {helper spf s\<cdot>x |spf x. spf \<in> inv Rev (test\<cdot>y) \<and> x \<in> inv Rev (test2\<cdot>h)})))" 
    by(rule cfun_belowI, simp add: spsHelpter_cont_inner h4)
qed

lemma spsHelpter_cont:"cont(\<lambda>f::(('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB) set rev). \<Lambda> h. (\<lambda> e. Abs_rev_uspec((\<lambda>x. x e)`{Automaton.helper (spf) s\<cdot>x| spf x. spf\<in>(inv Rev (test\<cdot>f)) \<and> x \<in> (inv Rev (test2\<cdot>h))})))"
  sorry
    
    
    
    
(* Similar to Rum96 *)
definition nda_h :: "('s::type, 'm::message) NDA \<rightarrow> ('s \<Rightarrow> 'm SPS)" where
"nda_h \<equiv>  \<Lambda> nda. spsFix\<cdot>(\<Lambda> h. (\<lambda>s. spsStep (ndaDom\<cdot>nda)(ndaRan\<cdot>nda)\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h)))"

lemma nda_h_mono:"monofun  (\<lambda> nda. spsFix\<cdot>(\<Lambda> h. (\<lambda>s. spsStep (ndaDom\<cdot>nda)(ndaRan\<cdot>nda)\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h))))"
  sorry


lemma nda_h_cont:"cont  (\<lambda> nda. spsFix\<cdot>(\<Lambda> h. (\<lambda>s. spsStep (ndaDom\<cdot>nda)(ndaRan\<cdot>nda)\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h))))"
  sorry
    
definition setrevImage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set rev \<rightarrow> 'b set rev" where
"setrevImage = undefined"

(* See: https://git.rwth-aachen.de/montibelle/automaton/core/issues/57 *)
definition uspecImage:: "('m::ufuncl \<Rightarrow> 'n::ufuncl) \<Rightarrow> 'm uspec \<rightarrow> 'n uspec" where
"uspecImage = undefined"

  
(* see: https://git.rwth-aachen.de/montibelle/automaton/core/issues/58 *)
definition uspecUnion:: "'m uspec \<rightarrow> 'm uspec \<rightarrow> 'm uspec" where
"uspecUnion = undefined"


(* Takes an tupel of the initial-state/output message... and returns the corresponding SPS *)
fun helper:: "('s \<times> 'm::message SB) \<Rightarrow> ('s::type, 'm::message) NDA \<rightarrow> 'm SPS" where
"helper (state, output) = (\<Lambda> nda. uspecImage (Rep_cfun (spfConc output))\<cdot>((nda_h\<cdot>nda) state))"


definition nda_H_helper :: "('s, 'm::message) NDA \<rightarrow> 'm SPS set rev" where
"nda_H_helper \<equiv> \<Lambda> nda. (setrevImage (\<lambda>t. helper t\<cdot>nda)\<cdot>(ndaInitialState\<cdot>nda))"

(* https://git.rwth-aachen.de/montibelle/automaton/core/issues/68 *)
definition nda_H :: "('s, 'm::message) NDA \<rightarrow> 'm SPS" where
"nda_H \<equiv> \<Lambda> nda. setflat_sps_rev\<cdot>(nda_H_helper\<cdot>nda)" 





lemma nda_rep_cont[simp]: "cont Rep_NDA"
proof -
  obtain nn :: "(('a, 'b) NDA \<Rightarrow> ('a \<times> (channel \<Rightarrow> 'b option) \<Rightarrow> ('a \<times> 'b stream\<^sup>\<Omega>) set rev) \<times> ('a \<times> 'b stream\<^sup>\<Omega>) set rev \<times> channel set discr \<times> channel set discr) \<Rightarrow> nat \<Rightarrow> ('a, 'b) NDA" where
    f1: "\<forall>f. chain (nn f) \<and> \<not> range (\<lambda>n. f (nn f n)) <<| f (Lub (nn f)) \<or> cont f"
using contI by moura
  have "Rep_NDA (Abs_NDA (\<Squnion>n. Rep_NDA (nn Rep_NDA n))) = (\<Squnion>n. Rep_NDA (nn Rep_NDA n))"
    using Abs_NDA_inverse by blast
then show ?thesis
  using f1 by (metis (no_types) below_NDA_def lub_NDA po_class.chain_def thelubE)
qed


lemma "cont (\<lambda>nda. fst (Rep_NDA nda))"
  by simp



lemma "cont (\<lambda> nda. spsFix\<cdot>(\<Lambda> h. (\<lambda>s. spsStep some suff\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h))))"
  by simp

lemma "cont (\<lambda> h. (\<lambda>s. spsStep (ndaDom\<cdot>nda)(ndaRan\<cdot>nda)\<cdot>(spsHelper s\<cdot>(ndaTransition\<cdot>nda)\<cdot>h)))"
  by simp


end