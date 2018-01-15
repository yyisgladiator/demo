(*  Title:        UBundle
    Author:       Sebastian, Jens, Marc

    Description:  Defines stream bundles
*)

theory UBundle_Pcpo
  imports UBundle
begin

  
default_sort uscl_pcpo

  
(****************************************************)
section\<open>Definitions\<close>
(****************************************************)  

  
(* ubLeast *)
text {* @{text "ubLeast"} creates a bundle with \<bottom> in each channel  *}
definition ubLeast :: "channel set \<Rightarrow> 'M\<^sup>\<Omega>"  where
"ubLeast cs \<equiv> Abs_ubundle (\<lambda>c. (c \<in> cs) \<leadsto> \<bottom> )"  

(* ubUp *)
text {* @{text "ubUp"}  replaces all "None" channels with \<bottom>. *}
definition ubUp:: " 'M\<^sup>\<Omega> \<rightarrow> 'M\<^sup>\<Omega>"  where
"ubUp \<equiv> \<Lambda> b . Abs_ubundle (\<lambda>c. if (c \<in> ubDom\<cdot>b) then (Rep_ubundle b) c else Some \<bottom>)"


(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)

  
subsection \<open>ubLeast\<close>

  
(* the optionLeast of the optionCpo is well-formed  *)
lemma ubleast_well: "ubWell ((optionLeast cs) :: channel \<Rightarrow> 'a option)"
  apply(simp add: optionLeast_def ubWell_def)
  by(simp add: usOkay_bot)

(* our definition of ubLeast is equal optionLeast  *)
lemma ubleast_optionLeast_eq: "ubLeast cs = Abs_ubundle(optionLeast cs)"
  by (simp add: ubLeast_def optionLeast_def)
  
(* the dom of ubLeast is the same as the argument of the function  *)
lemma ubleast_ubdom [simp]: "ubDom\<cdot>(ubLeast cs) = cs"
  apply (simp add: ubDom_def)
  by (metis ubleast_optionLeast_eq optionleast_dom ubdom_insert ubdom_ubrep_eq ubleast_well)

(* the element in each channel is the bottom element  *)
lemma ubleast_ubgetch[simp]:  assumes "c \<in> cs"
  shows "(ubLeast cs) . c = \<bottom>"
  by (simp add: assms ubgetch_ubrep_eq ubleast_optionLeast_eq ubleast_well)

(* the ubLeast bundle is the smallest bundle  *)
lemma ubleast_below [simp]: assumes "cs = ubDom\<cdot>ub"
  shows "ubLeast cs \<sqsubseteq> ub"
  by (metis assms below_ubundle_def minimal part_below ubleast_ubgetch ubdom_insert ubgetch_insert ubleast_ubdom)

lemma ubleast_empty [simp]: "ubLeast {} = Abs_ubundle Map.empty"
proof -
  have "optionLeast {} = (Map.empty::channel \<Rightarrow> 'a option)"
    by (meson dom_eq_empty_conv optionleast_dom)
  then show ?thesis
    by (simp add: ubleast_optionLeast_eq)
qed

(* if ubLeast {} is in an chain, all elements are equal *)
lemma ubundle_allempty: assumes "chain Y" and "ubLeast {} \<in> range Y"
  shows "\<And>i. (Y i) = ubLeast {}"
  by (metis (no_types, lifting) Abs_cfun_inverse2 Rep_ubundle_inverse assms(1) assms(2) empty_iff f_inv_into_f 
        part_eq ubdom_chain_eq2 ubDom_def ubdom_cont ubleast_ubdom)      

(* if an empty channel set is the first argument, then ubRestrict return the ubLeast with empty channel set  *)
lemma ubrestrict_ubleast [simp]: "ubRestrict {}\<cdot>ub = ubLeast {}"
  by (metis Rep_ubundle_inverse empty_iff empty_subsetI optionleast_dom part_eq subset_antisym ubleast_optionLeast_eq ubdom_insert ubrestrict_ubdom)

(* if the first argument disjoint with the domain of the bundle then the function return ubLeast with an empty channel set *)
lemma ubrestrict_ubleast2[simp]: assumes "cs \<inter> ubDom\<cdot>ub = {}" 
  shows "ubRestrict cs\<cdot>ub = ubLeast {}"
  by (metis Int_commute Int_empty_right assms dom_restrict ex_in_conv part_eq ubdom_insert ubrestrict_insert ubrestrict_ubleast)

lemma ubrestrict_below [simp]: assumes "chain Y" and "cont h"
  shows "(h (\<Squnion>i. Y i) \<bar> g (ubDom\<cdot>(\<Squnion>i. Y i))) \<sqsubseteq> (\<Squnion>i. (h (Y i)) \<bar> g (ubDom\<cdot>(Y i)))"
  proof -
    obtain nn :: "(nat \<Rightarrow> 'b\<^sup>\<Omega>) \<Rightarrow> (nat \<Rightarrow> 'b\<^sup>\<Omega>) \<Rightarrow> nat" where
      f1: "\<forall>f fa. f (nn fa f) \<noteq> fa (nn fa f) \<or> Lub f = Lub fa"
      by (meson lub_eq)
    have f2: "\<forall>f c. \<not> chain f \<or> (c\<cdot>(Lub f::'b\<^sup>\<Omega>)::'b\<^sup>\<Omega>) = (\<Squnion>n. c\<cdot>(f n))"
      using contlub_cfun_arg by blast
  have f3: "chain (\<lambda>n. h (Y n))"
    using assms(1) assms(2) ch2ch_cont by blast
  have f4: "h (Lub Y) = (\<Squnion>n. h (Y n))"
    using assms(1) assms(2) cont2contlubE by blast
  have "h (Y (nn (\<lambda>n. h (Y n) \<bar> g (UBundle.ubDom\<cdot>(Y n))) (\<lambda>n. h (Y n) \<bar> g (UBundle.ubDom\<cdot>(Lub Y))))) \<bar> g (UBundle.ubDom\<cdot>(Lub Y)) = h (Y (nn (\<lambda>n. h (Y n) \<bar> g (UBundle.ubDom\<cdot>(Y n))) (\<lambda>n. h (Y n) \<bar> g (UBundle.ubDom\<cdot>(Lub Y))))) \<bar> g (UBundle.ubDom\<cdot> (Y (nn (\<lambda>n. h (Y n) \<bar> g (UBundle.ubDom\<cdot>(Y n))) (\<lambda>n. h (Y n) \<bar> g (UBundle.ubDom\<cdot>(Lub Y))))))"
    by (simp add: assms(1))
  then have "(\<Squnion>n. h (Y n) \<bar> g (UBundle.ubDom\<cdot>(Lub Y))) = (\<Squnion>n. h (Y n) \<bar> g (UBundle.ubDom\<cdot>(Y n)))"
    using f1 by meson
  then have "h (Lub Y) \<bar> g (UBundle.ubDom\<cdot>(Lub Y)) = (\<Squnion>n. h (Y n) \<bar> g (UBundle.ubDom\<cdot>(Y n)))"
    using f4 f3 f2 by presburger
  then show ?thesis
    using not_below2not_eq by blast
qed

lemma ubunion_idR [simp]: "b \<uplus> (ubLeast {}) = b"
  by (simp add: ubunion_insert ubLeast_def ubWell_empty)    
    
    
subsection \<open>ubUp\<close>

    
(* the function returns a ubundle  *)
lemma ubup_well[simp]: "ubWell ((\<lambda> c. if c \<in> ubDom\<cdot>b then (Rep_ubundle b)c else Some \<bottom>) :: channel \<Rightarrow> 'a option)"
  apply(simp add: ubWell_def)
  by(simp add: usOkay_bot)

(* helper for the cont proof *)
lemma ubup_cont_h[simp]: "cont (\<lambda>b. (\<lambda> c. if c \<in> ubDom\<cdot>b then (Rep_ubundle b)c else Some \<bottom>))"
  by (smt contI2 below_ubundle_def eq_imp_below fun_below_iff is_ub_thelub lub_eq lub_fun monofunI
          po_class.chainE po_class.chainI ubrep_lub ubdom_below ubgetchE)

(* cont proof of ubUp *)
lemma ubup_cont[simp]: "cont (\<lambda>b. Abs_ubundle ((\<lambda> c. if (c\<in>ubDom\<cdot>b) then (Rep_ubundle b)c else Some \<bottom>) :: channel \<Rightarrow> 'a option))"
  by (simp add: cont_Abs_ubundle)

(* insert rule of ubUp *)
lemma ubup_insert: "ubUp\<cdot>b = Abs_ubundle (\<lambda>c. if (c\<in>ubDom\<cdot>b) then (Rep_ubundle b) c else Some \<bottom>)"
  by(simp add: ubUp_def)

(* the dom after applying ubUp is the same as UNIV *)
lemma ubup_ubdom [simp]: "ubDom\<cdot>(ubUp\<cdot>b) = UNIV"
  apply(simp add: ubdom_insert)
  apply(simp add: ubup_insert)
  by (smt CollectD Collect_cong UNIV_def dom_def optionLeast_def optionleast_dom ubdom_insert)

(* ubUp doesnt effect existing channel in a bundle *)
lemma ubup_ubgetch[simp]: assumes "c \<in> ubDom\<cdot>b"
  shows "(ubUp\<cdot>b) . c = b .c"
  by (simp add: assms ubup_insert ubgetch_insert)

(* ubUp changes the channel not in a bundle into \<bottom>  *)
lemma ubup_ubgetch2[simp]: assumes "c\<notin>ubDom\<cdot>b"
  shows "(ubUp\<cdot>b) . c = \<bottom>"
  by (simp add: assms ubup_insert ubgetch_ubrep_eq)

(* ubUp changes all the channel of ubLeast into \<bottom>  *)
lemma [simp]: "ubUp\<cdot>(ubLeast cs) . c = \<bottom>"
  using ubup_ubgetch2 by force

lemma ubup_restrict_id [simp]: assumes "c \<in> ubDom\<cdot>b2"
  shows "(Abs_ubundle (\<lambda> c. Some ((ubUp\<cdot>b2) . c)) \<bar> ubDom\<cdot>b2) . c = b2 . c"
  by (metis (no_types, lifting)
      UNIV_I assms option.sel restrict_in ubWell_def ubdom_channel_usokay ubgetch_insert ubrep_ubabs
      ubrestrict_insert ubrestrict_well ubup_ubdom ubup_ubgetch)

lemma ub_exists[simp]: "(ubLeast cs) \<in> (UB cs)"
  by (simp add: UB_def)

lemma ub_empty: "UB {} = {ubLeast {}}"
  apply (simp add: UB_def ubdom_insert ubLeast_def)
  apply rule
  apply (metis (mono_tags, lifting)
         CollectD Rep_ubundle_inject singleton_iff subsetI ubWell_empty ubrep_ubabs)
  by (simp add: ubWell_empty)

(****************************************************)
section\<open>Instantiation\<close>
(****************************************************) 


instantiation ubundle :: (uscl_pcpo) ubcl_comp
begin
definition ubLeast_ubundle_def: "UnivClasses.ubLeast \<equiv> ubLeast"

definition ubUnion_ubundle_def: "UnivClasses.ubUnion \<equiv> ubUnion"

definition ubRestrict_ubundle_def: "UnivClasses.ubRestrict \<equiv> ubRestrict"

instance
  apply intro_classes
          apply (simp add: ubDom_ubundle_def ubUnion_ubundle_def)
         apply (simp add: ubRestrict_ubundle_def ubUnion_ubundle_def ubunion_ubrestrict3)
        apply (simp add: ubDom_ubundle_def ubRestrict_ubundle_def)
       apply (simp add: UBundle_Pcpo.ubUnion_ubundle_def ubDom_ubundle_def ubRestrict_ubundle_def)
      apply (simp add: UBundle_Pcpo.ubRestrict_ubundle_def UBundle_Pcpo.ubUnion_ubundle_def ubDom_ubundle_def)
     apply (simp add: ubDom_ubundle_def ubRestrict_ubundle_def)
    apply (simp add: ubRestrict_ubundle_def)
   apply (simp add: ubDom_ubundle_def ubLeast_ubundle_def)
  apply (simp add: ubDom_ubundle_def ubLeast_ubundle_def)
   apply (simp add: UBundle_Pcpo.ubUnion_ubundle_def ubunion_associative)
  by (metis ubDom_ubundle_def ubUnion_ubundle_def ubunion_commutative)
end


end