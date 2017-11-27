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

  
(* ubLeast *)
subsection \<open>ubLeast\<close>

(* the optionLeast of the optionCpo is well-formed  *)
lemma ubleast_well: "ubWell (optionLeast cs)"
  sorry

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

(* if ubLeast {} is in an chain, all elements are equal *)
lemma ubundle_allempty: assumes "chain Y" and "ubLeast {} \<in> range Y"
  shows "\<And>i. (Y i) = ubLeast {}"
  by (metis (no_types, lifting) Abs_cfun_inverse2 Rep_ubundle_inverse assms(1) assms(2) empty_iff f_inv_into_f 
        part_eq ubdom_chain_eq2 ubDom_def ubdom_cont ubleast_ubdom)
      
      
      
(* Restrict *)      

(* if an empty channel set is the first argument, then ubRestrict return the ubLeast with empty channel set  *)
lemma ubrestrict_ubleast [simp]: "ubRestrict {}\<cdot>ub = ubLeast {}"
  by (metis Rep_ubundle_inverse empty_iff empty_subsetI optionleast_dom part_eq subset_antisym ubleast_optionLeast_eq ubdom_insert ubrestrict_ubdom)

(* if the first argument disjoint with the domain of the bundle then the function return ubLeast with an empty channel set *)
lemma ubrestrict_ubleast2[simp]: assumes "cs \<inter> ubDom\<cdot>ub = {}" 
  shows "ubRestrict cs\<cdot>ub = ubLeast {}"
  by (metis Int_commute Int_empty_right assms dom_restrict ex_in_conv part_eq ubdom_insert ubrestrict_insert ubrestrict_ubleast)
 
    
  subsection \<open>ubUp\<close>
(* ubUp *)
    
  thm ubUp_def
    
(* the function returns a ubundle  *)
lemma ubup_well[simp]: "ubWell (\<lambda> c. if c \<in> ubDom\<cdot>b then (Rep_ubundle b)c else Some \<bottom>)"
  by (smt domIff optionLeast_def ubWell_def ubdom_channel_usokay ubleast_well)

(* helper for the cont proof *)
lemma ubup_cont_h[simp]: "cont (\<lambda>b. (\<lambda> c. if c \<in> ubDom\<cdot>b then (Rep_ubundle b)c else Some \<bottom>))"
  by (smt contI2 below_ubundle_def eq_imp_below fun_below_iff is_ub_thelub lub_eq lub_fun monofunI
          po_class.chainE po_class.chainI ubrep_lub ubdom_below ubgetchE)

(* cont proof of ubUp *)
lemma ubup_cont[simp]: "cont (\<lambda>b. Abs_ubundle (\<lambda> c. if (c\<in>ubDom\<cdot>b) then (Rep_ubundle b)c else Some \<bottom>))"
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
    
    
    
    
    
end    