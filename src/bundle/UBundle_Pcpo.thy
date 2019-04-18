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
lift_definition ubLeast :: "channel set \<Rightarrow> 'M\<^sup>\<Omega>" is
"(\<lambda> cs c. (c \<in> cs) \<leadsto> \<bottom> )"  
  apply(rule ubwellI)
  by (simp add: usclOkay_bot)

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
  by(simp add: usclOkay_bot)

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

lemma ubunion_idR [simp]: "ubUnion\<cdot>b\<cdot>(ubLeast {}) = b"
  by (simp add: ubunion_insert ubLeast_def ubWell_empty)    
    
lemma ubrestrict_ubleast_inter: "ubLeast cs1 \<bar> cs2 = ubLeast (cs1 \<inter> cs2)"
proof -
  have f1: "\<forall>u ua. (ubDom\<cdot>u \<noteq> ubDom\<cdot>ua \<or> (\<exists>c. c \<in> ubDom\<cdot>u \<and> (u . c::'a) \<noteq> ua . c)) \<or> u = ua"
by (meson ubgetchI)
obtain cc :: "'a\<^sup>\<Omega> \<Rightarrow> 'a\<^sup>\<Omega> \<Rightarrow> channel" where
  "\<forall>x0 x1. (\<exists>v2. v2 \<in> ubDom\<cdot>x1 \<and> x1 . v2 \<noteq> x0 . v2) = (cc x0 x1 \<in> ubDom\<cdot>x1 \<and> x1 . cc x0 x1 \<noteq> x0 . cc x0 x1)"
  by moura
  then have f2: "\<forall>u ua. ubDom\<cdot>u \<noteq> ubDom\<cdot>ua \<or> cc ua u \<in> ubDom\<cdot>u \<and> u . cc ua u \<noteq> ua . cc ua u \<or> u = ua"
    using f1 by presburger
have f3: "ubDom\<cdot>((ubLeast cs1::'a\<^sup>\<Omega>) \<bar> cs2) = ubDom\<cdot>(ubLeast (cs1 \<inter> cs2)::'a\<^sup>\<Omega>)"
  by auto
  have f4: "\<forall>c. c \<notin> cs1 \<inter> cs2 \<or> c \<in> cs2"
    by blast
  have f5: "\<forall>c. c \<notin> cs1 \<inter> cs2 \<or> c \<in> cs1"
    by (meson inf_sup_ord(1) subset_eq)
  { assume "((ubLeast cs1 \<bar> cs2) . cc (ubLeast (cs1 \<inter> cs2)) (ubLeast cs1 \<bar> cs2)::'a) \<noteq> ubLeast (cs1 \<inter> cs2) . cc (ubLeast (cs1 \<inter> cs2)) (ubLeast cs1 \<bar> cs2)"
    then have ?thesis
      using f5 f4 f3 f2 by (metis (no_types) ubgetch_ubrestrict ubleast_ubdom ubleast_ubgetch) }
  then show ?thesis
    using f3 f2 by blast
qed

subsection \<open>ubUp\<close>

    
(* the function returns a ubundle  *)
lemma ubup_well[simp]: "ubWell ((\<lambda> c. if c \<in> ubDom\<cdot>b then (Rep_ubundle b)c else Some \<bottom>) :: channel \<Rightarrow> 'a option)"
  apply(simp add: ubWell_def)
  by(simp add: usclOkay_bot)

(* helper for the cont proof *)
lemma ubup_cont_h[simp]: "cont (\<lambda>b. (\<lambda> c. if c \<in> ubDom\<cdot>b then (Rep_ubundle b)c else Some \<bottom>))"
proof  (rule contI2)
  show mono_proof: "monofun (\<lambda>(b::'a\<^sup>\<Omega>) c::channel. if c \<in> UBundle.ubDom\<cdot>b then Rep_ubundle b c else Some \<bottom>)"
  proof (rule monofunI)
    fix x::"'a\<^sup>\<Omega>" and y::"'a\<^sup>\<Omega>"
    assume x_le_y: "x \<sqsubseteq> y"
    show "(\<lambda>c::channel. if c \<in> UBundle.ubDom\<cdot>x then Rep_ubundle x c else Some \<bottom>) \<sqsubseteq> (\<lambda>c::channel. if c \<in> UBundle.ubDom\<cdot>y then Rep_ubundle y c else Some \<bottom>)"
      apply (simp add: fun_below_iff)
      by (metis below_ubundle_def fun_belowD ubdom_below x_le_y)
  qed
  show "\<forall>Y::nat \<Rightarrow> 'a\<^sup>\<Omega>.
       chain Y \<longrightarrow>
       (\<lambda>c::channel. if c \<in> UBundle.ubDom\<cdot>(\<Squnion>i::nat. Y i) then Rep_ubundle (\<Squnion>i::nat. Y i) c else Some \<bottom>) \<sqsubseteq> (\<Squnion>i::nat. (\<lambda>c::channel. if c \<in> UBundle.ubDom\<cdot>(Y i) then Rep_ubundle (Y i) c else Some \<bottom>))"
  proof auto
    fix Y::"nat \<Rightarrow> 'a\<^sup>\<Omega>"
    assume chain_Y: "chain Y"
    have f1: "\<And> i. ubDom\<cdot>(\<Squnion>i. Y i)  = ubDom\<cdot>(Y i)"
      by (simp add: chain_Y)
    have f2: "chain (\<lambda> i. (\<lambda>c::channel. if c \<in> UBundle.ubDom\<cdot>(\<Squnion>j::nat. Y j) then Rep_ubundle (Y i) c else Some \<bottom>))"
      apply (rule chainI)
      apply (simp add: fun_below_iff)
      by (meson below_ubundle_def chain_Y fun_below_iff po_class.chain_def)
    show "(\<lambda>c::channel. if c \<in> UBundle.ubDom\<cdot>(\<Squnion>i::nat. Y i) then Rep_ubundle (\<Squnion>i::nat. Y i) c else Some \<bottom>) \<sqsubseteq>
       (\<Squnion>i::nat. (\<lambda>c::channel. if c \<in> UBundle.ubDom\<cdot>(\<Squnion>j::nat. Y j) then Rep_ubundle (Y i) c else Some \<bottom>))"
    proof (simp add: fun_below_iff, auto)
      show "\<And>x::channel. x \<in> UBundle.ubDom\<cdot>(Lub Y) \<Longrightarrow> Rep_ubundle (Lub Y) x \<sqsubseteq> (\<Squnion>i::nat. (\<lambda>c::channel. if c \<in> UBundle.ubDom\<cdot>(Lub Y) then Rep_ubundle (Y i) c else Some \<bottom>)) x"
      proof -
        fix x:: channel
        assume x_in_dom:"x \<in> UBundle.ubDom\<cdot>(Lub Y)"
        have f11: "(\<Squnion>i::nat. (\<lambda>c::channel. if c \<in> UBundle.ubDom\<cdot>(Lub Y) then Rep_ubundle (Y i) c else Some \<bottom>)) x = 
              (\<Squnion>i::nat. (\<lambda>c::channel. if c \<in> UBundle.ubDom\<cdot>(Lub Y) then Rep_ubundle (Y i) c else Some \<bottom>) x)"
          using f2 lub_fun by fastforce
        show "Rep_ubundle (Lub Y) x \<sqsubseteq> (\<Squnion>i::nat. (\<lambda>c::channel. if c \<in> UBundle.ubDom\<cdot>(Lub Y) then Rep_ubundle (Y i) c else Some \<bottom>)) x"
          apply (subst f11, auto)
           apply (simp add: x_in_dom)
          by (metis (mono_tags) below_refl ch2ch_cont chain_Y cont2contlubE lub_fun ubrep_cont)
      qed
    next
      show "\<And>x::channel. x \<notin> UBundle.ubDom\<cdot>(Lub Y) \<Longrightarrow> (Some \<bottom>) \<sqsubseteq> (\<Squnion>i::nat. (\<lambda>c::channel. if c \<in> UBundle.ubDom\<cdot>(Lub Y) then Rep_ubundle (Y i) c else Some \<bottom>)) x"
        by (simp add: f2 lub_fun)
    qed
  qed
qed

(* cont proof of ubUp *)
lemma ubup_cont[simp]: "cont (\<lambda>b. Abs_ubundle ((\<lambda> c. if (c\<in>ubDom\<cdot>b) then (Rep_ubundle b)c else Some \<bottom>) :: channel \<Rightarrow> 'a option))"
  by (simp add: cont_Abs_ubundle)

(* insert rule of ubUp *)
lemma ubup_insert: "ubUp\<cdot>b = Abs_ubundle (\<lambda>c. if (c\<in>ubDom\<cdot>b) then (Rep_ubundle b) c else Some \<bottom>)"
  by(simp add: ubUp_def)

(* the dom after applying ubUp is the same as UNIV *)
lemma ubup_ubdom [simp]: "ubDom\<cdot>(ubUp\<cdot>b) = UNIV"
  apply auto
  apply(simp add: ubdom_insert)
  apply(simp add: ubup_insert)
  apply (simp add: dom_def)
  by (metis ubgetchE)

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

lemma ubup_restrict_id2 [simp]: "ubUp\<cdot>(ub) \<bar> ubDom\<cdot>ub = ub"
  by (metis (no_types, lifting) inf_commute inf_top.right_neutral ubgetchI ubgetch_ubrestrict 
    ubrestrict_ubdom2 ubup_ubdom ubup_ubgetch)

(****************************************************)
section\<open>Instantiation\<close>
(****************************************************) 

lemma ubunion_ubrestrict_minus: assumes "cs2 \<subseteq> ubclDom\<cdot>f2"
  shows "ubUnion\<cdot>(ubRestrict (cs1 - cs2)\<cdot>f1)\<cdot>f2 = ubUnion\<cdot>(ubRestrict cs1\<cdot>f1)\<cdot>f2"
  apply (rule ub_eq)
   apply simp
   apply (smt Int_Diff Un_Diff_cancel2 sup.absorb_iff1 sup_left_commute ubclDom_ubundle_def assms)
  by (metis Int_iff UnE diff_eq ubgetch_ubrestrict ubrestrict_ubdom2 ubunionDom ubunion_getchL ubunion_getchR)

lemma ubclunion_ubclrestrict_minus_id: "ubUnion\<cdot>(ubRestrict (cs1 - cs2)\<cdot>ub)\<cdot>(ubRestrict (cs1 \<inter> cs2)\<cdot>ub) = ubRestrict cs1\<cdot>ub"
  apply (rule ub_eq)
  by auto

lemma ubunion_ubrestrict_id: assumes "ubDom\<cdot>ub = cs1 \<union> cs2" and "cs1 \<inter> cs2 = {}" 
  shows "ubUnion\<cdot>(ubRestrict cs1\<cdot>ub)\<cdot>(ubRestrict cs2\<cdot>ub) = ub"
  apply (rule ub_eq)
  using assms(1) apply auto
  by (metis Int_commute Int_iff ubgetch_ubrestrict ubrestrict_ubdom2 ubunion_getchL ubunion_getchR)

instantiation ubundle :: (uscl_pcpo) ubcl_comp
begin
definition ubclLeast_ubundle_def[simp]: "ubclLeast \<equiv> ubLeast"

definition ubclUnion_ubundle_def[simp]: "ubclUnion \<equiv> ubUnion"

definition ubclRestrict_ubundle_def[simp]: "ubclRestrict \<equiv> ubRestrict"

instance
  apply intro_classes
  apply (simp_all)
  apply (simp add: ubunion_ubrestrict3)
  apply (simp add: ubunion_ubrestrict_minus)
  apply (simp add: UBundle_Pcpo.ubclunion_ubclrestrict_minus_id)   
  apply (simp add: ubunion_associative)
  by (metis ubunion_commutative)
end


end