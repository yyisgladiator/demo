theory outFlashData

imports bundle.SB
begin

typedef outFlash="{cout,cin2}"
  by auto


instantiation outFlash::"{somechan,finite}"
begin
definition "Rep = Rep_outFlash"
instance
  apply(standard)
  apply(auto simp add: Rep_outFlash_def cEmpty_def)
  apply(auto simp add: ctype_empty_gdw)
  using ctype_empty_gdw
  apply (metis Rep_outFlash cMsg.simps ex_in_conv insertE insert_iff)
  apply (meson Rep_outFlash_inject injI) using cMsg.elims Rep_outFlash apply simp
  apply (metis cMsg.simps emptyE image_iff iso_tuple_UNIV_I)
  using type_definition.Abs_image type_definition_outFlash typedef_finite_UNIV by fastforce
end

definition "Flashout \<equiv> Abs_outFlash cout"
definition "Flashcin2 \<equiv> Abs_outFlash cin2"

free_constructors outFlash for "Flashout" | Flashcin2
  unfolding Flashout_def Flashcin2_def
  apply (metis Rep_outFlash Rep_outFlash_inverse empty_iff insert_iff)
  by (simp add: Abs_outFlash_inject)

lemma Flashout1_rep [simp]: "Rep (Flashout) = cout"
  by (simp add: Abs_outFlash_inverse Flashout_def Rep_outFlash_def)

lemma Flashcin2_rep [simp]: "Rep (Flashcin2) = cin2"
  by (simp add: Abs_outFlash_inverse Flashcin2_def Rep_outFlash_def)


fun outFlashChan::"('nat::type \<Rightarrow> 'a::type) \<Rightarrow> ('bool::type \<Rightarrow> 'a) \<Rightarrow>('nat\<times>'bool) \<Rightarrow> outFlash \<Rightarrow> 'a" where
"outFlashChan Cc1 Cc2 (port_c1, port_c2) Flashout = Cc1 port_c1" |
"outFlashChan Cc1 Cc2 (port_c1, port_c2) Flashcin2 = Cc2 port_c2"

abbreviation "buildFlashoutSBE \<equiv> outFlashChan (Tsyn o (map_option) \<B>) (Tsyn o (map_option) \<B>)" 

lemma buildflashout_ctype: "buildFlashoutSBE a c \<in> ctype (Rep c)"
  apply(cases c; cases a,simp)
   apply(simp_all add: ctype_def)
  
  using inj_def apply auto[1]
  using inj_def by auto[1]

lemma buildflashout_inj: "inj buildFlashoutSBE"
   apply (auto simp add: inj_def)
  by (metis outFlashChan.simps inj_def inj_B inj_tsyncons)+

lemma buildflashout_range: "range (\<lambda>a. buildFlashoutSBE a c) = ctype (Rep c)"
    apply(cases c)
  apply(auto simp add: image_iff ctype_def)
  by (metis option.simps(9))+

lemma buildflashout_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildFlashoutSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildFlashoutSBE a c)"
    using buildflashout_range by auto
  hence "\<exists>prod. sbe = buildFlashoutSBE prod"
    apply(subst fun_eq_iff,auto)
    apply(simp add: fun_eq_iff f_inv_into_f image_iff)
    using  outFlash.exhaust

    by (smt outFlashChan.simps(1) outFlashChan.simps(2)) 
  thus ?thesis
    by auto
qed

abbreviation "buildFlashoutSB \<equiv> outFlashChan (Rep_cfun (smap (Tsyn o (map_option) \<B>))) (Rep_cfun (smap (Tsyn o (map_option) \<B>)))" 


lemma buildflashoutsb_ctype: "sValues\<cdot>(buildFlashoutSB a c) \<subseteq> ctype (Rep c)"
  apply(cases c)
   apply auto
 
proof -
  fix x :: M
  assume a1: "x \<in> sValues\<cdot>(buildFlashoutSB a Flashout)"
  have f2: "\<forall>z. (Tsyn \<circ> map_option \<B>) z \<in> ctype cout"
    
    by (metis Flashout1_rep buildflashout_ctype outFlashChan.simps(1))
    obtain ss :: "bool option stream \<times> bool option stream \<Rightarrow> bool option stream" where
    "x \<in> (Tsyn \<circ> map_option \<B>) ` sValues\<cdot>(ss a)"
     using a1 by (metis outFlashChan.simps(1) old.prod.exhaust smap_sValues)
     then show "x \<in> ctype cout"
    using f2 by fastforce
next
  fix x :: M
  assume a1: "x \<in> sValues\<cdot>(buildFlashoutSB a Flashcin2)"
  have f2: "\<forall>z. (Tsyn \<circ> map_option \<B>) z \<in> ctype cin2"
    by (metis (full_types) Flashcin2_rep buildflashout_ctype outFlashChan.simps(2))
  obtain ss :: "bool option stream \<times> bool option stream \<Rightarrow> bool option stream" where
    "x \<in> (Tsyn \<circ> map_option \<B>) ` sValues\<cdot>(ss a)"
    using a1 by (metis outFlashChan.simps(2) old.prod.exhaust smap_sValues)
  then show "x \<in> ctype cin2"
    using f2 by fastforce
qed
  
 
lemma rep_cfun_smap_bool_inj:"inj   (Rep_cfun (smap (Tsyn o (map_option) \<B>)))"
  apply(rule smap_inj)
 
  by simp
lemma buildflashoutsb_inj: "inj buildFlashoutSB"
  apply (auto simp add: inj_def)

  apply (metis inj_eq outFlashChan.simps(1) rep_cfun_smap_bool_inj)
 
  by (metis inj_eq outFlashChan.simps(2) rep_cfun_smap_bool_inj)

lemma buildflashoutsb_range: "(\<Union>a. sValues\<cdot>(buildFlashoutSB a c)) = ctype (Rep c)"
  apply(cases c)
  apply auto
  apply (metis (no_types, lifting) Flashout1_rep buildflashoutsb_ctype contra_subsetD outFlashChan.simps)
  apply(rule_tac x="\<up>(inv (Tsyn \<circ> map_option \<B>)x)" in exI,auto)
  apply (smt Flashout1_rep buildflashout_range comp_apply f_inv_into_f outFlashChan.elims rangeI)
 
  apply (metis (no_types, hide_lams) Flashcin2_rep buildflashoutsb_ctype contra_subsetD outFlashChan.simps(2))
  apply(rule_tac x="\<up>(inv (Tsyn \<circ> map_option \<B>)x)" in exI,auto)
  using Flashcin2_rep buildflashout_range comp_apply f_inv_into_f outFlashChan.elims rangeI
  apply smt
  done
lemma smap_well:"sValues\<cdot>x\<subseteq>range f \<Longrightarrow>  \<exists>s. smap f\<cdot>s = x"
  apply(rule_tac x = "smap (inv f)\<cdot>x" in exI)
  by (simp add: snths_eq smap_snth_lemma f_inv_into_f snth2sValues subset_eq)
  
lemma buildflashoutsb_surj: assumes "sb_well sb"
  shows "sb \<in> range buildFlashoutSB"
proof -
  have ctypewell:"\<And> c. sValues\<cdot>(sb c) \<subseteq> ctype (Rep c)"
    using assms
    by (simp add: sb_well_def) 
  hence "\<exists>prod. sb = buildFlashoutSB prod"
    apply(subst fun_eq_iff,auto,simp add: sValues_def)
  proof -
    have f1: "\<forall>i M. sValues\<cdot>(sb i) \<subseteq> M \<or> \<not> ctype (Rep i) \<subseteq> M"
      by (metis ctypewell dual_order.trans)
    have f2: "ctype (Rep Flashout) \<subseteq> range(Tsyn o (map_option) \<B>)"
      
      apply(smt buildflashout_range f_inv_into_f outFlashChan.elims rangeI subsetI)
      done
 have  "ctype (Rep Flashcin2) \<subseteq> range(Tsyn o (map_option) \<B>)"
      
      apply(smt buildflashout_range f_inv_into_f outFlashChan.elims rangeI subsetI)
      done
    then  show "\<exists>s y. \<forall>i. sb i = buildFlashoutSB (s,y) i"
      using f1 f2 by (smt outFlash.exhaust outFlashChan.simps sValues_def smap_well)
  qed 
  thus ?thesis
    by auto
qed
end
