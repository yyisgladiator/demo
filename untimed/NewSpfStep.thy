(*  Title:        NewSpfStep
    Author:       Hendrik Kausch
    e-mail:       hendrik.kausch@rwth-aachen.de
*)

theory NewSpfStep
imports SPF
begin
default_sort type

typedef 'm sbElem = "{x :: (channel\<rightharpoonup>'m::message) . sbElemWell x}"
   by(simp add: sbElemWellEx)
  
definition sbHdElemWell::"'m::message SB \<Rightarrow> bool" where
"sbHdElemWell  \<equiv> \<lambda> sb. (\<forall>c \<in> ubDom\<cdot>(sb). sb. c \<noteq> \<epsilon>)"  

lemma sbHdElemWell_mono[simp]:"monofun (\<lambda> sb. (\<forall>c \<in> ubDom\<cdot>(sb). sb. c \<noteq> \<epsilon>))"
  apply(rule monofunI, simp add: less_bool_def)
  by (metis bottomI ubdom_below ubgetch_below)    

lemma sbHdElemWell_inv_ex:"sbHdElemWell sb \<Longrightarrow> \<exists>x. convDiscrUp x = (sbHdElem\<cdot>sb)"
  by (metis convdiscrup_inv_eq sbHdElem_channel sbHdElem_dom sbHdElemWell_def)

lemma sbHdElemWell_invConvDiscrUp:"sbHdElemWell sb \<Longrightarrow> \<forall>c\<in>ubDom\<cdot>(sb).((inv convDiscrUp) (sbHdElem\<cdot>sb)) \<rightharpoonup> c = inv Discr (inv Iup ((sbHdElem\<cdot>sb) \<rightharpoonup> c))"
  by (simp add: convDiscrUp_inv_subst sbHdElem_channel sbHdElemWell_def)
    
lemma sbHdElem_eq:"\<forall>c\<in>(ubDom\<cdot>sb1). sb1. c \<noteq>\<epsilon> \<Longrightarrow> sb1\<sqsubseteq>sb2 \<Longrightarrow> sbHdElem\<cdot>sb1 = sbHdElem\<cdot>sb2"
proof
  fix x::channel
  assume a1:"\<forall>c\<in>(ubDom\<cdot>sb1). sb1. c \<noteq>\<epsilon>"
  assume a2:"sb1\<sqsubseteq>sb2"
  have a3:"ubDom\<cdot>sb1 = ubDom\<cdot>sb2"
    using a2 ubdom_below by auto
  show "(sbHdElem\<cdot>sb1) x = (sbHdElem\<cdot>sb2) x"
    apply(simp add:sbHdElem_def sbHdElem_cont a3)
    using a1 a2 a3 lshd_eq ubgetch_below by blast
qed
 
(* updis bijectiv *)
thm inv_def
(* Returns the SPF that switches depending on input.  (spfStep_h1 In Out\<cdot>h)\<cdot>(sbHdElem\<cdot>sb) computes the SPF which has to be applied to the input sb*)
definition spfStep_inj :: "channel set \<Rightarrow> channel set \<Rightarrow> ('m::message sbElem \<Rightarrow> 'm SPF) \<rightarrow> 'm SB \<rightarrow>'m SPF" where
"spfStep_inj In Out \<equiv> (\<Lambda> h. (\<Lambda> sb. (if (sbHdElemWell sb \<and> ubDom\<cdot>sb = In) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)))"

(*inj_on*)

lemma spfStep_inj_mono_h[simp]:"monofun (\<lambda> sb. (if (sbHdElemWell sb) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out))"
proof(rule monofunI)
  fix x y::"'a stream\<^sup>\<Omega>"
  assume a1:"x \<sqsubseteq> y"
  show "(if sbHdElemWell x then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>x)))) else ufLeast In Out) \<sqsubseteq>
       (if sbHdElemWell y then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>y)))) else ufLeast In Out)"
  proof(cases "sbHdElemWell x")
    case True
    then have true_y:"sbHdElemWell y"
      by (metis a1 bottomI ubdom_below ubgetch_below sbHdElemWell_def)
    have a3:"sbHdElem\<cdot>x = sbHdElem\<cdot>y"
        apply(rule sbHdElem_eq)
        apply (meson True sbHdElemWell_def) 
        using True a1 by blast
    have "ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>x)))) \<sqsubseteq> ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>y))))"
        by (smt a1 a3 below_option_def po_eq_conv spfrt_step ufun_rel_eq)
    then show ?thesis
      by(simp add: True true_y)  
  next
    case False
    then show ?thesis
      by auto
  qed
qed

lemma discr_u_below_eq:assumes "(x::'a discr\<^sub>\<bottom>)\<sqsubseteq>y" and "x\<noteq>\<bottom>" shows "x = y"
  proof(insert assms(1), simp add: below_up_def assms)
    have "x \<noteq> Ibottom"
      using assms(2) inst_up_pcpo by auto
    then have "y \<noteq>Ibottom"
      by (metis assms(1) inst_up_pcpo bottomI)
    then show "case x of Ibottom \<Rightarrow> True | Iup a \<Rightarrow> case y of Ibottom \<Rightarrow> False | Iup x \<Rightarrow> a \<sqsubseteq> x \<Longrightarrow> x = y"
      by (metis assms(2) discrete_cpo inst_up_pcpo u.exhaust u.simps(5))
  qed

lemma sbhdelemwell_neg_adm_fin_h: assumes "chain Y" and "\<forall> i.  \<not> sbHdElemWell (Y i)"
  and "finite (ubDom\<cdot>(Lub Y))" shows "\<exists> c \<in>  (ubDom\<cdot>(Lub Y)). (\<forall> i. (Y i) . c = \<epsilon>)"
  apply (rule ccontr)
proof (simp)
  assume a1: "\<forall>c::channel\<in>ubDom\<cdot>(Lub Y). \<exists>i::nat. Y i  .  c \<noteq> \<epsilon> "
  have f1: "\<And> c::channel. c \<in>ubDom\<cdot>(Lub Y) \<longrightarrow> (\<exists>i::nat. Y i  .  c \<noteq> \<epsilon>)"
    by (simp add: a1)
  have f2: "\<And> c::channel. c \<in>ubDom\<cdot>(Lub Y) \<Longrightarrow> (\<exists>i::nat. Y i  .  c \<noteq> \<epsilon>)"
    by (simp add: a1)
  have f10 : "\<And>i. \<exists> c j. (Y i) . c = \<epsilon> \<and> (Y j) . c \<noteq> \<epsilon>"
    by (metis a1 assms(1) assms(2) sbHdElemWell_def ubdom_chain_eq2)
  have f11: "\<And> i j c.  (Y i . c = \<epsilon> \<and> Y j . c \<noteq> \<epsilon>) \<Longrightarrow> i \<le> j"
    by (metis assms(1) bottomI linear monofun_cfun_arg po_class.chain_mono)
  have f12: "\<exists> i. sbHdElemWell (Y i)"
    apply (rule ccontr)
    apply simp
  proof -
    assume a10: "\<forall>i::nat. \<not> sbHdElemWell (Y i)"
    have f110: "\<And> i::nat. \<not> sbHdElemWell (Y i)"
      by (simp add: a10)
    obtain i where i_def: "\<not> sbHdElemWell (Y i)"
      by (simp add: a10)
    obtain ch_not_eps where ch_not_eps_def: "ch_not_eps = {{i. Y i . ch \<noteq> \<epsilon>} | ch. ch \<in>  (ubDom\<cdot>(Lub Y))}"
      by blast
    obtain surj_f where surj_f_def: "surj_f = (\<lambda> ch. {i. Y i . ch \<noteq> \<epsilon>})"
      by simp
    have "ch_not_eps \<subseteq>  surj_f ` (ubDom\<cdot>(Lub Y))"
      using ch_not_eps_def surj_f_def by blast
    then have ch_not_epsfinite: "finite ch_not_eps"
      by (meson assms(3) finite_surj)
    have ch_not_eps_ele_not_emp: "\<forall> ele \<in> ch_not_eps. ele \<noteq> {}"
    proof rule
      fix ele
      assume a11: "ele \<in> ch_not_eps"
      obtain ch where ch_def: "ele = surj_f ch" and ch_def_2: "ch \<in> ubDom\<cdot>(Lub Y)"
        using a11 ch_not_eps_def surj_f_def by blast
      obtain j where j_def: "(Y j) . ch \<noteq> \<epsilon>"
        using a1 ch_def_2 by blast
      then show "ele \<noteq> {}"
        using ch_def surj_f_def by blast
    qed
    have dom_emty_iff:"(ch_not_eps={})  \<longleftrightarrow> (ubDom\<cdot>(Lub Y) = {})"
      using ch_not_eps_def by blast
    have dom_not_emp_false: "ch_not_eps\<noteq>{} \<Longrightarrow> False"
    proof -
      assume a111: "ch_not_eps\<noteq>{}"
      have "\<forall> ele. ele \<in> ch_not_eps \<longrightarrow> (\<exists> i. i \<in> ele \<and> (\<forall> j \<in> ele. i \<le> j))"
        apply (rule ccontr)
      proof (simp)
        assume a1111: "\<exists>ele::nat set. ele \<in>ch_not_eps \<and>  (\<forall>i::nat. i \<in> ele \<longrightarrow> (\<exists>x::nat\<in>ele. \<not> i \<le> x))"
        obtain ele where ele_def: "ele \<in> ch_not_eps \<and> (\<forall>i::nat. i \<in> ele \<longrightarrow> (\<exists>x::nat\<in>ele. \<not> i \<le> x))"
          using a1111 by blast
        obtain the_ch where the_ch_def: "ele = surj_f the_ch"
          using ch_not_eps_def ele_def surj_f_def by blast
        have ele_def2: "ele = {i. Y i . the_ch \<noteq> \<epsilon>}"
          using surj_f_def the_ch_def by blast
        obtain the_i where the_i_def: "the_i \<in> ele"
          using ch_not_eps_ele_not_emp ele_def by auto
        obtain the_subs where the_subst_def: "the_subs = {i. i \<le> the_i \<and> Y i . the_ch \<noteq> \<epsilon>}"
          by simp
        have the_subs_subs: "the_subs \<subseteq> ele"
          apply (simp add: the_subst_def ele_def2)
          apply rule
          by simp
        have the_min: "\<forall> i \<in> the_subs. Min the_subs \<le> i"
          by (simp add: the_subst_def)
        have the_min_in_subs: "Min the_subs \<in> the_subs"
          apply (rule Min_in)
          apply (simp add: the_subst_def)
          using ele_def2 the_i_def the_subst_def by blast
        then have the_min_in: "Min the_subs \<in> ele"
          using the_subs_subs by auto
        have the_min_min: "\<forall> i \<in> ele. Min the_subs \<le> i"
          apply rule
          apply (case_tac "i \<le> the_i")
          using ele_def2 the_min the_subst_def apply blast
          using the_min_in_subs the_subst_def by auto
        show False
          using ele_def the_min_in the_min_min by auto
      qed
      then have "\<And> ele. ele \<in> ch_not_eps \<Longrightarrow> (\<exists> i. i \<in> ele \<and> (\<forall> j \<in> ele. i \<le> j))"
        by blast
      then have "\<And> ele. ele \<in> ch_not_eps \<Longrightarrow> (\<exists>! i. i \<in> ele \<and> (\<forall> j \<in> ele. i \<le> j))"
        using le_antisym by blast
      obtain finite_ch_n_eps 
        where min_i_ch_def: "finite_ch_n_eps = {the_i | the_i ele. ele \<in> ch_not_eps \<and> (\<forall> i \<in> ele. the_i \<le> i) \<and> the_i \<in> ele}"
        by simp
      obtain bla::"nat set \<Rightarrow> nat set" where bla_def: "bla = (\<lambda> da_set. {the_i. (\<forall> i \<in> da_set. the_i \<le> i) \<and> the_i \<in> da_set})"
        by simp
      have "\<forall> da_set \<in> ch_not_eps. \<exists>! i \<in> da_set. bla da_set = {i}"
      proof rule
        fix da_set
        assume bla: "da_set \<in> ch_not_eps"
        obtain the_i where the_i_def: "the_i \<in> da_set" and the_i_def2: "(\<forall> j \<in> da_set. the_i \<le> j)"
          using \<open>\<And>ele::nat set. ele \<in> (ch_not_eps::nat set set) \<Longrightarrow> \<exists>i::nat. i \<in> ele \<and> (\<forall>j::nat\<in>ele. i \<le> j)\<close> bla by blast
        have "the_i \<in> bla da_set"
          using \<open>(bla::nat set \<Rightarrow> nat set) = (\<lambda>da_set::nat set. {the_i::nat. (\<forall>i::nat\<in>da_set. the_i \<le> i) \<and> the_i \<in> da_set})\<close> the_i_def the_i_def2 by blast
        have "\<forall> i \<in> bla da_set. i = the_i"
          by (simp add: \<open>(bla::nat set \<Rightarrow> nat set) = (\<lambda>da_set::nat set. {the_i::nat. (\<forall>i::nat\<in>da_set. the_i \<le> i) \<and> the_i \<in> da_set})\<close> eq_iff the_i_def the_i_def2)
        show "\<exists>!i::nat. i \<in> da_set \<and> bla da_set = {i}"
          apply (rule ex_ex1I)
           apply (rule_tac x ="the_i" in exI)
           apply rule
            apply (simp add: the_i_def)
           apply rule
            apply (simp add: \<open>\<forall>i::nat\<in>(bla::nat set \<Rightarrow> nat set) (da_set::nat set). i = (the_i::nat)\<close> subsetI)
           apply (simp add: \<open>(the_i::nat) \<in> (bla::nat set \<Rightarrow> nat set) (da_set::nat set)\<close>)
          by auto
      qed
      obtain min_set_set::"nat set" where min_set_set_def: "min_set_set = {THE i. i \<in> bla da_set | da_set. da_set \<in> ch_not_eps}"
        by simp
      have i_max_is_max: "\<forall> ch \<in> ubDom\<cdot>(Lub Y). \<exists> i . (i \<in> min_set_set) \<longrightarrow> Y i . ch \<noteq> \<epsilon>"
      proof  rule
        fix ch
        assume a1111: "ch \<in> ubDom\<cdot>(Lub Y)"
        obtain ch_set where ch_set_def: "ch_set = surj_f ch"
          by simp
        obtain the_set where the_st_def: "the_set = bla ch_set"
          by simp
        have ch_set_in_ch_not_eps: "ch_set \<in> ch_not_eps"
          apply (simp add: ch_not_eps_def)
          using a1111 ch_set_def surj_f_def by blast
        obtain the_min where the_min_def: "the_min \<in> ch_set \<and> (\<forall> j \<in> ch_set. the_min \<le> j)"
          using \<open>\<And>ele::nat set. ele \<in> (ch_not_eps::nat set set) \<Longrightarrow> \<exists>i::nat. i \<in> ele \<and> (\<forall>j::nat\<in>ele. i \<le> j)\<close> ch_set_in_ch_not_eps by auto

        have "bla ch_set = {the_min}"
          using bla_def the_min_def by force
        then have "the_min \<in> bla ch_set"
          by simp
        have "\<And> i. i \<in> bla ch_set \<Longrightarrow> i = the_min"
          using \<open>(bla::nat set \<Rightarrow> nat set) (ch_set::nat set) = {the_min::nat}\<close> by auto
        then have "(THE i::nat. i \<in> bla ch_set) = the_min"
          using \<open>(the_min::nat) \<in> (bla::nat set \<Rightarrow> nat set) (ch_set::nat set)\<close> by blast
        then have "the_min \<in> min_set_set"
          apply (simp add: min_set_set_def)
          apply (rule_tac x="ch_set" in exI)
          apply rule defer
           apply (simp add: ch_set_in_ch_not_eps)
          by simp
        then show " \<exists>i::nat. i \<in> min_set_set \<longrightarrow> Y i  .  ch \<noteq> \<epsilon>"
          apply (rule_tac x=the_min in exI)
          apply simp
          using ch_set_def mem_Collect_eq surj_f_def the_min_def by blast
      qed
      have "finite min_set_set"
        by (simp add: ch_not_epsfinite min_set_set_def)
      obtain the_max where the_max_def: "the_max = Max min_set_set"
        by simp
      have "the_max \<in> min_set_set"
        apply (subst the_max_def)
        apply (rule Max_in)
         apply (simp add: \<open>finite (min_set_set::nat set)\<close>)
        using a111 min_set_set_def by auto
      have "\<exists> i. sbHdElemWell (Y i)"
      proof (rule_tac x="the_max" in exI, simp add: sbHdElemWell_def, rule)
        fix c::channel
        assume a11111: "c \<in> ubDom\<cdot>(Y the_max)"
        obtain the_set where the_set_def: "the_set = surj_f c"
          by simp
        have "the_set \<in> ch_not_eps"
          using a11111 assms(1) ch_not_eps_def surj_f_def the_set_def by auto
        then obtain the_min where the_min_def: "the_min \<in> the_set \<and> (\<forall> j \<in> the_set. the_min \<le> j)"
          using \<open>\<forall>ele::nat set. ele \<in> (ch_not_eps::nat set set) \<longrightarrow> (\<exists>i::nat. i \<in> ele \<and> (\<forall>j::nat\<in>ele. i \<le> j))\<close> by blast
        have "bla the_set = {the_min}"
          using bla_def the_min_def by force
        then have "the_min \<in> bla the_set"
          by simp
        have "\<And> i. i \<in> bla the_set \<Longrightarrow> i = the_min"
          using \<open>(bla::nat set \<Rightarrow> nat set) (the_set::nat set) = {the_min::nat}\<close> by auto
        then have "(THE i::nat. i \<in> bla the_set) = the_min"
          using \<open>(the_min::nat) \<in> (bla::nat set \<Rightarrow> nat set) (the_set::nat set)\<close> by blast
        then have "the_min \<in> min_set_set"
          apply (simp add: min_set_set_def)
          apply (rule_tac x="the_set" in exI)
          apply rule defer
          apply (simp add: \<open>(the_set::nat set) \<in> (ch_not_eps::nat set set)\<close>)
          by simp
        then have "the_min \<le> the_max"
          by (simp add: \<open>finite (min_set_set::nat set)\<close> the_max_def)
        then have "Y the_min \<sqsubseteq> Y the_max"
          by (simp add: assms(1) po_class.chain_mono)
        have "Y the_min . c \<noteq> \<epsilon>"
          using surj_f_def the_min_def the_set_def by blast
        then show "Y the_max  .  c \<noteq> \<epsilon>"
          using \<open>(the_min::nat) \<le> (the_max::nat)\<close> f11 order_class.order.antisym by blast
      qed
      then show False
        by (simp add: a10)
    qed
    then show False
      apply (case_tac "ch_not_eps={}")
       apply (metis assms(1) dom_emty_iff empty_iff i_def sbHdElemWell_def ubdom_chain_eq2)
      by simp
  qed
  show False
    using assms(2) f12 by auto
qed


lemma sbhdelemwell_neg_adm_fin: assumes "chain Y" and "\<forall> i.  \<not> sbHdElemWell (Y i)"
  and "ubDom\<cdot>(Lub Y) = In" and "finite In" 
shows "\<not> sbHdElemWell (Lub Y)"
  apply (rule ccontr, simp)
proof -
  assume a1: "sbHdElemWell (Lub Y)"
  obtain c where c_def1: " (\<forall> i. (Y i) . c = \<epsilon>)" and c_def2: "c \<in> In"
    using assms(1) assms(2) assms(3) assms(4) sbhdelemwell_neg_adm_fin_h by blast
  obtain the_Y where the_Y_def: "the_Y = ubUnion\<cdot>(Lub Y)\<cdot>(Abs_ubundle([c \<mapsto> \<epsilon>]))"
    by simp
  have "\<And>i . Y i \<sqsubseteq> the_Y"
    apply (rule ub_below)
     apply (simp_all add: the_Y_def)
     apply (metis (mono_tags) a1 assms(1) assms(3) c_def1 c_def2 ch2ch_Rep_cfunR contlub_cfun_arg lub_eq_bottom_iff sbHdElemWell_def)
    apply (case_tac "ca = c")
     apply (simp add: c_def1)
    by (metis (mono_tags) a1 assms(1) assms(3) c_def1 c_def2 contlub_cfun_arg lub_eq_bottom_iff minimal po_class.chain_def sbHdElemWell_def)
  have "\<not> sbHdElemWell the_Y"
    by (metis (no_types, lifting) a1 assms(1) assms(3) c_def1 c_def2 ch2ch_Rep_cfunR contlub_cfun_arg lub_eq_bottom_iff sbHdElemWell_def)
  have "the_Y \<sqsubseteq> Lub Y"
    by (metis (no_types, lifting) a1 assms(1) assms(3) c_def1 c_def2 ch2ch_Rep_cfunR contlub_cfun_arg lub_eq_bottom_iff sbHdElemWell_def)
  show False
    by (metis (full_types) \<open>(the_Y::'a stream\<^sup>\<Omega>) \<sqsubseteq> Lub (Y::nat \<Rightarrow> 'a stream\<^sup>\<Omega>)\<close> \<open>\<And>i::nat. (Y::nat \<Rightarrow> 'a stream\<^sup>\<Omega>) i \<sqsubseteq> (the_Y::'a stream\<^sup>\<Omega>)\<close> \<open>\<not> sbHdElemWell (the_Y::'a stream\<^sup>\<Omega>)\<close> a1 assms(1) lub_below po_eq_conv)
qed

lemma sbhdelemwell_lub_n_exI:assumes "chain Y" and "ubDom\<cdot>(Y i) = In" and "finite In" and "sbHdElemWell (Lub Y)"
  shows "\<exists> i. sbHdElemWell (Y i)"
  using assms(1) assms(2) assms(3) assms(4) sbhdelemwell_neg_adm_fin by fastforce

lemma spfStep_inj_mono_h2[simp]:"monofun (\<lambda> sb. (if (sbHdElemWell sb \<and> ubDom\<cdot>sb = In) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out))"
proof(rule monofunI)
  fix x y::"'a stream\<^sup>\<Omega>"
  assume a1:"x \<sqsubseteq> y"
  show "(if sbHdElemWell x \<and> ubDom\<cdot>x = In then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>x)))) else ufLeast In Out) \<sqsubseteq>
       (if sbHdElemWell y \<and> ubDom\<cdot>y = In then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>y)))) else ufLeast In Out)"
  proof(cases "sbHdElemWell x \<and> ubDom\<cdot>x = In")
    case True
    then have true_y:"sbHdElemWell y"
      by (metis a1 bottomI ubdom_below ubgetch_below sbHdElemWell_def)
    have a3:"sbHdElem\<cdot>x = sbHdElem\<cdot>y"
        apply(rule sbHdElem_eq)
        apply (meson True sbHdElemWell_def) 
        using True a1 by blast
    have "ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>x)))) \<sqsubseteq> ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>y))))"
        by (smt a1 a3 below_option_def po_eq_conv spfrt_step ufun_rel_eq)
      then show ?thesis
        using a1 true_y ubdom_below by auto
  next
    case False
    then show ?thesis
      by auto
  qed
qed

lemma spfStep_inj_cont_h[simp]:assumes "finite In" 
  shows "cont (\<lambda> sb. (if (sbHdElemWell sb \<and> ubDom\<cdot>sb = In) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out))"(*Maybe In has to be finite for cont*)
proof(rule Cont.contI2, simp)
  fix Y::"nat \<Rightarrow> 'a stream\<^sup>\<Omega>"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i. if sbHdElemWell (Y i) \<and> ubDom\<cdot>(Y i) = In then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(Y i))))) else ufLeast In Out)"
  have dom:"ufDom\<cdot>(\<Squnion>i::nat. if sbHdElemWell (Y i) \<and> ubDom\<cdot>(Y i) = In then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(Y i))))) else ufLeast In Out) = In"
    by (smt a2 ufRestrict_dom ufdom_lub_eq ufleast_ufdom)
  have ran:"ufRan\<cdot>(\<Squnion>i::nat. if sbHdElemWell (Y i) \<and> ubDom\<cdot>(Y i) = In then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(Y i))))) else ufLeast In Out) = Out"
    by (smt a2 ufRestrict_ran ufleast_ufRan ufran_lub_eq)  
  have sbHdEq:"\<And>i. sbHdElemWell (Y i) \<Longrightarrow> (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(\<Squnion>i. Y i)))) = (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(Y i))))"
    by (metis a1 is_ub_thelub sbHdElemWell_def sbHdElem_eq)
  show "(if sbHdElemWell (\<Squnion>i::nat. Y i) \<and> ubDom\<cdot>(\<Squnion>i::nat. Y i) = In then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(\<Squnion>i. Y i))))) else ufLeast In Out) \<sqsubseteq>
       (\<Squnion>i. if sbHdElemWell (Y i) \<and> ubDom\<cdot>(Y i) = In then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(Y i))))) else ufLeast In Out)"
  proof(cases "sbHdElemWell (\<Squnion>i::nat. Y i) \<and> ubDom\<cdot>(\<Squnion>i::nat. Y i) = In")
    case True
    obtain n where n_def:"sbHdElemWell (Y n)"
      using True a1 assms sbhdelemwell_neg_adm_fin by auto
    then have h1:"(if sbHdElemWell (\<Squnion>i. Y i) \<and> ubDom\<cdot>(\<Squnion>i::nat. Y i) = In then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(\<Squnion>i. Y i))))) else ufLeast In Out) = (ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>( Y n))))))"
      by(subst sbHdEq[of n], simp_all add: True n_def)
    then have h2:"ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(Y n)))))\<sqsubseteq> (\<Squnion>i. (if sbHdElemWell (Y i) \<and> ubDom\<cdot>(Y i) = In then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(Y i))))) else ufLeast In Out))"
      by (smt a1 a2 below_lub n_def po_class.chain_def ubdom_chain_eq2)
    then show ?thesis
      by (simp add: h1)
  next
    case False
    then show ?thesis
      using dom ran by auto
  qed
qed
  
lemma spfStep_inj_mono[simp]:assumes "finite In" 
  shows "monofun (\<lambda> h. (\<Lambda> sb. (if (sbHdElemWell sb \<and> ubDom\<cdot>sb = In) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)))"
  apply (rule monofunI)
  apply (rule cfun_belowI)
  apply (simp add: assms)
  apply auto
  by (simp add: fun_belowD monofun_cfun_arg)
    

lemma spfStep_inj_cont[simp]: assumes "finite In"
  shows "cont (\<lambda> h. (\<Lambda> sb. (if (sbHdElemWell sb \<and> ubDom\<cdot>sb = In)
             then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)))"
proof (rule Cont.contI2, simp add: assms)
  fix Y::"nat \<Rightarrow> 'a sbElem \<Rightarrow> 'b ufun"
  assume a1: " chain Y"
  assume a2: "chain (\<lambda>i::nat. \<Lambda> (sb::'a stream\<^sup>\<Omega>).
                          if sbHdElemWell sb \<and> ubDom\<cdot>sb = In
                          then ufRestrict In Out\<cdot>(Y i (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)"
  have cont_lub: " \<And>x::'a stream\<^sup>\<Omega>.
       cont (\<lambda>x::'a stream\<^sup>\<Omega>.
                \<Squnion>i::nat.
                   if sbHdElemWell x \<and> ubDom\<cdot>x = In then ufRestrict In Out\<cdot>(Y i (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>x))))
                   else ufLeast In Out)"
    proof (rule cont2cont_lub, simp_all add: assms)
    fix xa :: "'a stream\<^sup>\<Omega>"
    have f1: "\<forall>n. Y n \<sqsubseteq> Y (Suc n)"
      by (meson a1 po_class.chain_def)
    obtain nn :: "(nat \<Rightarrow> 'b ufun) \<Rightarrow> nat" where
      f2: "\<forall>f. (\<not> chain f \<or> (\<forall>n. f n \<sqsubseteq> f (Suc n))) \<and> (chain f \<or> f (nn f) \<notsqsubseteq> f (Suc (nn f)))"
      using po_class.chain_def by moura
    have "(if sbHdElemWell xa \<and> ubDom\<cdot>xa = In then ufRestrict In Out\<cdot> (Y (nn (\<lambda>n. if sbHdElemWell xa \<and> ubDom\<cdot>xa = In then ufRestrict In Out\<cdot> (Y n (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>xa)))) else ufLeast In Out)) (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>xa)))) else ufLeast In Out) \<sqsubseteq> (if sbHdElemWell xa \<and> ubDom\<cdot>xa = In then ufRestrict In Out\<cdot> (Y (Suc (nn (\<lambda>n. if sbHdElemWell xa \<and> ubDom\<cdot>xa = In then ufRestrict In Out\<cdot> (Y n (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>xa)))) else ufLeast In Out))) (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>xa)))) else ufLeast In Out)"
      using f1 by (simp add: cont_pref_eq1I fun_belowD)
    then show "chain (\<lambda>n. if sbHdElemWell xa \<and> ubDom\<cdot>xa = In then ufRestrict In Out\<cdot> (Y n (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>xa)))) else ufLeast In Out)"
      using f2 by meson
  qed
  show "(\<Lambda> (sb::'a stream\<^sup>\<Omega>).
           if sbHdElemWell sb \<and> ubDom\<cdot>sb = In
           then ufRestrict In Out\<cdot>((\<Squnion>i::nat. Y i) (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out) \<sqsubseteq>
       (\<Squnion>i::nat.
           \<Lambda> (sb::'a stream\<^sup>\<Omega>).
              if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then ufRestrict In Out\<cdot>(Y i (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb))))
              else ufLeast In Out)"
  apply(subst lub_cfun, simp add: a2)
  apply(simp only: below_cfun_def below_fun_def)
  apply(subst beta_cfun, simp add: assms)
    apply(subst beta_cfun, simp add: assms)
    apply(subst beta_cfun)
    using cont_lub apply blast
    by (simp add: a1 ch2ch_fun cont2contlubE lub_fun)
qed

  
thm Rep_sbElem_inverse

(*
definition convSB :: "(channel \<rightharpoonup> 'm discr\<^sub>\<bottom>) \<Rightarrow> 'm stream ubundle" where
"convSB sb \<equiv> Abs_ubundle (\<lambda>c. (c \<in> dom sb) \<leadsto> (lscons\<cdot>(sb \<rightharpoonup> c)\<cdot>\<epsilon>))"
*)

lemma bla: assumes "sbElemWell (sb)" shows "ubWell (\<lambda>c. (c \<in> dom sb) \<leadsto> (lscons\<cdot>((convDiscrUp sb) \<rightharpoonup> c)\<cdot>\<epsilon>))"
  apply (rule ubwellI) 
  apply (simp add: domIff2)
  unfolding usclOkay_stream_def
proof - 
  fix c
  assume c_in_dom: "c \<in> dom sb"
  have f0: "sb\<rightharpoonup>c \<in> ctype c"
    by (simp add: assms c_in_dom sbElemWellI)
  have f1: "updis(sb\<rightharpoonup>c) && \<epsilon> = convDiscrUp sb\<rightharpoonup>c && \<epsilon>"
    by (simp add: c_in_dom convDiscrUp_def up_def)
  have f2: "updis(sb\<rightharpoonup>c) && \<epsilon> = \<up>(sb\<rightharpoonup>c)"
    by (simp add: sup'_def)
  have f3: "sdom\<cdot>(convDiscrUp sb\<rightharpoonup>c && \<epsilon>) = sdom\<cdot>(\<up>sb\<rightharpoonup>c)"
    using f1 f2 by auto
  have f4: "sdom\<cdot>(\<up>sb\<rightharpoonup>c) = {sb\<rightharpoonup>c}"
    by simp
  show "sdom\<cdot>(convDiscrUp sb\<rightharpoonup>c && \<epsilon>) \<subseteq> ctype c"
    by (simp add: f0 f3)
qed

lemma bla_dom: assumes "sbElemWell (sb)" shows "ubDom\<cdot>(convSB (convDiscrUp sb)) = dom sb"
  apply (simp add: convSB_def)
  apply (subst ubdom_ubrep_eq)
   apply (simp add: assms bla)
  by simp

lemma bla_apply: assumes "sbElemWell (sb)" and "c \<in> dom sb" 
  shows " (convSB (convDiscrUp sb)) . c = \<up>(sb \<rightharpoonup>c)"
  apply (simp add: convSB_def)
  apply (simp add: ubgetch_ubrep_eq assms bla)
  by (simp add: assms(2) convDiscrUp_def sup'_def up_def)

lemma sbElem_surj:
  shows "\<And> sbE. \<exists>sb. sbE =  Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)) 
                    \<and> sbHdElemWell sb \<and> ubDom\<cdot>sb = dom (Rep_sbElem sbE)"
proof -
  fix sbE ::"'a sbElem"
  obtain daFun where daFun_def: "daFun  = Rep_sbElem sbE"
    by (metis Rep_sbElem_inverse)
  have f0: "sbElemWell (Rep_sbElem sbE)"
    using Rep_sbElem by auto
  have f1: "sbElemWell daFun"
    by (simp add: daFun_def f0)
  have f2: "\<forall>c\<in> dom daFun. daFun\<rightharpoonup>c \<in> ctype c"
    using f1 sbElemWell_def by auto
  have f3: "dom daFun = dom (Rep_sbElem sbE)"
    by (simp add: daFun_def)
  obtain daBundle where daBundle_def: "daBundle = convSB (convDiscrUp daFun)"
    by simp
  have daDom_eq: "ubDom\<cdot>daBundle = dom daFun"
    apply (simp add: daBundle_def)
    by (simp add: f1 bla_dom)
  have daBundle_elem_wel: "sbHdElemWell daBundle"
    apply (simp add: sbHdElemWell_def)
  proof rule
    fix c::channel
    assume c_in_dom: "c \<in> ubDom\<cdot>daBundle"
    have c_in_dom_2: "c \<in> dom daFun"
      using c_in_dom daDom_eq by auto

    show "daBundle  .  c \<noteq> \<epsilon>"
      apply (simp add: daBundle_def)
      by (simp add: bla_apply f1 c_in_dom_2)
  qed    
  have f111: "sbHdElem\<cdot>daBundle = convDiscrUp daFun"
    apply (simp add: daBundle_def)
    apply (simp add: sbHdElem_cont sbHdElem_def)
    apply (rule part_eq)
    using daBundle_def daDom_eq apply auto[1]
    apply simp
    apply (subst add: daFun_def)
    apply (subst convSB_def)
    apply (subst ubgetch_ubrep_eq)
    apply (simp add: bla f1)
    apply simp
    using daBundle_def daDom_eq by auto
  show "\<exists>sb. sbE =  Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)) 
    \<and> sbHdElemWell sb \<and> ubDom\<cdot>sb = dom (Rep_sbElem sbE)"
    apply (rule_tac x="daBundle" in exI)
    apply rule defer
     apply (simp add: daBundle_elem_wel daDom_eq f3)
    apply (subst f111)
    by (simp add: Rep_sbElem_inverse convDiscrUp_inj daFun_def)
qed
    
lemma spfStep_inj_on[simp]:assumes "finite In" shows "inj_on (Rep_cfun (spfStep_inj In Out)) {h. \<forall>m. ufDom\<cdot>(h m) = In \<and> ufRan\<cdot>(h m) = Out}"
proof (simp add: spfStep_inj_def, rule inj_onI)
  fix x y :: "'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun"
  assume ax:" x \<in> {h. \<forall>m. ufDom\<cdot>(h m) = In \<and> ufRan\<cdot>(h m) = Out}"
  assume ay:" y \<in> {h. \<forall>m. ufDom\<cdot>(h m) = In \<and> ufRan\<cdot>(h m) = Out}"
  assume a1:"
       (\<Lambda> (h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) (sb::'a stream\<^sup>\<Omega>). if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)\<cdot>x =
       (\<Lambda> (h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) (sb::'a stream\<^sup>\<Omega>). if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)\<cdot>y"  
  have a2: "(\<Lambda> (h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) (sb::'a stream\<^sup>\<Omega>). if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)\<cdot>x =
            (\<Lambda> sb. if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then ufRestrict In Out\<cdot>(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)"
    by (simp add: assms)
  have a3: "(\<Lambda> (h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) (sb::'a stream\<^sup>\<Omega>). if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)\<cdot>y =
            (\<Lambda> sb. if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then ufRestrict In Out\<cdot>(y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)"
    by (simp add: assms)
  have a4: "(\<Lambda> sb. if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then ufRestrict In Out\<cdot>(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out) = 
            (\<Lambda> sb. if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then ufRestrict In Out\<cdot>(y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)"
    using a1 a2 a3 by auto
  show "x = y"
  proof(cases "x \<noteq> y")
    case True
    then obtain sbE where sbE_def:" x sbE \<noteq> y sbE"
      by fastforce
    have blabla: " dom (Rep_sbElem sbE) = In"
      sledgehammer
      sorry
    then obtain sb where sb_def:"((inv convDiscrUp (sbHdElem\<cdot>sb))) =  (Rep_sbElem sbE) \<and> sbHdElemWell sb \<and> ubDom\<cdot>sb = In"
      by (metis (full_types) Abs_sbElem_inverse mem_Collect_eq sbElem_surj sbHdElemWell_def sbHdElem_sbElemWell)
    then have spf_uneq:"(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<noteq> (y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb))))"
      by(simp add: Rep_sbElem_inverse sb_def sbE_def)
    obtain spf1 where spf_1_def:" (x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) = spf1"
      by simp
    obtain spf2 where spf_2_def:" (y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) = spf2"
      by simp
    have ufR_uneq:"ufRestrict In Out\<cdot>spf1 \<noteq> ufRestrict In Out\<cdot>spf2"
      by (metis (mono_tags, lifting) Rep_sbElem_inverse ax ay mem_Collect_eq sbE_def sb_def spf_1_def spf_2_def ufRestrict_apply)
    have uf_eq:"ufRestrict In Out\<cdot>spf1 = spf1 \<and> ufRestrict In Out\<cdot>spf2 = spf2"
      using ax ay spf_1_def spf_2_def by auto
    then have "spf1 \<noteq> spf2"
      using ufR_uneq by auto
    have sb_Well:"sbHdElemWell sb"
      by(simp add: sb_def)
    have h:"(\<lambda> sb. if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then ufRestrict In Out\<cdot>(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out) \<noteq>
             (\<lambda> sb. if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then ufRestrict In Out\<cdot>(y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)"
      apply(subst fun_eq_iff,auto)
      apply(rule_tac x="sb" in exI)
      using sb_def spf_1_def spf_2_def ufR_uneq by blast
    have "(\<Lambda> sb. if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then ufRestrict In Out\<cdot>(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out) \<noteq>
             (\<Lambda> sb. if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then ufRestrict In Out\<cdot>(y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)"
      apply(subst cfun_eq_iff, auto)
      apply(rule_tac x="sb" in exI)
      using \<open>(spf1::('a stream\<^sup>\<Omega>) ufun) \<noteq> (spf2::('a stream\<^sup>\<Omega>) ufun)\<close> assms sb_def spf_1_def spf_2_def uf_eq by auto
    then show ?thesis
      by (simp add: a4)
  next
    case False
    then show ?thesis 
      by simp
  qed
qed

lemma spfStep_eq_sb:assumes"sb1 \<sqsubseteq> sb2" and "sbHdElemWell sb1" shows "spfStep_inj In Out\<cdot>h\<cdot>sb1 = spfStep_inj In Out\<cdot>h\<cdot>sb2"
  sorry


lemma spf_contI2 [simp]: assumes "cont g"
  shows "cont (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)"
  by (simp add: assms)


definition spfStep::"channel set \<Rightarrow> channel set \<Rightarrow> ('m::message sbElem \<Rightarrow> 'm SPF)\<rightarrow>'m SPF" where
"spfStep In Out = (\<Lambda> h. Abs_ufun(\<Lambda> sb. (ubDom\<cdot>sb = In) \<leadsto> spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb))"

lemma spfStep_inner_cont[simp]:"cont((\<lambda> sb. (ubDom\<cdot>sb = In) \<leadsto> spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb))"
proof(rule spf_contI2)
  show "cont (\<lambda>b::'a stream\<^sup>\<Omega>. spfStep_inj In Out\<cdot>h\<cdot>b \<rightleftharpoons> b)"
  proof(rule Cont.contI2)
    show "monofun (\<lambda>b::'a stream\<^sup>\<Omega>. spfStep_inj In Out\<cdot>h\<cdot>b \<rightleftharpoons> b)"
    proof(rule monofunI)
      fix x y::"'a stream\<^sup>\<Omega>"
      assume a1:"x \<sqsubseteq> y"
      have "spfStep_inj In Out\<cdot>h\<cdot>x \<sqsubseteq> spfStep_inj In Out\<cdot>h\<cdot>y"
        by (simp add: a1 cont_pref_eq2I)
      then show "spfStep_inj In Out\<cdot>h\<cdot>x \<rightleftharpoons> x \<sqsubseteq> spfStep_inj In Out\<cdot>h\<cdot>y \<rightleftharpoons> y"
        apply (simp add: below_ufun_def below_cfun_def below_fun_def)
        by (metis a1 below_option_def below_refl cfun_belowI monofun_cfun)
    qed
  next
    fix Y::"nat \<Rightarrow> 'a stream\<^sup>\<Omega>"
    assume a1:"chain Y"
    assume a2:"chain (\<lambda>i::nat. spfStep_inj In Out\<cdot>h\<cdot>(Y i) \<rightleftharpoons> Y i)"
    have "(\<Squnion>(i::nat) ia::nat. spfStep_inj In Out\<cdot>h\<cdot>(Y ia) \<rightleftharpoons> Y i) =(\<Squnion>i. spfStep_inj In Out\<cdot>h\<cdot>(Y i) \<rightleftharpoons> Y i)"
      by (simp add: diag_lub a1 op_the_chain)
    then show "spfStep_inj In Out\<cdot>h\<cdot>(\<Squnion>i::nat. Y i) \<rightleftharpoons> (\<Squnion>i::nat. Y i) \<sqsubseteq> (\<Squnion>i::nat. spfStep_inj In Out\<cdot>h\<cdot>(Y i) \<rightleftharpoons> Y i)"
      by(simp add: a1 contlub_cfun_arg op_the_lub spfapply_lub)
  qed
qed

lemma ufLeast_out_ubDom:assumes "ubDom\<cdot>sb = In" shows "ubDom\<cdot>(ufLeast In Out \<rightleftharpoons> sb) = Out"
  apply(simp add: ufLeast_def assms)
  by (metis assms ubclDom_ubundle_def ubcldom_least_cs)
    
lemma spfStep_inj_out_dom[simp]:assumes"ubDom\<cdot>sb = In" and "finite In" shows "ubclDom\<cdot>(spfStep_inj In Out\<cdot> h \<cdot> f \<rightleftharpoons> sb) = Out"
  apply (subst ufran_2_ubcldom2)
   apply (simp add: spfStep_inj_def assms)
   apply (simp add: assms(1) ubclDom_ubundle_def)
  by (simp add: assms(2) spfStep_inj_def)
(*  by (metis assms ubclDom_ubundle_def ufRestrict_dom ufRestrict_ran ufran_2_ubcldom2) *)

lemma spfStep_inj_ran[simp]:assumes "finite In" shows"ufRan\<cdot>(spfStep_inj In Out\<cdot> h \<cdot> f) = Out"
  by(simp add: spfStep_inj_def assms)

lemma spf_pref_eq_2: assumes "(f \<sqsubseteq> g)"
  shows "(f \<rightleftharpoons> a) \<sqsubseteq> (g \<rightleftharpoons> a)" 
  by (metis assms below_ufun_def below_option_def cfun_below_iff po_eq_conv)
    
lemma spfStep_inj_inner_well[simp]:assumes "finite In" shows  "ufWell(\<Lambda> sb. (ubDom\<cdot>sb = In) \<leadsto> spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb)"
  proof(rule ufwellI)
    fix b::"'a SB"
    assume "b \<in> dom (Rep_cfun (\<Lambda> sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb))"
    hence b_def:" b \<in> dom (\<lambda> sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb)" 
      by simp
    thus "ubDom\<cdot>b = In"
    proof -
      show ?thesis
        by (smt b_def domIff)
    qed
    thus "ubDom\<cdot>(the ((\<Lambda> sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb)\<cdot>b)) = Out"
    proof -
      have "True \<and> ubDom\<cdot>(spfStep_inj In Out\<cdot>h\<cdot>b \<rightleftharpoons> b) = Out"
        by (metis \<open>ubDom\<cdot>(b::'a stream\<^sup>\<Omega>) = (In::channel set)\<close> assms spfStep_inj_out_dom ubclDom_ubundle_def)
      then show ?thesis
        by (simp add: \<open>ubDom\<cdot>(b::'a stream\<^sup>\<Omega>) = (In::channel set)\<close>)
    qed
  next
    fix b2::"'a SB"
    assume "ubDom\<cdot>b2 = In"
    thus "b2 \<in> dom (Rep_cfun (\<Lambda> sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb))" 
      by (simp add: domIff)
qed

lemma spfStep_cont[simp]:assumes "finite In" 
  shows "cont(\<lambda> h. Abs_ufun(\<Lambda> sb. (ubDom\<cdot>sb = In) \<leadsto> spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb))"
proof(rule Cont.contI2)
  show "monofun
     (\<lambda>h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun.
         Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb))"
    apply (rule monofunI)
    apply(simp add: below_ufun_def below_cfun_def below_fun_def, auto)
    apply (simp add: assms rep_abs_cufun)
  proof -
    fix x :: "'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun" and y :: "'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun" and xa :: "'a stream\<^sup>\<Omega>"
    assume "\<forall>xa xb. Rep_cufun (x xa) xb \<sqsubseteq> Rep_cufun (y xa) xb"
    then have "x \<sqsubseteq> y"
      by (simp add: below_fun_def below_ufun_def cfun_below_iff)
    moreover
    { assume "Rep_cufun (spfStep_inj In Out\<cdot>y\<cdot>xa) xa \<noteq> Rep_cufun (spfStep_inj In Out\<cdot>x\<cdot>xa) xa \<and> x \<sqsubseteq> y"
      then have "ubDom\<cdot>xa = In \<longrightarrow> Some (spfStep_inj In Out\<cdot>x\<cdot>xa \<rightleftharpoons> xa) \<sqsubseteq> Some (spfStep_inj In Out\<cdot>y\<cdot>xa \<rightleftharpoons> xa)"
        by (metis (no_types) below_option_def below_ufun_def cfun_below_iff monofun_cfun_arg some_below) }
    ultimately show "ubDom\<cdot>xa = In \<longrightarrow> Some (spfStep_inj In Out\<cdot>x\<cdot>xa \<rightleftharpoons> xa) \<sqsubseteq> Some (spfStep_inj In Out\<cdot>y\<cdot>xa \<rightleftharpoons> xa)"
      by fastforce
  qed
next
  fix Y ::"nat \<Rightarrow> 'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun"
  assume y_chain: "chain Y"
  assume cufun_chain: "chain (\<lambda>i::nat. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>(Y i)\<cdot>sb \<rightleftharpoons> sb))"
  have dom_L: "ufDom\<cdot>
    (Abs_cufun
      (\<lambda>sb::'a stream\<^sup>\<Omega>.
          (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>(\<Squnion>i::nat. Y i)\<cdot>sb \<rightleftharpoons> sb)) = In"
    apply (fold ubclDom_ubundle_def)
    apply (rule ufun_ufdom_abs)
     apply (simp add: ubclDom_ubundle_def)
    by (simp add: assms ubclDom_ubundle_def)
  have dom_R: "ufDom\<cdot>
    (\<Squnion>i::nat.
        Abs_cufun
         (\<lambda>sb::'a stream\<^sup>\<Omega>. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>(Y i)\<cdot>sb \<rightleftharpoons> sb)) = In"
    apply (fold ubclDom_ubundle_def)
    apply (subst ufdom_lub_eq)
     apply (simp add: cufun_chain ubclDom_ubundle_def)
    apply (rule ufun_ufdom_abs)
    apply (simp add: ubclDom_ubundle_def)
    by (simp add: assms ubclDom_ubundle_def)
  show "Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>(\<Squnion>i::nat. Y i)\<cdot>sb \<rightleftharpoons> sb) \<sqsubseteq>
       (\<Squnion>i::nat. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>(Y i)\<cdot>sb \<rightleftharpoons> sb))"
    apply (rule ufun_belowI)
     apply (simp_all add: dom_L dom_R)
     apply (simp_all add: rep_abs_cufun assms)
    apply (fold ubclDom_ubundle_def)
    apply simp
    apply (simp add: rep_cufun_lub_apply ubclDom_ubundle_def cufun_chain)
    apply (simp add: rep_abs_cufun assms ubclDom_ubundle_def)
    by (simp add: contlub_cfun_arg contlub_cfun_fun spfapply_lub y_chain)
qed
     

lemma spfstep_dom[simp]:assumes "finite cIn" shows "ufDom\<cdot>(spfStep cIn cOut\<cdot>f) = cIn"
  apply (simp add: spfStep_def assms)
  apply (fold ubclDom_ubundle_def)
  apply (rule ufun_ufdom_abs)
  by (simp_all add: assms ubclDom_ubundle_def)
    
lemma spfstep_ran [simp]:assumes "finite cIn" shows "ufRan\<cdot>(spfStep cIn cOut\<cdot>f) = cOut"
  apply (subst ufran_least)
  apply (simp add: assms)
  apply (simp add: spfStep_def assms)
  by (metis ubclDom_ubundle_def ubcldom_least_cs)
    
    
lemma spfstep_inj_dom[simp]:assumes "finite cIn" shows "ufDom\<cdot>(spfStep_inj cIn cOut\<cdot>f\<cdot>sb) = cIn"
  by (simp add:  assms spfStep_inj_def)
    
lemma spfstep_inj_ran [simp]:assumes "finite cIn" shows "ufRan\<cdot>(spfStep_inj cIn cOut\<cdot>f\<cdot>sb) = cOut"
  by (simp add:  assms spfStep_inj_def)
    
lemma test2:"ubDom\<cdot>sb \<noteq> In \<Longrightarrow> (ufRestrict In Out\<cdot>spf \<rightleftharpoons> sb) = the None"
  apply(simp add: ufRestrict_def)
  by (metis option.exhaust_sel ubclDom_ubundle_def ufdom_2ufundom ufleast_ufdom)
    
lemma test2_2:"ubDom\<cdot>sb \<noteq> In \<Longrightarrow> (ufLeast In Out \<rightleftharpoons> sb) = the None"
  apply(simp add: ufLeast_def)
  by (simp add: ubclDom_ubundle_def)
    
  
lemma spfStep_2_spfStep_inj: assumes "finite In" shows "spfStep In Out\<cdot>h \<rightleftharpoons> sb = spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb"
  apply(rule ub_eq)
   apply (metis (no_types, hide_lams) assms not_None_eq spfstep_dom spfstep_inj_dom 
      spfstep_inj_ran spfstep_ran ubclDom_ubundle_def ufdom_2ufundom ufran_2_ubcldom2)
  by (simp add: assms spfStep_def spfStep_inj_def test2_2)
(* lemma spfstep_insert  *)

    
lemma spfstep_step: assumes "ubDom\<cdot>sb = In" 
  and "sbHdElemWell sb" and "finite In" 
  and "ufDom\<cdot>(f (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) = In 
      \<and> ufRan\<cdot>(f (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) = Out"
shows "spfStep In Out\<cdot>f \<rightleftharpoons> sb = (f (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb))))\<rightleftharpoons>sb"
  by (simp add:spfStep_2_spfStep_inj  spfStep_inj_def assms)

end