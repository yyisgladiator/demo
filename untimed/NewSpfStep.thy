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
"spfStep_inj In Out \<equiv> (\<Lambda> h. (\<Lambda> sb. (if (sbHdElemWell sb) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)))"

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


lemma spfStep_inj_cont_h[simp]:"cont (\<lambda> sb. (if (sbHdElemWell sb) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out))"(*Maybe In has to be finite for cont*)
proof(rule Cont.contI2, simp)
  fix Y::"nat \<Rightarrow> 'a stream\<^sup>\<Omega>"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i. if sbHdElemWell (Y i) then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(Y i))))) else ufLeast In Out)"
  have dom:"ufDom\<cdot>(\<Squnion>i::nat. if sbHdElemWell (Y i) then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(Y i))))) else ufLeast In Out) = In"
    by (smt a2 ufRestrict_dom ufdom_lub_eq ufleast_ufdom)
  have ran:"ufRan\<cdot>(\<Squnion>i::nat. if sbHdElemWell (Y i) then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(Y i))))) else ufLeast In Out) = Out"
    by (smt a2 ufRestrict_ran ufleast_ufRan ufran_lub_eq)  
  have sbHdEq:"\<And>i. sbHdElemWell (Y i) \<Longrightarrow> (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(\<Squnion>i. Y i)))) = (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(Y i))))"
    by (metis a1 is_ub_thelub sbHdElemWell_def sbHdElem_eq)
  show "(if sbHdElemWell (\<Squnion>i. Y i) then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(\<Squnion>i. Y i))))) else ufLeast In Out) \<sqsubseteq>
       (\<Squnion>i. if sbHdElemWell (Y i) then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(Y i))))) else ufLeast In Out)"
  proof(cases "sbHdElemWell (\<Squnion>i. Y i)")
    case True
    obtain n where n_def:"sbHdElemWell (Y n)"
      sorry
    then have h1:"(if sbHdElemWell (\<Squnion>i. Y i) then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(\<Squnion>i. Y i))))) else ufLeast In Out) = (ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>( Y n))))))"
      by(subst sbHdEq[of n], simp_all add: True n_def)
    then have h2:"ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(Y n)))))\<sqsubseteq> (\<Squnion>i. (if sbHdElemWell (Y i) then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(Y i))))) else ufLeast In Out))"
        using a2 below_lub n_def by fastforce
    then show ?thesis
      by (simp add: h1)
  next
    case False
    then show ?thesis
      using dom ran by auto
  qed
qed
  
lemma spfStep_inj_mono[simp]:"monofun (\<lambda> h. (\<Lambda> sb. (if (sbHdElemWell sb) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)))"
proof(rule monofunI)
  fix x y ::"'a sbElem \<Rightarrow> 'b ufun"
  assume a1:"x \<sqsubseteq> y"
  show "(\<Lambda> sb. if sbHdElemWell sb then ufRestrict In Out\<cdot>(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out) \<sqsubseteq>
       (\<Lambda> sb. if sbHdElemWell sb then ufRestrict In Out\<cdot>(y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)"
  proof(rule cfun_belowI,auto)
    fix xa::"'a stream\<^sup>\<Omega>"
    assume a2:"sbHdElemWell xa"
    show "ufRestrict In Out\<cdot>(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>xa)))) \<sqsubseteq> ufRestrict In Out\<cdot>(y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>xa))))"
      by (simp add: a1 cont_pref_eq1I fun_belowD)
  qed
qed
    

lemma spfStep_inj_cont[simp]:"cont (\<lambda> h. (\<Lambda> sb. (if (sbHdElemWell sb) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)))"
proof(rule Cont.contI2, simp)
  fix Y::"nat \<Rightarrow> 'a sbElem \<Rightarrow> 'b ufun"
  assume a1: "chain Y"
  assume a2: "chain (\<lambda>i::nat. \<Lambda> (sb::'a stream\<^sup>\<Omega>). if sbHdElemWell sb then ufRestrict In Out\<cdot>(Y i (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)"
  have cont_lub:"\<And>x::'a stream\<^sup>\<Omega>. cont (\<lambda>x::'a stream\<^sup>\<Omega>. \<Squnion>i::nat. if sbHdElemWell x then ufRestrict In Out\<cdot>(Y i (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>x)))) else ufLeast In Out)"
  proof(rule cont2cont_lub, simp_all add: a2)
    fix sb::"'a stream\<^sup>\<Omega>"
    show "chain (\<lambda>i. if sbHdElemWell sb then ufRestrict In Out\<cdot>(Y i (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)"
    proof(cases "sbHdElemWell sb")
      case True
      then show ?thesis 
        by (simp add: a1 ch2ch_fun)
    next
      case False
      then show ?thesis
        by simp
    qed
  qed
  show "(\<Lambda> sb. if sbHdElemWell sb then ufRestrict In Out\<cdot>((\<Squnion>i::nat. Y i) (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out) \<sqsubseteq>
       (\<Squnion>i. \<Lambda> sb. if sbHdElemWell sb then ufRestrict In Out\<cdot>(Y i (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)"
    apply(subst lub_cfun, simp add: a2)
    apply(simp only: below_cfun_def below_fun_def)
    apply(subst beta_cfun, simp)
    apply(subst beta_cfun)
    apply simp
    apply(subst beta_cfun, simp only: cont_lub)
    by (simp add: a1 ch2ch_fun cont2contlubE lub_fun)
qed
  
        
    
lemma sbElem_surj_h:" \<exists>sb. f = (inv convDiscrUp (sbHdElem\<cdot>sb)) \<and> sbHdElemWell sb"
proof-    
  show "\<exists>sb. f = inv convDiscrUp (sbHdElem\<cdot>sb) \<and> sbHdElemWell sb"
    sorry
qed
          
lemma sbElem_surj:"\<exists>sb. sbE =  Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)) \<and> sbHdElemWell sb"
  sorry
    
lemma spfStep_inj_on[simp]:"inj_on (Rep_cfun (spfStep_inj In Out)) {h. \<forall>m. ufDom\<cdot>(h m) = In \<and> ufRan\<cdot>(h m) = Out}"
proof(simp add: spfStep_inj_def, rule inj_onI)
  fix x y :: "'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun"
  assume ax:" x \<in> {h. \<forall>m. ufDom\<cdot>(h m) = In \<and> ufRan\<cdot>(h m) = Out}"
  assume ay:" y \<in> {h. \<forall>m. ufDom\<cdot>(h m) = In \<and> ufRan\<cdot>(h m) = Out}"
  assume a1:"(\<Lambda> sb. if sbHdElemWell sb then ufRestrict In Out\<cdot>(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out) =
             (\<Lambda> sb. if sbHdElemWell sb then ufRestrict In Out\<cdot>(y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)"
  have ya:"(\<forall>elem.  ufDom\<cdot>(y elem) = In \<and> ufRan\<cdot>(y elem) = Out)"
    using ay by auto
  have xa:"(\<forall>elem.  ufDom\<cdot>(x elem) = In \<and> ufRan\<cdot>(x elem) = Out)"
    using ax by auto
  show "x = y"
  proof(cases "x \<noteq> y")
    case True
    then obtain sbE where sbE_def:" x sbE \<noteq> y sbE"
      by fastforce
    then obtain sb where sb_def:"((inv convDiscrUp (sbHdElem\<cdot>sb))) =  (Rep_sbElem sbE) \<and> sbHdElemWell sb"
      using sbElem_surj_h  by metis
    then have spf_uneq:"(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<noteq> (y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb))))"
      by(simp add: Rep_sbElem_inverse sb_def sbE_def)
    obtain spf1 where spf_1_def:" (x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) = spf1"
      by simp
    obtain spf2 where spf_2_def:" (y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) = spf2"
      by simp
    have ufR_uneq:"ufRestrict In Out\<cdot>spf1 \<noteq> ufRestrict In Out\<cdot>spf2"
      using ax ya spf_uneq spf_1_def spf_2_def by auto
    have uf_eq:"ufRestrict In Out\<cdot>spf1 = spf1 \<and> ufRestrict In Out\<cdot>spf2 = spf2"
      using ax spf_1_def spf_2_def ya by auto
    then have "spf1 \<noteq> spf2"
      using ufR_uneq by auto
    have sb_Well:"sbHdElemWell sb"
      by(simp add: sb_def)
    have h:"(\<lambda> sb. if sbHdElemWell sb then ufRestrict In Out\<cdot>(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out) \<noteq>
             (\<lambda> sb. if sbHdElemWell sb then ufRestrict In Out\<cdot>(y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)"
      apply(subst fun_eq_iff,auto)
      apply(rule_tac x="sb" in exI)
      by(simp add: spf_1_def spf_2_def ufR_uneq sb_Well)
    have "(\<Lambda> sb. if sbHdElemWell sb then ufRestrict In Out\<cdot>(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out) \<noteq>
             (\<Lambda> sb. if sbHdElemWell sb then ufRestrict In Out\<cdot>(y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)"
      apply(subst cfun_eq_iff, auto)
      apply(rule_tac x="sb" in exI)
      by(simp add: spf_1_def spf_2_def ufR_uneq sb_Well)
    then show ?thesis
      by(simp add: a1)
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
        by (smt a1 below_option_def below_refl box_below monofun_cfun_arg)
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
    
lemma spfStep_inj_out_dom[simp]:assumes"ubDom\<cdot>sb = In" shows "ubDom\<cdot>(spfStep_inj In Out\<cdot> h \<cdot> f \<rightleftharpoons> sb) = Out"
  apply(simp add: spfStep_inj_def assms ufLeast_out_ubDom)
  by (metis assms ubclDom_ubundle_def ufRestrict_dom ufRestrict_ran ufran_2_ubcldom2)

lemma spfStep_inj_ran[simp]:assumes "finite In" shows"ufRan\<cdot>(spfStep_inj In Out\<cdot> h \<cdot> f) = Out"
  by(simp add: spfStep_inj_def assms)

lemma spf_pref_eq_2: assumes "(f \<sqsubseteq> g)"
  shows "(f \<rightleftharpoons> a) \<sqsubseteq> (g \<rightleftharpoons> a)" 
  by (metis assms below_ufun_def below_option_def cfun_below_iff po_eq_conv)
    
lemma spfStep_inj_inner_well[simp]:"ufWell(\<Lambda> sb. (ubDom\<cdot>sb = In) \<leadsto> spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb)"
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
      by simp 
  next
    fix b2::"'a SB"
    assume "ubDom\<cdot>b2 = In"
    thus "b2 \<in> dom (Rep_cfun (\<Lambda> sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb))" 
      by (simp add: domIff)
qed

lemma spfStep_cont[simp]:"cont(\<lambda> h. Abs_ufun(\<Lambda> sb. (ubDom\<cdot>sb = In) \<leadsto> spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb))"
proof(rule Cont.contI2)
  show "monofun (\<lambda>h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb))"
  proof(rule monofunI)
    fix x y::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun"
    assume a1:"x \<sqsubseteq> y"
    show "Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>x\<cdot>sb \<rightleftharpoons> sb) \<sqsubseteq> Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>y\<cdot>sb \<rightleftharpoons> sb)"
      apply(simp add: below_ufun_def below_cfun_def below_fun_def, auto)
      by (meson a1 cfun_below_iff monofun_cfun_arg some_below spf_pref_eq_2)
  qed
next
  fix Y::"nat \<Rightarrow> 'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>(Y i)\<cdot>sb \<rightleftharpoons> sb))"
  have h1_0:"\<And>sb. (spfStep_inj In Out\<cdot>(\<Squnion>i. Y i)\<cdot>sb \<rightleftharpoons> sb) = (\<Squnion>i. spfStep_inj In Out\<cdot>(Y i)\<cdot>sb \<rightleftharpoons> sb)"
    apply(subst contlub_cfun_arg, simp add: a1)
    apply(subst contlub_cfun_fun)
    using a1 apply auto[1]
    apply(rule spfapply_lub)
    using a1 by auto[1]
    have h0_2:"\<forall>sb. ((ubDom\<cdot>sb = In)\<leadsto>\<Squnion>i. spfStep_inj In Out\<cdot>(Y i)\<cdot>sb \<rightleftharpoons> sb) = (\<Squnion>i. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>(Y i)\<cdot>sb \<rightleftharpoons> sb)"
  proof(auto)
    fix sb::"'a stream\<^sup>\<Omega>"
    assume a11: "In = ubDom\<cdot>sb"  
    have h0_21:"((ubDom\<cdot>sb = In)\<leadsto>(\<Squnion>i. spfStep_inj In Out\<cdot>(Y i)\<cdot>sb \<rightleftharpoons> sb)) = (\<Squnion>i. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>(Y i)\<cdot>sb \<rightleftharpoons> sb)"
    proof(cases "ubDom\<cdot>sb = In")
      case True
      then show ?thesis 
        apply auto
        apply(rule some_lub_chain_eq2)
        by (meson a1 monofun_cfun_arg monofun_cfun_fun po_class.chain_def spf_pref_eq_2)
    next
      case False
      then show ?thesis 
        by simp
    qed
    show"Some (\<Squnion>i. (spfStep_inj (ubDom\<cdot>sb) Out\<cdot>(Y i)\<cdot>sb) \<rightleftharpoons> sb) = (\<Squnion>i. Some ((spfStep_inj (ubDom\<cdot>sb) Out\<cdot>(Y i)\<cdot>sb) \<rightleftharpoons> sb))"
      using a11 h0_21 by auto
  qed 
  have cont_lub2:"cont (\<lambda>x. \<Squnion>i. (ubDom\<cdot>x = In)\<leadsto>spfStep_inj In Out\<cdot>(Y i)\<cdot>x \<rightleftharpoons> x)"
    apply(rule cont2cont_lub)
    apply(rule chainI)
    apply (smt a1 cont_pref_eq1I eq_imp_below monofun_cfun_fun po_class.chain_def some_below spf_pref_eq_2)
    by simp  
  have ufWell:"ufWell (\<Lambda> x. \<Squnion>i::nat. Rep_cufun (Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>(Y i)\<cdot>sb \<rightleftharpoons> sb)) x)"
  apply(subst rep_abs_cufun, simp, simp)
  proof(rule ufwellI)
    fix b:: "'a stream\<^sup>\<Omega>"    
    assume "b \<in> dom (Rep_cfun (\<Lambda> (x::'a stream\<^sup>\<Omega>). \<Squnion>i::nat. (ubDom\<cdot>x = In)\<leadsto>spfStep_inj In Out\<cdot>(Y i)\<cdot>x \<rightleftharpoons> x))"
    hence b_def:" b \<in> dom (\<lambda> x. \<Squnion>i. (ubDom\<cdot>x = In) \<leadsto> spfStep_inj In Out\<cdot>(Y i)\<cdot>x \<rightleftharpoons> x)"
      using cont_lub2 by auto
    thus "ubDom\<cdot>b = In"
      by (metis (no_types, lifting) domIff h0_2)
    thus "ubDom\<cdot>Rep_cfun (\<Lambda> x. \<Squnion>i. (ubDom\<cdot>x = In)\<leadsto>spfStep_inj In Out\<cdot>(Y i)\<cdot>x \<rightleftharpoons> x)\<rightharpoonup>b = Out"
      apply(subst beta_cfun,subst cont_lub2, simp,simp)
      by (smt h0_2 h1_0 lub_eq option.sel spfStep_inj_out_dom)
  next
    fix b2::"'a stream\<^sup>\<Omega>"
    assume "ubDom\<cdot>b2 = In"
    thus "b2 \<in> dom (Rep_cfun (\<Lambda> x. \<Squnion>i. (ubDom\<cdot>x = In)\<leadsto>spfStep_inj In Out\<cdot>(Y i)\<cdot>x \<rightleftharpoons> x))"
    proof -
      show ?thesis
        by (metis (lifting) Abs_cfun_inverse2 \<open>ubDom\<cdot>b2 = In\<close> cont_lub2 domIff h0_2 option.distinct(1))
    qed
  qed
  have h1:"(\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>(\<Squnion>i. Y i)\<cdot>sb \<rightleftharpoons> sb) \<sqsubseteq> Rep_cufun (\<Squnion>i. Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>(Y i)\<cdot>sb \<rightleftharpoons> sb))"
    apply(subst h1_0, subst h0_2)
    apply(subst lub_ufun)
    apply (simp add: a2)
    apply(subst lub_cfun)
    using a2 rep_ufun_chain apply blast
    apply(subst rep_abs_cufun)
    apply(subst rep_abs_cufun, simp,simp)
    apply(simp_all only: ufWell cont_lub2)
    by simp
  show " Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>(\<Squnion>i. Y i)\<cdot>sb \<rightleftharpoons> sb) \<sqsubseteq>
       (\<Squnion>i::nat. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. (ubDom\<cdot>sb = In)\<leadsto>spfStep_inj In Out\<cdot>(Y i)\<cdot>sb \<rightleftharpoons> sb))"
    by(simp add: below_ufun_def below_cfun_def h1)
qed
     

lemma spfstep_dom[simp]:"ufDom\<cdot>(spfStep cIn cOut\<cdot>f) = cIn"
  sorry
    
lemma spfstep_ran [simp]:"ufRan\<cdot>(spfStep cIn cOut\<cdot>f) = cOut"
  sorry
    
    
lemma spfstep_inj_dom[simp]:"ufDom\<cdot>(spfStep_inj cIn cOut\<cdot>f\<cdot>sb) = cIn"
  sorry
    
lemma spfstep_inj_ran [simp]:"ufRan\<cdot>(spfStep_inj cIn cOut\<cdot>f\<cdot>sb) = cOut"
  sorry
    
lemma test2:"ubDom\<cdot>sb \<noteq> In \<Longrightarrow> (ufRestrict In Out\<cdot>spf \<rightleftharpoons> sb) = the None"
  apply(simp add: ufRestrict_def)
  by (metis option.exhaust_sel ubclDom_ubundle_def ufdom_2ufundom ufleast_ufdom)
    
lemma test2_2:"ubDom\<cdot>sb \<noteq> In \<Longrightarrow> (ufLeast In Out \<rightleftharpoons> sb) = the None"
  apply(simp add: ufLeast_def)
  by (simp add: ubclDom_ubundle_def)
    
  
lemma spfStep_2_spfStep_inj: "spfStep In Out\<cdot>h \<rightleftharpoons> sb = spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb"
  apply(rule ub_eq)
   apply (metis (no_types, lifting) option.exhaust_sel spfstep_dom spfstep_inj_dom spfstep_inj_ran
      spfstep_ran ubclDom_ubundle_def ufdom_2ufundom ufran_2_ubcldom2)
  apply(simp add: spfStep_def spfStep_inj_def, auto)
  using test2 test2_2 by fastforce+
    
(* lemma spfstep_insert  *)

    
lemma spfstep_step: assumes "ubDom\<cdot>sb = In" 
  and "sbHdElemWell sb" and "finite In" 
  and "ufDom\<cdot>(f (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) = In 
      \<and> ufRan\<cdot>(f (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) = Out"
shows "spfStep In Out\<cdot>f \<rightleftharpoons> sb = (f (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb))))\<rightleftharpoons>sb"
  by (simp add:spfStep_2_spfStep_inj  spfStep_inj_def assms)

end