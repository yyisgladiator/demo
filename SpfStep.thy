(*  Title:        SpfStep
    Author:       Hendrik Kausch
    e-mail:       hendrik.kausch@rwth-aachen.de
*)

theory SpfStep
imports SPF If_Else_Continuity
begin
default_sort type

(* updis bijectiv *)
thm inv_def
  
(*Just used to transform the function*)  
definition spfStep_h2::" channel set \<Rightarrow> (channel\<rightharpoonup>'m::message discr\<^sub>\<bottom>) \<Rightarrow> (channel\<rightharpoonup>'m)" where
"spfStep_h2 In = (\<lambda>f. (\<lambda>c. (c \<in> In) \<leadsto> (inv updis f \<rightharpoonup> c)))"

(* If the conditions are correct then we use imput h to compute a SPF. After that check if the SPF has the right dom and ran*)
definition spfStep_h1::"channel set \<Rightarrow> channel set \<Rightarrow>((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF) \<rightarrow>((channel\<rightharpoonup>'m discr\<^sub>\<bottom>)\<rightarrow> 'm SPF)" where
"spfStep_h1 In Out= (\<Lambda> h. (\<Lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In f)) else spfLeast In Out))"

lemma[simp]: "spfDom\<cdot>((\<lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In f)) else spfLeast In Out)f) = In"
  by simp
    
lemma[simp]: "spfRan\<cdot>((\<lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In f)) else spfLeast In Out)f) = Out"
  by simp

lemma spfRestrict_apply2[simp]: assumes "spfDom\<cdot>f \<noteq> In \<or> spfRan\<cdot>f \<noteq> Out" shows "spfRestrict In Out\<cdot>f = spfLeast In Out"
  apply(simp add: spfRestrict_def)
  using assms by blast

lemma assumes "F \<sqsubseteq> G" shows "spfRestrict In Out\<cdot>F = F \<Longrightarrow> spfRestrict In Out\<cdot>G = G"
  by (metis assms spfRestrict_apply spfRestrict_dom spfRestrict_ran spfdom_eq spfran_eq)

lemma discr_u_below_eq:assumes "(x::'a discr\<^sub>\<bottom>)\<sqsubseteq>y" and "x\<noteq>\<bottom>" shows "x = y"
  proof(insert assms(1), simp add: below_up_def assms)
    have "x \<noteq> Ibottom"
      using assms(2) inst_up_pcpo by auto
    then have "y \<noteq>Ibottom"
      by (metis assms(1) inst_up_pcpo bottomI)
    then show "case x of Ibottom \<Rightarrow> True | Iup a \<Rightarrow> case y of Ibottom \<Rightarrow> False | Iup x \<Rightarrow> a \<sqsubseteq> x \<Longrightarrow> x = y"
      by (metis assms(2) discrete_cpo inst_up_pcpo u.exhaust u.simps(5))
  qed

lemma discr_u_Lub2n: assumes "chain (Y::nat \<Rightarrow>'a discr\<^sub>\<bottom>)" and "Y n \<noteq> \<bottom>" shows "\<Squnion>i. Y i = Y n"
  by (metis (mono_tags, lifting) SetPcpo.less_bool_def lub_chain_maxelem)
    
lemma fun_discr_u_dom_Lub2n: assumes "chain (Y::nat \<Rightarrow>(channel \<rightharpoonup> 'a discr\<^sub>\<bottom>))" and "(\<forall>c\<in>(dom (Y n)). (Y n\<rightharpoonup>c) \<noteq> \<bottom>)"  shows "\<Squnion>i. Y i = Y n"
  by (metis (full_types) SetPcpo.less_bool_def lub_chain_maxelem)

lemma fun_discr_u_spfStep_h2: assumes "chain (Y::nat \<Rightarrow>(channel \<rightharpoonup> 'a::message discr\<^sub>\<bottom>))" and "(\<forall>c\<in>In. ((Y n)\<rightharpoonup>c) \<noteq> \<bottom>)"  shows "spfStep_h2 In (\<Squnion>i. Y i) = spfStep_h2 In (Y n)"
proof
  fix x::channel
  have Lub_channel:"\<forall>c\<in>In. (\<Squnion>i. Y i) \<rightharpoonup>c= Y n \<rightharpoonup>c"
  proof -
    { fix cc :: channel
      have "\<And>f n c. \<not> chain f \<or> (f n (c::channel)::('a discr\<^sub>\<bottom>) option) \<sqsubseteq> Lub f c"
        by (meson below_fun_def is_ub_thelub)
      then have "cc \<notin> In \<or> Y n\<rightharpoonup>cc = Lub Y\<rightharpoonup>cc"
        by (metis assms(1) assms(2) below_option_def discr_u_below_eq) }
    then show ?thesis
      by simp
  qed
  have inv_updis_lub:"\<forall>c\<in>In. inv updis ((\<Squnion>i. Y i)\<rightharpoonup>c) = inv updis Y n\<rightharpoonup>c"
    by(simp add: Lub_channel)
  then have "x\<in>In \<Longrightarrow> spfStep_h2 In (\<Squnion>i. Y i) x = spfStep_h2 In (Y n) x"
    by (simp add: spfStep_h2_def inv_updis_lub)
  moreover have "x\<notin>In \<Longrightarrow> spfStep_h2 In (\<Squnion>i. Y i) x = spfStep_h2 In (Y n) x"
    by(simp add: spfStep_h2_def)
  ultimately show "spfStep_h2 In (\<Squnion>i. Y i) x = spfStep_h2 In (Y n) x"
    by blast
qed
  
lemma fun_discr_u_spfStep_h2_h: assumes "chain (Y::nat \<Rightarrow>(channel \<rightharpoonup> 'a::message discr\<^sub>\<bottom>))" and "(\<forall>c\<in>In. ((Y n)\<rightharpoonup>c) \<noteq> \<bottom>)"  shows "h(spfStep_h2 In (\<Squnion>i. Y i)) = h(spfStep_h2 In (Y n))"
  by(simp add: fun_discr_u_spfStep_h2[of Y In n] assms)

lemma spfrestrict_below: assumes"x\<sqsubseteq>y" shows "spfRestrict In Out\<cdot>x \<sqsubseteq> spfRestrict In Out\<cdot>y"
  by (simp add: assms monofun_cfun_arg)

lemma obtain_n_for_c:assumes "chain (Y::nat \<Rightarrow> channel\<rightharpoonup>'a discr\<^sub>\<bottom>)" and "((\<Squnion>i. Y i) \<rightharpoonup> c) \<noteq> \<bottom>" obtains n where "(Y n \<rightharpoonup> c) = ((\<Squnion>i. Y i) \<rightharpoonup> c)"
  by (metis (mono_tags, lifting) assms(1) discr_u_below_eq is_ub_thelub lub_eq_bottom_iff part_the_chain part_the_lub)

lemma exists_n_for_c:assumes "chain (Y::nat \<Rightarrow> channel\<rightharpoonup>'a discr\<^sub>\<bottom>)" and "((\<Squnion>i. Y i) \<rightharpoonup> c) \<noteq> \<bottom>" shows "\<exists>n. (Y n \<rightharpoonup> c) = ((\<Squnion>i. Y i) \<rightharpoonup> c)"
  by (metis (mono_tags, lifting) assms(1) discr_u_below_eq is_ub_thelub lub_eq_bottom_iff part_the_chain part_the_lub)

lemma discr_u_chain_lubnbot: assumes"chain (Y::nat \<Rightarrow> 'a discr\<^sub>\<bottom>)" and "(\<Squnion>i. Y i) \<noteq>\<bottom>" shows "\<exists>i. Y i \<noteq> \<bottom>"
  using assms(1) assms(2) lub_eq_bottom_iff by auto

lemma discr_u_chain_lubnbot_forall_c: assumes"chain (Y::nat \<Rightarrow> channel \<Rightarrow> 'a discr\<^sub>\<bottom>)" and "\<forall>c. (\<Squnion>i. Y i) c \<noteq>\<bottom>" shows "\<forall>c. \<exists>i. Y i c \<noteq> \<bottom>" 
  by (metis (no_types, lifting) assms(1) assms(2) below_refl lub_eq_bottom_iff lub_fun po_class.chain_def)
    
lemma discr_u_chain_lubnbot_equiv: assumes"chain (Y::nat \<Rightarrow> channel \<Rightarrow> 'a discr\<^sub>\<bottom>)" shows "((\<Squnion>i. Y i) c \<noteq>\<bottom>) \<longleftrightarrow> (\<exists>i. Y i c \<noteq> \<bottom>)" 
  by (simp add: assms ch2ch_fun lub_eq_bottom_iff lub_fun)

(*    
lemma test:  assumes "chain (Y::nat \<Rightarrow> channel\<rightharpoonup>'a discr\<^sub>\<bottom>)" 
  and "\<forall>c. \<exists>i. ((Y i) \<rightharpoonup> c) \<noteq> \<bottom>" 
  and "\<forall>c. ((\<Squnion>i. Y i) \<rightharpoonup> c) \<noteq> \<bottom>"
shows "finite_chain Y"
proof(rule finite_chainI, simp add: assms,rule max_in_chainI)
    show "\<exists>i. max_in_chain i Y"
    
lemma test2:
  assumes "chain (Y::nat \<Rightarrow> channel\<rightharpoonup>'a discr\<^sub>\<bottom>)" 
  and "\<forall>c\<in>In. \<exists>i. ((Y i) \<rightharpoonup> c) \<noteq> \<bottom>" 
  and "\<forall>c\<in>In. ((\<Squnion>i. Y i) \<rightharpoonup> c) \<noteq> \<bottom>" 
shows "finite_chain Y"
    sorry
  *)  
(*Change goal to finite chain Y, works only for finite channel type*)    
lemma obtain_n_for_all_c:
  assumes "chain (Y::nat \<Rightarrow> channel\<rightharpoonup>'a discr\<^sub>\<bottom>)" 
shows "finite In \<Longrightarrow> \<exists>n. \<forall>c\<in>In. ((Y n)\<rightharpoonup> c) = ((\<Squnion>i. Y i) \<rightharpoonup> c)"
proof(induct In rule: infinite_finite_induct)
  case (infinite A)
  then show ?case
    using infinite.hyps by auto
  next
    case empty
    then show ?case 
      by simp
  next
    case (insert x F)
    then show ?case
    proof-
      assume a1:"finite F"
      assume a2:"x \<notin> F"
      assume a3:"finite F \<Longrightarrow> \<exists>n. \<forall>c\<in>F. Y n\<rightharpoonup>c = \<Squnion>i. Y i\<rightharpoonup>c"
      obtain n where "\<forall>c\<in>F. Y n\<rightharpoonup>c = \<Squnion>i. Y i\<rightharpoonup>c"
        using a3 a1 by blast
      obtain m where "Y m\<rightharpoonup>x = \<Squnion>i. Y i\<rightharpoonup>x"
        by (metis (mono_tags, lifting) assms(1) lub_eq_bottom_iff obtain_n_for_c part_the_chain part_the_lub)
      show "\<exists>n. \<forall>c\<in>insert x F. Y n\<rightharpoonup>c = \<Squnion>i. Y i\<rightharpoonup>c"
      proof(cases "n \<le>m")
        case True
        have "\<forall>c\<in>F. Y n\<rightharpoonup>c \<sqsubseteq> Y m \<rightharpoonup>c"
          by (metis True assms(1) part_the_chain po_class.chain_mono)
        then have "\<forall>c\<in>F. Y n\<rightharpoonup>c = Y m \<rightharpoonup>c"
          by (metis (mono_tags, lifting) \<open>\<forall>c\<in>F. Y n\<rightharpoonup>c = \<Squnion>i. Y i\<rightharpoonup>c\<close> assms(1) discr_u_below_eq lub_eq_bottom_iff part_the_chain part_the_lub)
        then have "\<forall>c\<in>insert x F. Y m\<rightharpoonup>c = \<Squnion>i. Y i\<rightharpoonup>c"
          using \<open>Y m\<rightharpoonup>x = \<Squnion>i. Y i\<rightharpoonup>x\<close> \<open>\<forall>c\<in>F. Y n\<rightharpoonup>c = \<Squnion>i. Y i\<rightharpoonup>c\<close> by auto
        then show ?thesis
          by blast
      next
        case False
        have "\<forall>c\<in>insert x F. Y m\<rightharpoonup>c \<sqsubseteq> Y n \<rightharpoonup>c"
          by (metis False assms(1) below_option_def below_refl fun_below_iff le_cases po_class.chain_mono)
        have "\<forall>c\<in>insert x F. Y n\<rightharpoonup>c = \<Squnion>i. Y i\<rightharpoonup>c"
          by (metis (mono_tags, lifting) \<open>Y m\<rightharpoonup>x = \<Squnion>i. Y i\<rightharpoonup>x\<close> \<open>\<forall>c\<in>F. Y n\<rightharpoonup>c = \<Squnion>i. Y i\<rightharpoonup>c\<close> \<open>\<forall>c\<in>insert x F. Y m\<rightharpoonup>c \<sqsubseteq> Y n\<rightharpoonup>c\<close> assms(1) discr_u_below_eq insertE lub_eq_bottom_iff part_the_chain part_the_lub)
        then show ?thesis 
          by blast
      qed
    qed
qed


lemma obtain_n_for_all_ch:assumes "chain (Y::nat \<Rightarrow> channel\<rightharpoonup>'a discr\<^sub>\<bottom>)" and "finite In" obtains n where "\<forall>c\<in>In. ((Y n)\<rightharpoonup> c) = ((\<Squnion>i. Y i) \<rightharpoonup> c)"
  using assms(1) assms(2) obtain_n_for_all_c by blast
    

    
(*spfStep_h1 mono cont*)
    
(*    
declare[[show_types]]*)
lemma[simp]:"monofun (\<lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In f)) else spfLeast In Out)"
  proof(rule monofunI)  
    fix x and y::"(channel\<rightharpoonup>'a::message discr\<^sub>\<bottom>)"
    assume a1:"x \<sqsubseteq> y"
    show "(if In \<subseteq> dom x \<and> (\<forall>c\<in>In. x\<rightharpoonup>c \<noteq> \<bottom>) then spfRestrict In Out\<cdot>(h (spfStep_h2 In x)) else spfLeast In Out) \<sqsubseteq>
           (if In \<subseteq> dom y \<and> (\<forall>c\<in>In. y\<rightharpoonup>c \<noteq> \<bottom>) then spfRestrict In Out\<cdot>(h (spfStep_h2 In y)) else spfLeast In Out)"
    proof(cases "In \<subseteq> dom x \<and> (\<forall>c\<in>In. x\<rightharpoonup>c \<noteq> \<bottom>)")
      case True
      have "dom x = dom y"
        by (simp add: a1 part_dom_eq)
      then have h1:"In \<subseteq> dom y"
        using True by auto
      have "\<forall>c. x\<rightharpoonup> c \<sqsubseteq> y\<rightharpoonup> c"
        by (metis a1 below_option_def fun_below_iff not_below2not_eq)
      then have h2:"(\<forall>c\<in>In. y\<rightharpoonup>c \<noteq> \<bottom>)"
        by (metis True bottomI)
      have h3:"(\<And>c. c\<in>In \<Longrightarrow> x\<rightharpoonup>c = y\<rightharpoonup>c)"
      proof-
        fix c::channel
        assume a1:"c \<in> In"
        have h1:"x\<rightharpoonup>c \<noteq> \<bottom>"
          by(simp add: True a1)
        show "x\<rightharpoonup>c = y\<rightharpoonup>c"
          by (simp add: \<open>\<forall>c. x\<rightharpoonup>c \<sqsubseteq> y\<rightharpoonup>c\<close> h1 discr_u_below_eq)
      qed
      show ?thesis
      proof(simp add: True h1 h2)
        show "spfRestrict In Out\<cdot>(h (spfStep_h2 In x)) \<sqsubseteq> spfRestrict In Out\<cdot>(h (spfStep_h2 In y))"
          proof(cases "spfDom\<cdot>(h (spfStep_h2 In x)) = In \<and> spfRan\<cdot>(h (spfStep_h2 In x)) = Out")
            case True
            have "\<And>c. (c \<in> In) \<Longrightarrow> x\<rightharpoonup>c = y\<rightharpoonup>c"
              by (simp add: h3)
            then have "spfStep_h2 In x = spfStep_h2 In y" 
                by(auto simp add: spfStep_h2_def)
            then have "(h (spfStep_h2 In x)) \<sqsubseteq> (h (spfStep_h2 In y))"
              by simp
            then show ?thesis
              using cont_pref_eq1I by blast
          next
            case False
            have h11:"spfRestrict In Out\<cdot>(h (spfStep_h2 In x)) = spfLeast In Out"
              using False by auto
            then show ?thesis
              proof(cases "spfDom\<cdot>(h (spfStep_h2 In y)) = In \<and> spfRan\<cdot>(h (spfStep_h2 In y)) = Out")
                case True
                then show ?thesis
                  by (simp add: h11)
              next
                case False
                have h12:"spfRestrict In Out\<cdot>(h (spfStep_h2 In y)) = spfLeast In Out"
                  using False by auto
                then show ?thesis
                  by (simp add: h11)
              qed
          qed
      qed
    next
      case False
      show ?thesis
        by (simp add: False)
    qed
  qed
    
lemma[simp]:assumes "finite In" shows "cont(\<lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In f)) else spfLeast In Out) "
  (*apply(rule equalizing_pred_cont)
  apply(simp_all add: cont_at_def,auto)*)
  proof(rule Cont.contI2,simp)    
    fix Y::"nat \<Rightarrow> (channel\<rightharpoonup>'a::message discr\<^sub>\<bottom>)"
    assume a1:"chain Y"
    assume a2:"chain (\<lambda>i. if (In \<subseteq> dom (Y i) \<and> (\<forall>c\<in>In. ((Y i)\<rightharpoonup>c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else spfLeast In Out)"
    show "(if In \<subseteq> dom (\<Squnion>i. Y i) \<and> (\<forall>c\<in>In. (\<Squnion>i. Y i)\<rightharpoonup>c \<noteq> \<bottom>) then spfRestrict In Out\<cdot>(h (spfStep_h2 In (\<Squnion>i. Y i))) else spfLeast In Out) \<sqsubseteq>
         (\<Squnion>i. if In \<subseteq> dom (Y i) \<and> (\<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>) then spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else spfLeast In Out)"
      proof(cases "In \<subseteq> dom (\<Squnion>i. Y i) \<and> (\<forall>c\<in>In. (\<Squnion>i. Y i)\<rightharpoonup>c \<noteq> \<bottom>)")
        case True
        then have "\<forall>i. In \<subseteq> dom (Y i)" 
          by(simp add:  part_dom_lub a1)
        have chain_Yc:"\<forall>c. chain (\<lambda>i. Y i\<rightharpoonup>c)"
          using a1 by (metis part_the_chain)
        then have "\<forall>i c. Y i\<rightharpoonup>c \<sqsubseteq> Y (Suc i) \<rightharpoonup>c"
          using po_class.chainE by blast
        have "\<forall>i c. Y i\<rightharpoonup>c = \<bottom> \<Longrightarrow>\<forall>c.  (\<Squnion>i. Y i) \<rightharpoonup> c = \<bottom>"
          by (simp add: a1 part_the_lub)
        have "\<exists>c\<in>In. \<forall>i.  Y i\<rightharpoonup>c = \<bottom> \<Longrightarrow>\<exists>c\<in>In.  (\<Squnion>i. Y i) \<rightharpoonup> c = \<bottom>"
          by (simp add: a1 lub_eq_bottom_iff part_the_chain part_the_lub)
        have h123:"\<forall>c\<in>In. \<exists>i. Y i \<rightharpoonup> c \<noteq> \<bottom>"
          by (metis (mono_tags, lifting) True a1 lub_eq_bottom_iff part_the_chain part_the_lub)
        then have helper1:"\<And>c. c\<in>In \<Longrightarrow>  \<exists>i. Y i \<rightharpoonup> c \<noteq> \<bottom>"
          by simp
        have "\<And>x. \<forall>c\<in>In. Y x \<rightharpoonup> c \<noteq> \<bottom> \<Longrightarrow> \<forall>i\<ge>x. \<forall>c\<in>In. Y i \<rightharpoonup> c = Y x \<rightharpoonup> c" 
          by (metis (mono_tags, lifting) chain_Yc discr_u_below_eq po_class.chain_mono)
        have helper2:"\<And>x c. Y x \<rightharpoonup> c \<noteq> \<bottom> \<Longrightarrow> \<forall>i\<ge>x. Y i \<rightharpoonup> c = Y x \<rightharpoonup> c" 
          by (metis (mono_tags, lifting) chain_Yc discr_u_below_eq po_class.chain_mono)
        then have "\<forall>c. \<exists>i. \<forall>ia\<ge>i. Y ia  \<rightharpoonup> c = Y i  \<rightharpoonup> c"
          by metis
        have "\<forall>c\<in>In. \<exists>i. \<forall>ia\<ge>i. Y ia  \<rightharpoonup> c \<noteq> \<bottom>"
          by (metis helper1 helper2)
        have "\<forall>c\<in>In. \<exists>i. Y i \<rightharpoonup> c= (\<Squnion>i. Y i) \<rightharpoonup> c"
        proof -
          { fix cc :: channel
            have "\<And>n c. Y n\<rightharpoonup>c \<sqsubseteq> Lub Y\<rightharpoonup>c"
              by (metis a1 chain_Yc is_ub_thelub part_the_lub)
            then have "\<exists>n. cc \<notin> In \<or> Y n\<rightharpoonup>cc = Lub Y\<rightharpoonup>cc"
              by (meson discr_u_below_eq helper1) }
          then show ?thesis
            by blast
        qed
        then have "\<And> c. c\<in>In \<Longrightarrow>\<exists>i.  Y i \<rightharpoonup> c = (\<Squnion>i. Y i)\<rightharpoonup>c"
          by simp
        obtain n where "\<forall>c\<in>In. ((Y n)\<rightharpoonup>c = ((\<Squnion>i. Y i) \<rightharpoonup>c))"
          by(rule obtain_n_for_all_ch[of Y In],simp_all add: assms a1 True h123)
        then have "(\<lambda>i. if (In \<subseteq> dom (Y i) \<and> (\<forall>c\<in>In. ((Y i)\<rightharpoonup>c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else spfLeast In Out) n = spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y n)))"
        by (simp add: True \<open>\<forall>i. In \<subseteq> dom (Y i)\<close>)
        have "In \<subseteq> dom (Y n) \<and> (\<forall>c\<in>In. Y n\<rightharpoonup>c \<noteq> \<bottom>)"
          by (simp add: True \<open>\<forall>c\<in>In. Y n\<rightharpoonup>c = \<Squnion>i. Y i\<rightharpoonup>c\<close> \<open>\<forall>i. In \<subseteq> dom (Y i)\<close>)
        have "\<forall>i\<ge>n. \<forall>c\<in>In. ((Y i)\<rightharpoonup>c \<noteq> \<bottom>)" 
        proof(auto)
          fix i::nat and c::channel
          assume a1:"n \<le> i"
          assume a2:"c \<in> In"
          assume a3:"Y i\<rightharpoonup>c = \<bottom>"
          have "\<forall>c\<in>In. Y n \<rightharpoonup>c \<noteq> \<bottom>"
            by (simp add: \<open>In \<subseteq> dom (Y n) \<and> (\<forall>c\<in>In. Y n\<rightharpoonup>c \<noteq> \<bottom>)\<close>)
          have "Y n \<rightharpoonup>c \<sqsubseteq> Y i\<rightharpoonup>c"
            using \<open>\<forall>c. chain (\<lambda>i. Y i\<rightharpoonup>c)\<close> a1 po_class.chain_mono by auto
          then show "False"
            by (simp add: \<open>In \<subseteq> dom (Y n) \<and> (\<forall>c\<in>In. Y n\<rightharpoonup>c \<noteq> \<bottom>)\<close> a2 a3)
        qed
        have chain_eq_second_gen:"\<forall>i\<ge>n. (\<lambda>i. if (In \<subseteq> dom (Y i) \<and> (\<forall>c\<in>In. ((Y i)\<rightharpoonup>c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else spfLeast In Out) i = spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y i)))" 
          by (simp add: \<open>\<forall>i. In \<subseteq> dom (Y i)\<close> \<open>\<forall>i\<ge>n. \<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>\<close>)
        have chain_second_part:"chain (\<lambda>i. if n \<le> i then spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else spfLeast In Out)"
        proof(rule chainI)
          fix i::nat
          show "(if n \<le> i then spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else spfLeast In Out) \<sqsubseteq> (if n \<le> Suc i then spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y (Suc i)))) else spfLeast In Out)"
          proof(cases "n \<le> i")
            case True
            have "\<forall>c\<in>In. Y i\<rightharpoonup>c = Y (Suc i)\<rightharpoonup>c"
              using True \<open>\<forall>i c. Y i\<rightharpoonup>c \<sqsubseteq> Y (Suc i)\<rightharpoonup>c\<close> \<open>\<forall>i\<ge>n. \<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>\<close> discr_u_below_eq by blast
            then have "\<forall>c\<in>In. inv updis (Y i)\<rightharpoonup>c = inv updis Y (Suc i)\<rightharpoonup>c"
              by simp
            then have h_13:"(\<lambda>c. (c \<in> In)\<leadsto>inv updis Y i\<rightharpoonup>c) = (\<lambda>c. (c \<in> In)\<leadsto>inv updis Y (Suc i)\<rightharpoonup>c)"
              by auto
            show ?thesis
              by(simp add: spfStep_h2_def h_13)
          next
            case False
            then show ?thesis 
              by simp
          qed
        qed
        have h1:"(if In \<subseteq> dom (Y n) \<and> (\<forall>c\<in>In. (Y n\<rightharpoonup>c \<noteq> \<bottom>)) then spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y n))) else spfLeast In Out) \<sqsubseteq>(\<Squnion>i. if In \<subseteq> dom (Y i) \<and> (\<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>) then spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else spfLeast In Out)"
          using a2 below_lub by blast
        have h2:"(if In \<subseteq> dom (\<Squnion>i. Y i) \<and> (\<forall>c\<in>In. (\<Squnion>i. Y i)\<rightharpoonup>c \<noteq> \<bottom>) then spfRestrict In Out\<cdot>(h (spfStep_h2 In (\<Squnion>i. Y i))) else spfLeast In Out) = (if In \<subseteq> dom (Y n) \<and> (\<forall>c\<in>In. (Y n\<rightharpoonup>c \<noteq> \<bottom>)) then spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y n))) else spfLeast In Out)"
          by (metis True \<open>In \<subseteq> dom (Y n) \<and> (\<forall>c\<in>In. Y n\<rightharpoonup>c \<noteq> \<bottom>)\<close> a1 fun_discr_u_spfStep_h2)
        then show ?thesis
          by(simp only: h1 h2)
      next
        case False
        then have "\<not>(In \<subseteq> dom (\<Squnion>i. Y i)) \<or> \<not>(\<forall>c\<in>In. (\<Squnion>i. Y i) \<rightharpoonup>c \<noteq> \<bottom>)"
          by simp
        have "\<And>i. dom (Y i) = dom (\<Squnion>i. Y i)"
          by(simp add:  part_dom_lub a1)
        then have c1:"\<And>i. \<not>(In \<subseteq> dom (\<Squnion>i. Y i)) \<Longrightarrow> \<not>(In \<subseteq> dom (Y i))"
          by simp
        have c2:"\<And>i. \<not>(\<forall>c\<in>In. (\<Squnion>i. Y i) \<rightharpoonup>c \<noteq> \<bottom>) \<Longrightarrow> \<not>(\<forall>c\<in>In. (Y i) \<rightharpoonup>c \<noteq> \<bottom>)"
          by (metis a1 is_ub_thelub minimal part_the_chain part_the_lub po_eq_conv)
        have "\<And> i. \<not>(In \<subseteq> dom (Y i)) \<or> \<not>(\<forall>c\<in>In. (Y i) \<rightharpoonup>c \<noteq> \<bottom>)"
          by(metis c1 c2 False)
        then have False2:"\<And>i. \<not>(In \<subseteq> dom (Y i) \<and> (\<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>))"
          by simp
        show ?thesis 
          by(simp add: False False2)
      qed
    qed
              
lemma spfStep_h1_mono[simp]:assumes "finite In" shows "monofun (\<lambda> h. (\<Lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In f)) else spfLeast In Out))"
by(rule monofunI, simp add: below_cfun_def below_fun_def, simp add: spfrestrict_below assms)
  
        
lemma spfStep_h1_cont[simp]:assumes "finite In" shows "cont (\<lambda> h. (\<Lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In f)) else spfLeast In Out))"
proof(rule Cont.contI2, simp add: spfStep_h1_mono assms)  
  have h0: " \<And>Y x. chain Y \<Longrightarrow> chain (\<lambda>i. Y i (spfStep_h2 In x))"
    by (simp add: ch2ch_fun)
  have h1:"\<And>Y x. chain Y \<Longrightarrow>
           chain (\<lambda>i. \<Lambda> f. if In \<subseteq> dom f \<and> (\<forall>c\<in>In. f\<rightharpoonup>c \<noteq> \<bottom>) then spfRestrict In Out\<cdot>(Y i (spfStep_h2 In f)) else spfLeast In Out) \<Longrightarrow>
           In \<subseteq> dom x \<Longrightarrow> \<forall>c\<in>In. x\<rightharpoonup>c \<noteq> \<bottom> \<Longrightarrow> spfRestrict In Out\<cdot>((\<Squnion>i. Y i) (spfStep_h2 In x)) \<sqsubseteq> (\<Squnion>i. spfRestrict In Out\<cdot>(Y i (spfStep_h2 In x)))"
    by(simp add: lub_fun h0 contlub_cfun_arg)
  show "\<And>Y. chain Y \<Longrightarrow>
         chain (\<lambda>i. \<Lambda> f. if In \<subseteq> dom f \<and> (\<forall>c\<in>In. f\<rightharpoonup>c \<noteq> \<bottom>) then spfRestrict In Out\<cdot>(Y i (spfStep_h2 In f)) else spfLeast In Out) \<Longrightarrow>
         (\<Lambda> f. if In \<subseteq> dom f \<and> (\<forall>c\<in>In. f\<rightharpoonup>c \<noteq> \<bottom>) then spfRestrict In Out\<cdot>((\<Squnion>i. Y i) (spfStep_h2 In f)) else spfLeast In Out) \<sqsubseteq>
         (\<Squnion>i. \<Lambda> f. if In \<subseteq> dom f \<and> (\<forall>c\<in>In. f\<rightharpoonup>c \<noteq> \<bottom>) then spfRestrict In Out\<cdot>(Y i (spfStep_h2 In f)) else spfLeast In Out)"
    by(simp add: below_cfun_def below_fun_def contlub_cfun_fun, auto, simp add: h1 assms)
qed
  
lemma[simp]:assumes"finite In" shows"spfDom\<cdot>(spfStep_h1 In Out\<cdot> h \<cdot> f) = In"
  by(simp add: spfStep_h1_def assms)
    

lemma spfStep_h1_ran[simp]:assumes "finite In" shows"spfRan\<cdot>(spfStep_h1 In Out\<cdot> h \<cdot> f) = Out"
  by(simp add: spfStep_h1_def assms)

lemma spfstep_h1_insert:assumes "finite In" shows"spfStep_h1 In Out\<cdot> h\<cdot>f = (if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In f)) else spfLeast In Out)"
  by(simp add:  spfStep_h1_def assms)    

(*spfStep_h1 mono cont end*)     
      
(* Returns the SPF that switches depending on input.  (spfStep_h1 In Out\<cdot>h)\<cdot>(sbHdElem\<cdot>sb) computes the SPF which has to be applied to the input sb*)
definition spfStep :: "channel set \<Rightarrow> channel set \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF) \<rightarrow> 'm SPF" where
"spfStep In Out \<equiv> \<Lambda> h. Abs_SPF (\<Lambda>  sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot>h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"


(* spfStep mono and cont*)


lemma spf_pref_eq_2: assumes "(f \<sqsubseteq> g)"
  shows "(f \<rightleftharpoons> a) \<sqsubseteq> (g \<rightleftharpoons> a)" 
  by (metis assms below_SPF_def below_option_def cfun_below_iff po_eq_conv)


lemma getSb_in_h:assumes "chain (Y::nat \<Rightarrow> 'a::message SPF)" shows "(\<Squnion>i. Rep_SPF (Y i))\<cdot> sb = (\<Squnion>i. (Rep_SPF (Y i) \<cdot> sb))"
  by(subst contlub_cfun_fun, simp_all add: assms)
    
lemma spf_sbDom: assumes "spfDom\<cdot>f = In" and "spfRan\<cdot>f = Out" and "sbDom\<cdot>sb= In" shows "sbDom\<cdot>(f \<rightleftharpoons> sb) = Out"
  by (simp add: assms(1) assms(2) assms(3))

(* Used for cont proofs*)
lemma getSb_in:assumes "chain Y" shows "(\<Squnion>i. Y i) \<rightleftharpoons> sb = (\<Squnion>i. Y i \<rightleftharpoons> sb)"
proof(cases "spfDom\<cdot>(\<Squnion>i. Y i) = sbDom\<cdot>sb")
  case True
  then have "\<forall>i. spfDom\<cdot>(Y i) = sbDom\<cdot>(sb)"
    using assms spfdom_eq_lub by auto
  have chain:"chain (\<lambda>i. Y i \<rightleftharpoons> sb)"
    by (simp add: op_the_chain assms)
  have "\<forall>i. Y i  \<rightleftharpoons> sb \<sqsubseteq> (\<Squnion>i. Y i \<rightleftharpoons> sb)"
    using below_lub chain by blast
  show ?thesis (*@jens.buerger*)
      sorry
next
  case False
  then have "\<forall>i. spfDom\<cdot>(Y i) \<noteq> sbDom\<cdot>(sb)"
    using assms spfdom_eq_lub by blast
  then show ?thesis 
    by (metis (mono_tags, lifting) spf_pref_eq_2 False assms lub_chain_maxelem option.exhaust_sel po_class.chainE spfdom2sbdom)
qed

(* spfStep inner SPF spf_well and cont*)

lemma spfStep_inSPF_mono[simp]:"monofun (\<lambda>b. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>b) \<rightleftharpoons> b)"
  apply(rule monofunI)
  by (metis below_SPF_def below_option_def below_refl monofun_cfun monofun_cfun_arg)
   
    
lemma spfStep_inSPF_cont[simp]:assumes "finite In" shows"cont (\<lambda> sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot> h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"  
proof(rule spf_contI2,rule Cont.contI2,auto)
  fix Y::"nat \<Rightarrow> 'a SB" and ia::nat
  assume chain:"chain Y"
  assume chain2:"chain (\<lambda>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> Y i)"
  have h1:"spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(\<Squnion>i. Y i)) = (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)))"
    by(simp add: chain contlub_cfun_fun contlub_cfun_arg)
  have h_true:"sbDom\<cdot>(\<Squnion>i. Y i) = In \<Longrightarrow> \<forall>i. sbDom\<cdot>(Y i) = In"
    by (simp add: chain sbChain_dom_eq2)
  have h_false:"sbDom\<cdot>(\<Squnion>i. Y i) \<noteq> In \<Longrightarrow> \<forall>i. sbDom\<cdot>(Y i) \<noteq> In"
    by (simp add: chain sbChain_dom_eq2)
  have "(\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i))) \<rightleftharpoons> (Y ia) = (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> (Y ia))"
    by (simp add:  getSb_in chain)
  then have "\<forall>ia. (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i))) \<rightleftharpoons> (Y ia) = (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> (Y ia))"
    by (simp add: chain getSb_in)
  then have h2_h:"(\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i))) \<rightleftharpoons> (\<Squnion>i. Y i) = (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> (\<Squnion>i. Y i))"
    by (simp add: chain getSb_in)
  have h2:"(\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> (\<Squnion>ib. Y ib)) = (\<Squnion>i. \<Squnion>ib. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> (Y ib))"
    by (simp add: chain contlub_cfun_arg op_the_lub)
  have "(\<Squnion>i ib. spfStep_h1 In Out\<cdot>h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> Y ib) \<sqsubseteq> (\<Squnion>i. spfStep_h1 In Out\<cdot>h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> Y i)" (* @jens.buerger*)
    sorry
  then have "(\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i))) \<rightleftharpoons> (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> Y i)"
    by(simp add: h2_h h2)
  then show "spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(\<Squnion>i. Y i)) \<rightleftharpoons> (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> Y i)"
    by(simp add: h1)
qed   
    
lemma spfStep_inSPF_well[simp]:assumes"finite In" shows "spf_well (\<Lambda>  sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot> h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)" 
  proof(rule spf_wellI)
    fix b::"'a SB"
    assume "b \<in> dom (Rep_cfun (\<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
    hence b_def:" b \<in> dom (\<lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)" 
      by (simp add: assms)
    thus "sbDom\<cdot>b = In"
    proof -
      show ?thesis
      by (meson b_def if_then_sbDom)
    qed
    thus "sbDom\<cdot>(the ((\<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)\<cdot>b)) = Out" 
      by (simp add: assms)
  next
    fix b2::"'a SB"
    assume "sbDom\<cdot>b2 = In"
    thus "b2 \<in> dom (Rep_cfun (\<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))" 
      by (simp add: domIff assms)
qed

(*spfStep outer cont*)
    
lemma spfStep_mono[simp]:assumes"finite In" shows"monofun (\<lambda> h. Abs_SPF (\<Lambda>  sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot> h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
proof(rule monofunI, simp add: below_SPF_def below_cfun_def assms)
  fix x y::"((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF)"
  assume a1:"x \<sqsubseteq> y"
  have h1:"(\<lambda>sb. spfStep_h1 In Out\<cdot>x\<cdot>(sbHdElem\<cdot>sb)) \<sqsubseteq> (\<lambda>sb. spfStep_h1 In Out\<cdot>y\<cdot>(sbHdElem\<cdot>sb))"
    apply(simp add: below_fun_def)
    using a1 cfun_below_iff monofun_cfun_arg by blast
  have h2:"(\<lambda>sb. spfStep_h1 In Out\<cdot>x\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb) \<sqsubseteq> (\<lambda>sb. spfStep_h1 In Out\<cdot>y\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
  proof(simp add: below_fun_def,auto)
    fix xa :: "'m SB"
    have "\<And>s. spfStep_h1 In Out\<cdot>x\<cdot>(sbHdElem\<cdot>s) \<sqsubseteq> spfStep_h1 In Out\<cdot>y\<cdot>(sbHdElem\<cdot>s)"
      using fun_below_iff h1 by fastforce
    then show "spfStep_h1 In Out\<cdot>x\<cdot>(sbHdElem\<cdot>xa) \<rightleftharpoons> xa \<sqsubseteq> spfStep_h1 In Out\<cdot>y\<cdot>(sbHdElem\<cdot>xa) \<rightleftharpoons> xa"
      by (metis (no_types) below_SPF_def below_option_def below_refl cfun_below_iff)
  qed
  show "(\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>x\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb) \<sqsubseteq> (\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>y\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
    using h2 by (simp add: below_option_def fun_below_iff)
qed

    
lemma spfStep_cont:assumes "finite In" shows"cont (\<lambda> h. Abs_SPF (\<Lambda>  sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot> h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
proof(rule Cont.contI2, simp add: assms)
  fix Y::"nat \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF)"
  assume a1: "chain Y"
  assume a2: "chain (\<lambda>i. Abs_CSPF (\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
  have chain_1:"chain (\<lambda>i. spfStep_h1 In Out\<cdot>(Y i))"
    using a1 by auto
  have chain_2:"\<And>x. chain (\<lambda>i. spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>x))"
    using chain_1 by auto
  have chain_3:"\<And>sb. chain (\<lambda>i. spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb))"
    by (simp add: chain_2)
  have chain_4:"\<And>sb. chain (\<lambda>i. spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
    by (simp add: chain_2 op_the_chain)
  have h:"\<forall>sb. spfStep_h1 In Out\<cdot>(\<Squnion>i. Y i)\<cdot>(sbHdElem\<cdot>sb) = (\<Squnion>i. (spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb)))"
  by(simp add: a1 chain_1 chain_2 contlub_cfun_arg contlub_cfun_fun contlub_lambda)  
  have h0_1:"\<forall>sb.  spfStep_h1 In Out\<cdot>(\<Squnion>i. Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb = (\<Squnion>i. (spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
    apply(subst contlub_cfun_arg, simp add: a1)
    apply(subst contlub_cfun_fun, simp add: chain_1)
    by(simp add: getSb_in chain_3)
  have h0_2:"\<forall>sb. ((sbDom\<cdot>sb = In)\<leadsto>\<Squnion>i. spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb) = (\<Squnion>i. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
  proof(auto)
    fix sb::"'m SB"
    assume a11: "In = sbDom\<cdot>sb"  
    have h0_21:"((sbDom\<cdot>sb = In)\<leadsto>(\<Squnion>i. spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)) = (\<Squnion>i. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
    by(simp add: some_lub_chain_eq chain_4)
      show"Some (\<Squnion>i. (spfStep_h1 (sbDom\<cdot>sb) Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb)) \<rightleftharpoons> sb) = (\<Squnion>i. Some ((spfStep_h1 (sbDom\<cdot>sb) Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb)) \<rightleftharpoons> sb))"
      using a11 h0_21 by auto
  qed 
  have chain_h0:"chain (\<lambda>i. \<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
  proof(rule chainI)
    fix i::nat
    show "(\<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb) \<sqsubseteq> (\<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y (Suc i))\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
      apply(simp add: below_cfun_def assms)
      by (smt below_option_def cfun_below_iff chain_1 fun_belowI po_class.chain_def some_below spf_pref_eq_2)
  qed    
  have cont_lub2:"cont (\<lambda>x. \<Squnion>i. (sbDom\<cdot>x = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>x) \<rightleftharpoons> x)"
    apply(rule cont2cont_lub,simp_all add: assms)
    apply(rule chainI)
    by (smt below_option_def cfun_below_iff chain_1 fun_belowI po_class.chain_def some_below spf_pref_eq_2)
  have "\<And>b.  sbDom\<cdot>b= In \<Longrightarrow> \<forall>i . sbDom\<cdot>(spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>b) \<rightleftharpoons> b) = Out"
    using assms by auto
  then have spf_well_h:"\<And>b. sbDom\<cdot>b= In \<Longrightarrow> sbDom\<cdot>(\<Squnion>i. (spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>b) \<rightleftharpoons> b)) = Out"
    by (metis (no_types, lifting) chain_4 sbChain_dom_eq2)
  have spf_well2:"spf_well (\<Lambda> x. \<Squnion>i. (sbDom\<cdot>x = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>x) \<rightleftharpoons> x)"
    proof(rule spf_wellI)
    fix b:: "'m SB"    
    assume "b \<in> dom (Rep_cfun (\<Lambda> x. \<Squnion>i. (sbDom\<cdot>x = In) \<leadsto> spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>x) \<rightleftharpoons> x))"
    hence b_def:" b \<in> dom (\<lambda> x. \<Squnion>i. (sbDom\<cdot>x = In) \<leadsto> spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>x) \<rightleftharpoons> x)"
      using cont_lub2 by auto
    thus "sbDom\<cdot>b = In"
      by (metis (no_types, lifting) domIff h0_2)
    thus "sbDom\<cdot>Rep_cfun (\<Lambda> x. \<Squnion>i. (sbDom\<cdot>x = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>x) \<rightleftharpoons> x)\<rightharpoonup>b = Out"
      apply(subst beta_cfun,subst cont_lub2, simp,simp)
      by (smt \<open>sbDom\<cdot>b = In\<close> \<open>\<And>b. sbDom\<cdot>b = In \<Longrightarrow> sbDom\<cdot> (\<Squnion>i. spfStep_h1 In Out\<cdot>(Y i)\<cdot> (sbHdElem\<cdot>b) \<rightleftharpoons> b) = Out\<close> h0_2 lub_eq option.sel)
  next
    fix b2::"'m SB"
    assume "sbDom\<cdot>b2 = In"
    thus "b2 \<in> dom (Rep_cfun (\<Lambda> x. \<Squnion>i. (sbDom\<cdot>x = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>x) \<rightleftharpoons> x))"
    proof -
      show ?thesis
        by (metis (lifting) Abs_cfun_inverse2 \<open>sbDom\<cdot>b2 = In\<close> cont_lub2 domIff h0_2 option.distinct(1))
    qed
  qed
  have h0:"Rep_CSPF (\<Squnion>i. Abs_CSPF (\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)) = (\<Squnion>i. (\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
   apply(subst lub_SPF)
   apply (simp add: a2)
   apply(subst lub_cfun)
   using a2 rep_spf_chain apply blast
   apply(subst rep_abs_cspf)
   apply(subst rep_abs_cspf, simp add: assms, simp add: assms,simp only: spf_well2 cont_lub2)+
   apply(subst rep_abs_cspf, simp add: assms, simp add: assms)
   apply(subst contlub_lambda,simp_all)
   apply(rule chainI)
   by (smt below_option_def cfun_below_iff chain_1 fun_belowI po_class.chain_def some_below spf_pref_eq_2)
  have h1:"(\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(\<Squnion>i. Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb) \<sqsubseteq> Rep_CSPF (\<Squnion>i. Abs_CSPF (\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
  proof(simp add: h0, subst h0_1, rule fun_belowI)
    fix x::"'m SB"
    have chain_sb:"chain (\<lambda>i.(\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
    proof(rule chainI)
      fix i::nat
      show "(\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb) \<sqsubseteq> (\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y (Suc i))\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
        by (smt below_option_def cfun_below_iff chain_1 fun_belowI po_class.chain_def some_below spf_pref_eq_2)
    qed 
    show"(sbDom\<cdot>x = In)\<leadsto>\<Squnion>i. spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>x) \<rightleftharpoons> x \<sqsubseteq> (\<Squnion>i. (\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)) x"
    proof(cases "(sbDom\<cdot>x = In)")
      case True
      then show ?thesis
        by (smt chain_4 chain_sb lub_eq lub_fun po_eq_conv some_lub_chain_eq3)
    next
      case False
      then have "(\<Squnion>i. (\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)) x = None"
        by (simp add: chain_sb False lub_fun)
      then show ?thesis
        by (simp add: False)
    qed
  qed
  show "Abs_CSPF (\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(\<Squnion>i. Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb) \<sqsubseteq> (\<Squnion>i. Abs_CSPF (\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
    by(simp add: below_SPF_def below_cfun_def h1 assms)
qed 
  
lemma spfstep_insert: assumes "finite In" shows "spfStep In Out\<cdot>h= Abs_SPF (\<Lambda>  sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot> h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
  by(simp add: spfStep_cont spfStep_def assms)

lemma spfstep_dom [simp]:assumes "finite cIn" shows"spfDom\<cdot>(spfStep cIn cOut\<cdot>f) = cIn"
  by(simp add: spfstep_insert spfDomAbs assms)

lemma spfstep_ran [simp]:assumes "finite cIn" shows"spfRan\<cdot>(spfStep cIn cOut\<cdot>f) = cOut"
  apply(simp add: spfstep_insert assms)
  apply(unfold spfran_least,simp add: assms)
  by (simp add: assms spfDomAbs)
   
lemma sbHdElem_dom[simp]:"dom (sbHdElem\<cdot>sb) = sbDom\<cdot>sb"
  by(simp add: sbHdElem_def sbHdElem_cont)

lemma sbHdElem_channel: assumes "sbDom\<cdot>sb = In"  and "c \<in> In" and "sb . c \<noteq> \<bottom>" shows "sbHdElem\<cdot>sb\<rightharpoonup>c \<noteq> \<bottom>"
    by(simp add: sbHdElem_def sbHdElem_cont assms)    
    
lemma stepstep_step: assumes "sbDom\<cdot>sb = In" and "\<forall>c\<in>In. sb . c \<noteq> \<bottom>" and "finite In" shows "spfStep In Out\<cdot>f\<rightleftharpoons>sb = (f ((inv convDiscrUp)(sbHdElem\<cdot>sb)))\<rightleftharpoons>sb"
proof(simp add: spfstep_insert assms)
  fix c::channel
  have "\<forall>c\<in>In. sb . c \<noteq> \<bottom> \<longrightarrow> sbHdElem\<cdot>sb\<rightharpoonup>c \<noteq> \<bottom>"
  proof auto
    fix x::channel
    assume a1:"x \<in> In"
    assume a2:"sb . x \<noteq> \<bottom>"
    have " sbHdElem\<cdot>sb\<rightharpoonup>x \<noteq> \<bottom>"
      by(rule sbHdElem_channel, simp_all add: a1 assms, simp add: a1)
    then show "sbHdElem\<cdot>sb\<rightharpoonup>x = \<bottom> \<Longrightarrow> False"
      by auto
  qed
  then have h1_h:"In \<subseteq> dom (sbHdElem\<cdot>sb) \<and> (\<forall>c\<in>In. sbHdElem\<cdot>sb\<rightharpoonup>c \<noteq> \<bottom>)"
    by(simp add: assms)
  have "spfDom\<cdot>(f (spfStep_h2 In (sbHdElem\<cdot>sb))) = In \<and> spfRan\<cdot>(f (spfStep_h2 In (sbHdElem\<cdot>sb))) = Out" (* in Lemma assumptions for f*)
    sorry
  then have h1:"spfStep_h1 In Out\<cdot>f\<cdot>(sbHdElem\<cdot>sb) = (f (spfStep_h2 In (sbHdElem\<cdot>sb)))"
    by(simp add: spfstep_h1_insert h1_h assms)
  have h2:"spfStep_h2 In (sbHdElem\<cdot>sb) = inv convDiscrUp (sbHdElem\<cdot>sb)"
    apply(simp add: spfStep_h2_def, unfold convDiscrUp_def inv_def updis_exists) (*ToDo*)
    sorry
  then show "spfStep_h1 In Out\<cdot>f\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb = f (inv convDiscrUp (sbHdElem\<cdot>sb)) \<rightleftharpoons> sb"
    by(simp add: h1)
qed
    
end