(*  Title:        SpfStep
    Author:       Hendrik Kausch
    e-mail:       hendrik.kausch@rwth-aachen.de
*)

theory SpfStep
imports SPF "../inc/If_Else_Continuity"
begin
default_sort type

(* updis bijectiv *)
thm inv_def
  
(*Just used to transform the function*)  
definition spfStep_h2::" channel set \<Rightarrow> (channel\<rightharpoonup>'m::message discr\<^sub>\<bottom>) \<Rightarrow> (channel\<rightharpoonup>'m)" where
"spfStep_h2 In = (\<lambda>f. (\<lambda>c. (c \<in> In) \<leadsto> (inv updis f \<rightharpoonup> c)))"

(* If the conditions are correct then we use imput h to compute a SPF. After that check if the SPF has the right dom and ran*)
definition spfStep_h1::"channel set \<Rightarrow> channel set \<Rightarrow>((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF) \<rightarrow>((channel\<rightharpoonup>'m discr\<^sub>\<bottom>)\<rightarrow> 'm SPF)" where
"spfStep_h1 In Out= (\<Lambda> h. (\<Lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then ufRestrict In Out\<cdot>(h (spfStep_h2 In f)) else ufLeast In Out))"

lemma[simp]: "ufDom\<cdot>((\<lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then ufRestrict In Out\<cdot>(h (spfStep_h2 In f)) else ufLeast In Out)f) = In"
  by simp
    
lemma[simp]: "ufRan\<cdot>((\<lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then ufRestrict In Out\<cdot>(h (spfStep_h2 In f)) else ufLeast In Out)f) = Out"
  by simp

lemma ufRestrict_apply2[simp]: assumes "ufDom\<cdot>f \<noteq> In \<or> ufRan\<cdot>f \<noteq> Out" shows "ufRestrict In Out\<cdot>f = ufLeast In Out"
  apply(simp add: ufRestrict_def)
  using assms by blast

lemma assumes "F \<sqsubseteq> G" shows "ufRestrict In Out\<cdot>F = F \<Longrightarrow> ufRestrict In Out\<cdot>G = G"
  by (metis assms ufRestrict_apply ufRestrict_dom ufRestrict_ran ufdom_below_eq ufran_below)

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

lemma spfrestrict_below: assumes"x\<sqsubseteq>y" shows "ufRestrict In Out\<cdot>x \<sqsubseteq> ufRestrict In Out\<cdot>y"
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
lemma[simp]:"monofun (\<lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then ufRestrict In Out\<cdot>(h (spfStep_h2 In f)) else ufLeast In Out)"
  proof(rule monofunI)  
    fix x and y::"(channel\<rightharpoonup>'a::message discr\<^sub>\<bottom>)"
    assume a1:"x \<sqsubseteq> y"
    show "(if In \<subseteq> dom x \<and> (\<forall>c\<in>In. x\<rightharpoonup>c \<noteq> \<bottom>) then ufRestrict In Out\<cdot>(h (spfStep_h2 In x)) else ufLeast In Out) \<sqsubseteq>
           (if In \<subseteq> dom y \<and> (\<forall>c\<in>In. y\<rightharpoonup>c \<noteq> \<bottom>) then ufRestrict In Out\<cdot>(h (spfStep_h2 In y)) else ufLeast In Out)"
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
        show "ufRestrict In Out\<cdot>(h (spfStep_h2 In x)) \<sqsubseteq> ufRestrict In Out\<cdot>(h (spfStep_h2 In y))"
          proof(cases "ufDom\<cdot>(h (spfStep_h2 In x)) = In \<and> ufRan\<cdot>(h (spfStep_h2 In x)) = Out")
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
            have h11:"ufRestrict In Out\<cdot>(h (spfStep_h2 In x)) = ufLeast In Out"
              using False by auto
            then show ?thesis
              proof(cases "ufDom\<cdot>(h (spfStep_h2 In y)) = In \<and> ufRan\<cdot>(h (spfStep_h2 In y)) = Out")
                case True
                then show ?thesis
                  by (simp add: h11)
              next
                case False
                have h12:"ufRestrict In Out\<cdot>(h (spfStep_h2 In y)) = ufLeast In Out"
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
    
lemma[simp]:assumes "finite In" shows "cont(\<lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then ufRestrict In Out\<cdot>(h (spfStep_h2 In f)) else ufLeast In Out) "
  (*apply(rule equalizing_pred_cont)
  apply(simp_all add: cont_at_def,auto)*)
  proof(rule Cont.contI2,simp)    
    fix Y::"nat \<Rightarrow> (channel\<rightharpoonup>'a::message discr\<^sub>\<bottom>)"
    assume a1:"chain Y"
    assume a2:"chain (\<lambda>i. if (In \<subseteq> dom (Y i) \<and> (\<forall>c\<in>In. ((Y i)\<rightharpoonup>c \<noteq> \<bottom>))) then ufRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else ufLeast In Out)"
    show "(if In \<subseteq> dom (\<Squnion>i. Y i) \<and> (\<forall>c\<in>In. (\<Squnion>i. Y i)\<rightharpoonup>c \<noteq> \<bottom>) then ufRestrict In Out\<cdot>(h (spfStep_h2 In (\<Squnion>i. Y i))) else ufLeast In Out) \<sqsubseteq>
         (\<Squnion>i. if In \<subseteq> dom (Y i) \<and> (\<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>) then ufRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else ufLeast In Out)"
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
        then have "(\<lambda>i. if (In \<subseteq> dom (Y i) \<and> (\<forall>c\<in>In. ((Y i)\<rightharpoonup>c \<noteq> \<bottom>))) then ufRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else ufLeast In Out) n = ufRestrict In Out\<cdot>(h (spfStep_h2 In (Y n)))"
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
        have chain_eq_second_gen:"\<forall>i\<ge>n. (\<lambda>i. if (In \<subseteq> dom (Y i) \<and> (\<forall>c\<in>In. ((Y i)\<rightharpoonup>c \<noteq> \<bottom>))) then ufRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else ufLeast In Out) i = ufRestrict In Out\<cdot>(h (spfStep_h2 In (Y i)))" 
          by (simp add: \<open>\<forall>i. In \<subseteq> dom (Y i)\<close> \<open>\<forall>i\<ge>n. \<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>\<close>)
        have chain_second_part:"chain (\<lambda>i. if n \<le> i then ufRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else ufLeast In Out)"
        proof(rule chainI)
          fix i::nat
          show "(if n \<le> i then ufRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else ufLeast In Out) \<sqsubseteq> (if n \<le> Suc i then ufRestrict In Out\<cdot>(h (spfStep_h2 In (Y (Suc i)))) else ufLeast In Out)"
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
        have h1:"(if In \<subseteq> dom (Y n) \<and> (\<forall>c\<in>In. (Y n\<rightharpoonup>c \<noteq> \<bottom>)) then ufRestrict In Out\<cdot>(h (spfStep_h2 In (Y n))) else ufLeast In Out) \<sqsubseteq>(\<Squnion>i. if In \<subseteq> dom (Y i) \<and> (\<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>) then ufRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else ufLeast In Out)"
          using a2 below_lub by blast
        have h2:"(if In \<subseteq> dom (\<Squnion>i. Y i) \<and> (\<forall>c\<in>In. (\<Squnion>i. Y i)\<rightharpoonup>c \<noteq> \<bottom>) then ufRestrict In Out\<cdot>(h (spfStep_h2 In (\<Squnion>i. Y i))) else ufLeast In Out) = (if In \<subseteq> dom (Y n) \<and> (\<forall>c\<in>In. (Y n\<rightharpoonup>c \<noteq> \<bottom>)) then ufRestrict In Out\<cdot>(h (spfStep_h2 In (Y n))) else ufLeast In Out)"
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
              
lemma spfStep_h1_mono[simp]:assumes "finite In" shows "monofun (\<lambda> h. (\<Lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then ufRestrict In Out\<cdot>(h (spfStep_h2 In f)) else ufLeast In Out))"
by(rule monofunI, simp add: below_cfun_def below_fun_def, simp add: spfrestrict_below assms)
  
        
lemma spfStep_h1_cont[simp]:assumes "finite In" shows "cont (\<lambda> h. (\<Lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then ufRestrict In Out\<cdot>(h (spfStep_h2 In f)) else ufLeast In Out))"
proof(rule Cont.contI2, simp add: spfStep_h1_mono assms)  
  have h0: " \<And>Y x. chain Y \<Longrightarrow> chain (\<lambda>i. Y i (spfStep_h2 In x))"
    by (simp add: ch2ch_fun)
  have h1:"\<And>Y x. chain Y \<Longrightarrow>
           chain (\<lambda>i. \<Lambda> f. if In \<subseteq> dom f \<and> (\<forall>c\<in>In. f\<rightharpoonup>c \<noteq> \<bottom>) then ufRestrict In Out\<cdot>(Y i (spfStep_h2 In f)) else ufLeast In Out) \<Longrightarrow>
           In \<subseteq> dom x \<Longrightarrow> \<forall>c\<in>In. x\<rightharpoonup>c \<noteq> \<bottom> \<Longrightarrow> ufRestrict In Out\<cdot>((\<Squnion>i. Y i) (spfStep_h2 In x)) \<sqsubseteq> (\<Squnion>i. ufRestrict In Out\<cdot>(Y i (spfStep_h2 In x)))"
    by(simp add: lub_fun h0 contlub_cfun_arg)
  show "\<And>Y. chain Y \<Longrightarrow>
         chain (\<lambda>i. \<Lambda> f. if In \<subseteq> dom f \<and> (\<forall>c\<in>In. f\<rightharpoonup>c \<noteq> \<bottom>) then ufRestrict In Out\<cdot>(Y i (spfStep_h2 In f)) else ufLeast In Out) \<Longrightarrow>
         (\<Lambda> f. if In \<subseteq> dom f \<and> (\<forall>c\<in>In. f\<rightharpoonup>c \<noteq> \<bottom>) then ufRestrict In Out\<cdot>((\<Squnion>i. Y i) (spfStep_h2 In f)) else ufLeast In Out) \<sqsubseteq>
         (\<Squnion>i. \<Lambda> f. if In \<subseteq> dom f \<and> (\<forall>c\<in>In. f\<rightharpoonup>c \<noteq> \<bottom>) then ufRestrict In Out\<cdot>(Y i (spfStep_h2 In f)) else ufLeast In Out)"
    by(simp add: below_cfun_def below_fun_def contlub_cfun_fun, auto, simp add: h1 assms)
qed
  
lemma[simp]:assumes"finite In" shows"ufDom\<cdot>(spfStep_h1 In Out\<cdot> h \<cdot> f) = In"
  by(simp add: spfStep_h1_def assms)
    

lemma spfStep_h1_ran[simp]:assumes "finite In" shows"ufRan\<cdot>(spfStep_h1 In Out\<cdot> h \<cdot> f) = Out"
  by(simp add: spfStep_h1_def assms)

lemma ufLeast_out_ubDom:assumes "ubDom\<cdot>sb = In" shows "ubDom\<cdot>(ufLeast In Out \<rightleftharpoons> sb) = Out"
  apply(simp add: ufLeast_def assms)
  by (metis assms ubDom_ubundle_def ubdom_least_cs)
    
lemma spfStep_h1_out_dom[simp]:assumes "finite In" and "ubDom\<cdot>sb = In" shows "ubDom\<cdot>(spfStep_h1 In Out\<cdot> h \<cdot> f \<rightleftharpoons> sb) = Out"
  apply(simp add: spfStep_h1_def assms ufLeast_out_ubDom)
  by (metis assms(2) ubDom_ubundle_def ufRestrict_dom ufRestrict_ran ufran_2_ubdom2)

lemma spfstep_h1_insert:assumes "finite In" shows"spfStep_h1 In Out\<cdot> h\<cdot>f = (if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then ufRestrict In Out\<cdot>(h (spfStep_h2 In f)) else ufLeast In Out)"
  by(simp add:  spfStep_h1_def assms)    

(*spfStep_h1 mono cont end*)     
      
(* Returns the SPF that switches depending on input.  (spfStep_h1 In Out\<cdot>h)\<cdot>(sbHdElem\<cdot>sb) computes the SPF which has to be applied to the input sb*)
definition spfStep :: "channel set \<Rightarrow> channel set \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF) \<rightarrow> 'm SPF" where
"spfStep In Out \<equiv> \<Lambda> h. Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot>h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"


(* spfStep mono and cont*)


lemma spf_pref_eq_2: assumes "(f \<sqsubseteq> g)"
  shows "(f \<rightleftharpoons> a) \<sqsubseteq> (g \<rightleftharpoons> a)" 
  by (metis assms below_ufun_def below_option_def cfun_below_iff po_eq_conv)


lemma getSb_in_h:assumes "chain (Y::nat \<Rightarrow> 'a::message SPF)" shows "(\<Squnion>i. Rep_ufun (Y i))\<cdot> sb = (\<Squnion>i. (Rep_ufun (Y i) \<cdot> sb))"
  by(subst contlub_cfun_fun, simp_all add: assms)
    
lemma spf_ubDom: assumes "ufDom\<cdot>f = In" and "ufRan\<cdot>f = Out" and "ubDom\<cdot>sb= In" shows "ubDom\<cdot>(f \<rightleftharpoons> sb) = Out"
  by (metis assms(1) assms(2) assms(3) ubDom_ubundle_def ufran_2_ubdom2)

(* spfStep inner SPF spf_well and cont*)

lemma spfStep_inSPF_mono[simp]:"monofun (\<lambda>b. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>b) \<rightleftharpoons> b)"
  apply(rule monofunI)
  by (metis below_ufun_def below_option_def below_refl monofun_cfun monofun_cfun_arg)
   
lemma spf_contI2 [simp]: assumes "cont g"
  shows "cont (\<lambda>b. (ubDom\<cdot>b = In)\<leadsto>g b)"
  by (metis (no_types) assms if_then_cont ubDom_ubundle_def)
    
lemma spfStep_inSPF_cont[simp]:assumes "finite In" shows"cont (\<lambda> sb.  (ubDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot> h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"  
proof(rule spf_contI2,rule Cont.contI2,auto)
  fix Y::"nat \<Rightarrow> 'a SB" and ia::nat
  assume chain:"chain Y"
  assume chain2:"chain (\<lambda>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> Y i)"
  have h1:"spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(\<Squnion>i. Y i)) = (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)))"
    by(simp add: chain contlub_cfun_fun contlub_cfun_arg)
  have h_true:"ubDom\<cdot>(\<Squnion>i. Y i) = In \<Longrightarrow> \<forall>i. ubDom\<cdot>(Y i) = In"
    by (simp add: chain)
  have h_false:"ubDom\<cdot>(\<Squnion>i. Y i) \<noteq> In \<Longrightarrow> \<forall>i. ubDom\<cdot>(Y i) \<noteq> In"
    by (simp add: chain)
  have "(\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i))) \<rightleftharpoons> (Y ia) = (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> (Y ia))"
    by (simp add: spfapply_lub chain)
  then have "\<forall>ia. (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i))) \<rightleftharpoons> (Y ia) = (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> (Y ia))"
    by (simp add: chain spfapply_lub)
  then have h2_h:"(\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i))) \<rightleftharpoons> (\<Squnion>i. Y i) = (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> (\<Squnion>i. Y i))"
    by (simp add: chain spfapply_lub)
  have h2:"(\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> (\<Squnion>ib. Y ib)) = (\<Squnion>i. \<Squnion>ib. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> (Y ib))"
    by (simp add: chain contlub_cfun_arg op_the_lub)
  have "(\<Squnion>i ib. spfStep_h1 In Out\<cdot>h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> Y ib) = (\<Squnion>i. spfStep_h1 In Out\<cdot>h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> Y i)" (* @jens.buerger*)
    apply(rule diag_lub)
    apply (meson chain monofun_cfun_arg po_class.chain_def spf_pref_eq_2)
    using ch2ch_Rep_cfunR chain op_the_chain by auto
  then have "(\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i))) \<rightleftharpoons> (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> Y i)"
    by(simp add: h2_h h2)
  then show "spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(\<Squnion>i. Y i)) \<rightleftharpoons> (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> Y i)"
    by(simp add: h1)
qed   
    
lemma spfStep_inSPF_well[simp]:assumes"finite In" shows "ufWell (\<Lambda>  sb.  (ubDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot> h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)" 
  proof(rule ufwellI)
    fix b::"'a SB"
    assume "b \<in> dom (Rep_cfun (\<Lambda> sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
    hence b_def:" b \<in> dom (\<lambda> sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)" 
      by (simp add: assms)
    thus "ubDom\<cdot>b = In"
    proof -
      show ?thesis
        by (smt b_def domIff)
    qed
    thus "ubDom\<cdot>(the ((\<Lambda> sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)\<cdot>b)) = Out" 
      using assms by simp
      (* by (simp add: assms) *)
  next
    fix b2::"'a SB"
    assume "ubDom\<cdot>b2 = In"
    thus "b2 \<in> dom (Rep_cfun (\<Lambda> sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))" 
      by (simp add: domIff assms)
qed

(*spfStep outer cont*)
    
lemma spfStep_mono[simp]:assumes"finite In" shows"monofun (\<lambda> h. Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot> h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
proof(rule monofunI, simp add: below_ufun_def below_cfun_def assms)
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
      by (metis (no_types) below_ufun_def below_option_def below_refl cfun_below_iff)
  qed
  show "(\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>x\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb) \<sqsubseteq> (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>y\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
    using h2 by (simp add: below_option_def fun_below_iff)
qed

    
lemma spfStep_cont:assumes "finite In" shows"cont (\<lambda> h. Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot> h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
proof(rule Cont.contI2, simp add: assms)
  fix Y::"nat \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF)"
  assume a1: "chain Y"
  assume a2: "chain (\<lambda>i. Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
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
    by(simp add: spfapply_lub chain_3)
  have h0_2:"\<forall>sb. ((ubDom\<cdot>sb = In)\<leadsto>\<Squnion>i. spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb) = (\<Squnion>i. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
  proof(auto)
    fix sb::"'m SB"
    assume a11: "In = ubDom\<cdot>sb"  
    have h0_21:"((ubDom\<cdot>sb = In)\<leadsto>(\<Squnion>i. spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)) = (\<Squnion>i. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
    by(simp add: some_lub_chain_eq chain_4)
      show"Some (\<Squnion>i. (spfStep_h1 (ubDom\<cdot>sb) Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb)) \<rightleftharpoons> sb) = (\<Squnion>i. Some ((spfStep_h1 (ubDom\<cdot>sb) Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb)) \<rightleftharpoons> sb))"
      using a11 h0_21 by auto
  qed 
  have chain_h0:"chain (\<lambda>i. \<Lambda> sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
  proof(rule chainI)
    fix i::nat
    show "(\<Lambda> sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb) \<sqsubseteq> (\<Lambda> sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y (Suc i))\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
      apply(simp add: below_cfun_def assms)
      by (smt below_option_def cfun_below_iff chain_1 fun_belowI po_class.chain_def some_below spf_pref_eq_2)
  qed    
  have cont_lub2:"cont (\<lambda>x. \<Squnion>i. (ubDom\<cdot>x = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>x) \<rightleftharpoons> x)"
    apply(rule cont2cont_lub,simp_all add: assms)
    apply(rule chainI)
    by (smt below_option_def cfun_below_iff chain_1 fun_belowI po_class.chain_def some_below spf_pref_eq_2)
  have "\<And>b.  ubDom\<cdot>b= In \<Longrightarrow> \<forall>i . ubDom\<cdot>(spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>b) \<rightleftharpoons> b) = Out"
    using assms by simp
  then have spf_well_h:"\<And>b. ubDom\<cdot>b= In \<Longrightarrow> ubDom\<cdot>(\<Squnion>i. (spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>b) \<rightleftharpoons> b)) = Out"
    by (metis (no_types, lifting) chain_4 lub_eq ubdom_chain_eq2)
  have spf_well2:"ufWell (\<Lambda> x. \<Squnion>i. (ubDom\<cdot>x = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>x) \<rightleftharpoons> x)"
    proof(rule ufwellI)
    fix b:: "'m SB"    
    assume "b \<in> dom (Rep_cfun (\<Lambda> x. \<Squnion>i. (ubDom\<cdot>x = In) \<leadsto> spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>x) \<rightleftharpoons> x))"
    hence b_def:" b \<in> dom (\<lambda> x. \<Squnion>i. (ubDom\<cdot>x = In) \<leadsto> spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>x) \<rightleftharpoons> x)"
      using cont_lub2 by auto
    thus "ubDom\<cdot>b = In"
      by (metis (no_types, lifting) domIff h0_2)
    thus "ubDom\<cdot>Rep_cfun (\<Lambda> x. \<Squnion>i. (ubDom\<cdot>x = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>x) \<rightleftharpoons> x)\<rightharpoonup>b = Out"
      apply(subst beta_cfun,subst cont_lub2, simp,simp)
      by (smt \<open>ubDom\<cdot>b = In\<close> \<open>\<And>b. ubDom\<cdot>b = In \<Longrightarrow> ubDom\<cdot> (\<Squnion>i. spfStep_h1 In Out\<cdot>(Y i)\<cdot> (sbHdElem\<cdot>b) \<rightleftharpoons> b) = Out\<close> h0_2 lub_eq option.sel)
  next
    fix b2::"'m SB"
    assume "ubDom\<cdot>b2 = In"
    thus "b2 \<in> dom (Rep_cfun (\<Lambda> x. \<Squnion>i. (ubDom\<cdot>x = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>x) \<rightleftharpoons> x))"
    proof -
      show ?thesis
        by (metis (lifting) Abs_cfun_inverse2 \<open>ubDom\<cdot>b2 = In\<close> cont_lub2 domIff h0_2 option.distinct(1))
    qed
  qed
  have h0:"Rep_cufun (\<Squnion>i. Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)) = (\<Squnion>i. (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
   apply(subst lub_ufun)
   apply (simp add: a2)
   apply(subst lub_cfun)
   using a2 rep_ufun_chain apply blast
   apply(subst rep_abs_cufun)
   apply(subst rep_abs_cufun, simp add: assms, simp add: assms,simp only: spf_well2 cont_lub2)+
   apply(subst rep_abs_cufun, simp add: assms, simp add: assms)
   apply(subst contlub_lambda,simp_all)
   apply(rule chainI)
   by (smt below_option_def cfun_below_iff chain_1 fun_belowI po_class.chain_def some_below spf_pref_eq_2)
  have h1:"(\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(\<Squnion>i. Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb) \<sqsubseteq> Rep_cufun (\<Squnion>i. Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
  proof(simp add: h0, subst h0_1, rule fun_belowI)
    fix x::"'m SB"
    have chain_sb:"chain (\<lambda>i.(\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
    proof(rule chainI)
      fix i::nat
      show "(\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb) \<sqsubseteq> (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y (Suc i))\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
        by (smt below_option_def cfun_below_iff chain_1 fun_belowI po_class.chain_def some_below spf_pref_eq_2)
    qed 
    show"(ubDom\<cdot>x = In)\<leadsto>\<Squnion>i. spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>x) \<rightleftharpoons> x \<sqsubseteq> (\<Squnion>i. (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)) x"
    proof(cases "(ubDom\<cdot>x = In)")
      case True
      then show ?thesis
        by (smt chain_4 chain_sb lub_eq lub_fun po_eq_conv some_lub_chain_eq3)
    next
      case False
      then have "(\<Squnion>i. (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)) x = None"
        by (simp add: chain_sb False lub_fun)
      then show ?thesis
        by (simp add: False)
    qed
  qed
  show "Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(\<Squnion>i. Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb) \<sqsubseteq> (\<Squnion>i. Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
    by(simp add: below_ufun_def below_cfun_def h1 assms)
qed 
  
lemma spfstep_insert: assumes "finite In" shows "spfStep In Out\<cdot>h= Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot> h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
  by(simp add: spfStep_cont spfStep_def assms)

lemma spfDomAbs: assumes "cont (\<lambda> x. (ubDom\<cdot>x = cs ) \<leadsto> f(x))" 
                     and "ufWell (\<Lambda> x. (ubDom\<cdot>x = cs ) \<leadsto> f(x))"
                   shows "ufDom\<cdot>(Abs_cufun (\<lambda> x. (ubDom\<cdot>x = cs ) \<leadsto> f(x))) = cs"
apply(simp add: ufDom_def)
apply(simp_all add: assms)
  by (smt Abs_cfun_inverse2 assms(1) assms(2) domIff rep_abs_cufun2 tfl_some ubDom_ubundle_def ufunLeastIDom)

lemma spfstep_dom [simp]:assumes "finite cIn" shows"ufDom\<cdot>(spfStep cIn cOut\<cdot>f) = cIn"
  by(simp add: spfstep_insert spfDomAbs assms)

lemma ubDom_ubLeast[simp]:"ubDom\<cdot>(ubLeast cIn) = cIn"
  by simp
    
lemma spfstep_ran [simp]:assumes "finite cIn" shows"ufRan\<cdot>(spfStep cIn cOut\<cdot>f) = cOut"
  apply(simp add: spfstep_insert assms)
  apply(unfold ufran_least,simp add: assms)
  apply (simp add: assms spfDomAbs)
  by (metis assms spfStep_h1_out_dom ubDom_ubundle_def ubdom_least_cs)

lemma sbHdElem_dom[simp]:"dom (sbHdElem\<cdot>sb) = ubDom\<cdot>sb"
  by(simp add: sbHdElem_def sbHdElem_cont)

lemma sbHdElem_channel: assumes "ubDom\<cdot>sb = In"  and "c \<in> In" and "sb . c \<noteq> \<bottom>" shows "sbHdElem\<cdot>sb\<rightharpoonup>c \<noteq> \<bottom>"
    by(simp add: sbHdElem_def sbHdElem_cont assms)    
    
lemma stepstep_step: assumes "ubDom\<cdot>sb = In" and "\<forall>c\<in>In. sb . c \<noteq> \<bottom>" and "finite In" shows "spfStep In Out\<cdot>f\<rightleftharpoons>sb = (f ((inv convDiscrUp)(sbHdElem\<cdot>sb)))\<rightleftharpoons>sb"
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
  have "ufDom\<cdot>(f (spfStep_h2 In (sbHdElem\<cdot>sb))) = In \<and> ufRan\<cdot>(f (spfStep_h2 In (sbHdElem\<cdot>sb))) = Out" (* in Lemma assumptions for f*)
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