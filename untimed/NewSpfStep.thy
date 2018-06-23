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
  by (metis convdiscrup_inv_eq sbHdElemWell_def sbHdElem_channel sbHdElem_dom)

lemma sbHdElemWell_invConvDiscrUp:"sbHdElemWell sb \<Longrightarrow> \<forall>c\<in>ubDom\<cdot>(sb).((inv convDiscrUp) (sbHdElem\<cdot>sb)) \<rightharpoonup> c = inv Discr (inv Iup ((sbHdElem\<cdot>sb) \<rightharpoonup> c))"
  by (simp add: convDiscrUp_inv_subst sbHdElemWell_def sbHdElem_channel)
    
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
      by (metis a1 bottomI sbHdElemWell_def ubdom_below ubgetch_below)
    have a3:"sbHdElem\<cdot>x = sbHdElem\<cdot>y"
        apply(rule sbHdElem_eq)
        apply (meson True sbHdElemWell_def)
        using True sbHdElemWell_def a1 by blast
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
    obtain n where n_def:" sbHdElemWell (Y n)"
      sorry
    then have h1:"(if sbHdElemWell (\<Squnion>i. Y i) then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(\<Squnion>i. Y i))))) else ufLeast In Out) = (ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>( Y n))))))"
      by(subst sbHdEq[of n], simp_all add: True n_def)
    then have h2:"ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(Y n)))))\<sqsubseteq> (\<Squnion>i. (if sbHdElemWell (Y i) then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>(Y i))))) else ufLeast In Out))"
    proof -
      show ?thesis
        using a2 below_lub n_def by fastforce
    qed
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
    
lemma spfStep_inj_on:"inj_on (Rep_cfun (spfStep_inj In Out)) {h. \<forall>m. ufDom\<cdot>(h m) = In \<and> ufRan\<cdot>(h m) = Out}"
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

lemma spfStep_cont:"cont(\<lambda> h. Abs_ufun(\<Lambda> sb. (ubDom\<cdot>sb = In) \<leadsto> spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb))"
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
     
lemma "spfStep In Out\<cdot>h \<rightleftharpoons> sb = spfStep_inj In Out\<cdot>h\<cdot>sb \<rightleftharpoons> sb"
  sorry
  
  (*TODO
lemma spfstep_insert 

lemma spfstep_dom[simp]:"ufDom\<cdot>(spfStep cIn cOut\<cdot>f) = cIn"
  oops
    
lemma spfstep_ran [simp]:"ufRan\<cdot>(spfStep cIn cOut\<cdot>f) = cOut"
  oops 
    
lemma spfstep_step
*)
end