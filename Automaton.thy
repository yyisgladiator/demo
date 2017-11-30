(*  Title:        Automaton
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Frontend for deterministic Automatons, transformed from MontiArc-Automaton
*)

theory Automaton
imports SPF If_Else_Continuity
begin
default_sort type


section \<open>Backend Signatures\<close>
(* This stuff is only here until the functions are defined in the backend, they will be in SPF.thy *)


(* VERY Basic automaton type *)
(* ToDo: wellformed condition *)

(* FYI: in the non-deterministic case the automaton will be a cpo *)

(* The content is:
  transition function \<times> initial state \<times> initial Output \<times> input domain \<times> output domain *)
typedef ('state::type, 'm::message) automaton = 
  "{f::(('state \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> ('state \<times> 'm SB)) \<times> 'state \<times> 'm SB \<times> channel set \<times> channel set. True}"
  sorry

definition getInitialState :: "('s, 'm::message) automaton \<Rightarrow> 's" where
"getInitialState automat = fst (snd (Rep_automaton automat))"

definition getDom :: "('s, 'm::message) automaton \<Rightarrow> channel set" where
"getDom = undefined" (* todo *)

definition getRan :: "('s, 'm::message) automaton \<Rightarrow> channel set" where
"getRan = undefined" (* todo *)

setup_lifting type_definition_automaton

(* HK is defining this. returns the fixpoint *)
definition myFixer :: "channel set \<Rightarrow> channel set \<Rightarrow> (('s \<Rightarrow> 'm SPF)\<rightarrow>('s \<Rightarrow> 'm SPF)) \<rightarrow> ('s \<Rightarrow> 'm SPF)" where
"myFixer = undefined"


(* updis bijectiv *)
thm inv_def
definition spfStep_h2::" channel set \<Rightarrow> (channel\<rightharpoonup>'m::message discr\<^sub>\<bottom>) \<Rightarrow> (channel\<rightharpoonup>'m)" where
"spfStep_h2 In = (\<lambda>f. (\<lambda>c. (c \<in> In) \<leadsto> (inv updis f \<rightharpoonup> c)))"

(* look at "if-then-cont" file in root *)
(* If_Else_Continuity.thy *)

(* spfRestrict wrapper on "h (spfStep_h2 In f)" *)
(* "h" should be cont, maybe later *)
(* alternative (\<bottom> \<notin> ran f) *)
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
lemma discr_u_chain_lubnbot_equiv_allc: assumes"chain (Y::nat \<Rightarrow> channel \<Rightarrow> 'a discr\<^sub>\<bottom>)" shows " (\<forall>c. (\<Squnion>i. Y i) c \<noteq>\<bottom>) \<longleftrightarrow> (\<exists>i.\<forall>c. Y i c \<noteq> \<bottom>)"
  apply(auto)*)
    
lemma obtain_n_for_all_c:assumes "chain (Y::nat \<Rightarrow> channel\<rightharpoonup>'a discr\<^sub>\<bottom>)"
(*  shows "finite_chain Y" (* Wenn channel finite *) *)
and "\<forall>c\<in>In. \<exists>i. ((Y i) \<rightharpoonup> c) \<noteq> \<bottom>" 
and "\<forall>c\<in>In. ((\<Squnion>i. Y i) \<rightharpoonup> c) \<noteq> \<bottom>" 

shows "\<exists>n. \<forall>c\<in>In. ((Y n)\<rightharpoonup> c) = ((\<Squnion>i. Y i) \<rightharpoonup> c)"
proof-
  have chain_Yc:"\<forall>c. chain(\<lambda>i. Y i  \<rightharpoonup> c)"
    by (metis assms(1) part_the_chain)
  have "\<forall>c\<in>In. \<exists>i. (Y i  \<rightharpoonup> c) \<noteq> \<bottom>"
    by (simp add: assms(2))
  have test1:"\<And>c. c\<in>In \<Longrightarrow> ((\<Squnion>i. Y i) \<rightharpoonup> c) \<noteq> \<bottom>"
    by(simp add: assms(3))
  have "\<And>c. c\<in>In  \<Longrightarrow> \<exists>i. (Y i)\<rightharpoonup> c \<noteq> \<bottom>"
    by (simp add: assms(2))
  have h1:"\<And>c. c\<in>In \<Longrightarrow>  \<exists>i. (Y i)\<rightharpoonup> c = ((\<Squnion>i. Y i) \<rightharpoonup> c)"
    using assms(1) assms(3) exists_n_for_c by blast
  have h2:"\<And>c. c\<in>In \<Longrightarrow> \<exists>i. \<forall>ia\<ge>i. Y ia \<rightharpoonup> c = (Y i)\<rightharpoonup> c"
  proof -
    fix c :: channel
    { fix nn :: "nat \<Rightarrow> nat"
      have "\<And>f n na c. \<not> chain f \<or> \<not> n \<le> na \<or> (f n\<rightharpoonup>c::channel::'a discr\<^sub>\<bottom>) \<sqsubseteq> f na\<rightharpoonup>c"
        by (metis part_the_chain po_class.chain_mono)
      then have "\<exists>n. \<not> n \<le> nn n \<or> Y (nn n)\<rightharpoonup>c = Y n\<rightharpoonup>c"
        by (metis assms(1) discr_u_below_eq) }
    then show "\<exists>n. \<forall>na\<ge>n. Y na\<rightharpoonup>c = Y n\<rightharpoonup>c"
      by meson
  qed
  have h3_2:"\<exists>i. \<forall>c\<in>In. Y i \<rightharpoonup> c \<noteq> \<bottom>"(* AHHHHHHHHHHHHHHAHAHAHHHHHHHHHHHHHHHHHH\<And>\<And>\<And>\<And>\<And>\<And>\<And>\<And>\<And>\<And>\<And>\<And>\<And>!11!1\<And>! HELP MEEE*)
      sorry
  (*have h3:"\<exists>i. \<forall>c\<in>In. \<forall>ia\<ge>i. Y ia \<rightharpoonup> c = (Y i)\<rightharpoonup> c" 
    sorry*)
  then have h4:"\<exists>i. \<forall>c\<in>In. Y i \<rightharpoonup> c = (\<Squnion>i. ((Y i) \<rightharpoonup> c))"
    using below_lub chain_Yc discr_u_below_eq by blast
  then have "\<exists>i. \<forall>c\<in>In. (Y i)\<rightharpoonup> c = (\<Squnion>i. Y i)\<rightharpoonup> c"
    by (metis assms(1) part_the_lub)
  then show ?thesis
    by simp
qed  
  


lemma obtain_n_for_all_ch:assumes "chain (Y::nat \<Rightarrow> channel\<rightharpoonup>'a discr\<^sub>\<bottom>)" and "\<forall>c\<in>In. \<exists>i. ((Y i) \<rightharpoonup> c) \<noteq> \<bottom>" and "\<forall>c\<in>In. ((\<Squnion>i. Y i) \<rightharpoonup> c) \<noteq> \<bottom>" obtains n where "\<forall>c\<in>In. ((Y n)\<rightharpoonup> c) = ((\<Squnion>i. Y i) \<rightharpoonup> c)"
  using assms(1) assms(2) assms(3) obtain_n_for_all_c by blast
    

    
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
    
lemma[simp]:"cont(\<lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In f)) else spfLeast In Out) "
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
          by(rule obtain_n_for_all_ch[of Y In],simp_all add: a1 True h123)
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
              
lemma spfStep_h1_mono[simp]:"monofun (\<lambda> h. (\<Lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In f)) else spfLeast In Out))"
by(rule monofunI, simp add: below_cfun_def below_fun_def, simp add: spfrestrict_below)
  
  
    
      
lemma spfStep_h1_cont[simp]:"cont (\<lambda> h. (\<Lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In f)) else spfLeast In Out))"
proof(rule Cont.contI2, simp add: spfStep_h1_mono)  
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
    by(simp add: below_cfun_def below_fun_def contlub_cfun_fun, auto, simp add: h1)
qed
  
      
      
lemma[simp]: "spfDom\<cdot>(spfStep_h1 In Out\<cdot> h \<cdot> f) = In"
  by(simp add: spfStep_h1_def)
    

lemma spfStep_h1_ran[simp]: "spfRan\<cdot>(spfStep_h1 In Out\<cdot> h \<cdot> f) = Out"
  by(simp add: spfStep_h1_def)

lemma spfstep_h1_insert: "spfStep_h1 In Out\<cdot> h\<cdot>f = (if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In f)) else spfLeast In Out)"
  by(simp add:  spfStep_h1_def)    

(*spfStep_h1 mono cont end*)     
      
thm spfRestrict_def
(* Skeleton of spfStep. Returns the SPF that switches depending on input *)
definition spfStep :: "channel set \<Rightarrow> channel set \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF) \<rightarrow> 'm SPF" where
"spfStep In Out \<equiv> \<Lambda> h. Abs_SPF (\<Lambda>  sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot> h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"


(* spfStep mono and cont*)


(* spfStep inner SPF spf_well and cont*)

lemma spfStep_inSPF_mono[simp]:"monofun (\<lambda>b. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>b) \<rightleftharpoons> b)"
  apply(rule monofunI)
  by (metis below_SPF_def below_option_def below_refl monofun_cfun monofun_cfun_arg)
   
    
lemma spfStep_inSPF_cont[simp]:"cont (\<lambda> sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot> h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"  
proof(rule spf_contI2,rule Cont.contI2,auto)
  fix Y::"nat \<Rightarrow> 'a SB"
  assume chain:"chain Y"
  assume chain2:"chain (\<lambda>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> Y i)"
  have h1:"spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(\<Squnion>i. Y i)) = (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)))"
    by(simp add: chain contlub_cfun_fun contlub_cfun_arg)
  have h_true:"sbDom\<cdot>(\<Squnion>i. Y i) = In \<Longrightarrow> \<forall>i. sbDom\<cdot>(Y i) = In"
    by (simp add: chain sbChain_dom_eq2)
  have h_false:"sbDom\<cdot>(\<Squnion>i. Y i) \<noteq> In \<Longrightarrow> \<forall>i. sbDom\<cdot>(Y i) \<noteq> In"
    by (simp add: chain sbChain_dom_eq2)
  have "(\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i))) \<rightleftharpoons> (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> Y i)"
    sorry (* @Jens *)
  then show "spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(\<Squnion>i. Y i)) \<rightleftharpoons> (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> Y i)"
    by(simp add: h1)
qed   
    
lemma spfStep_inSPF_well[simp]:"spf_well (\<Lambda>  sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot> h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)" 
  proof(rule spf_wellI)
    fix b::"'a SB"
    assume "b \<in> dom (Rep_cfun (\<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
    hence b_def:" b \<in> dom (\<lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)" 
      by simp
    thus "sbDom\<cdot>b = In"
    proof -
      show ?thesis
      by (meson b_def if_then_sbDom)
    qed
    thus "sbDom\<cdot>(the ((\<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)\<cdot>b)) = Out" 
      by simp
  next
    fix b2::"'a SB"
    assume "sbDom\<cdot>b2 = In"
    thus "b2 \<in> dom (Rep_cfun (\<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot> h\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))" 
      by (simp add: domIff)
qed

(*spfStep outer cont*)
    
lemma spfStep_mono[simp]:"monofun (\<lambda> h. Abs_SPF (\<Lambda>  sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot> h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
proof(rule monofunI, simp add: below_SPF_def below_cfun_def)
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

lemma spf_pref_eq_2: assumes "(f \<sqsubseteq> g)"
  shows "(f \<rightleftharpoons> a) \<sqsubseteq> (g \<rightleftharpoons> a)" 
  by (metis assms below_SPF_def below_option_def cfun_below_iff po_eq_conv)


lemma getSb_in_h:assumes "chain (Y::nat \<Rightarrow> 'a::message SPF)" shows "(\<Squnion>i. Rep_SPF (Y i))\<cdot> sb = (\<Squnion>i. (Rep_SPF (Y i) \<cdot> sb))"
  by(subst contlub_cfun_fun, simp_all add: assms)
    
    
lemma getSb_in:assumes "chain Y" shows "(\<Squnion>i. Y i) \<rightleftharpoons> sb = (\<Squnion>i. Y i \<rightleftharpoons> sb)"
proof(cases "spfDom\<cdot>(\<Squnion>i. Y i) = sbDom\<cdot>sb")
  case True
  then have "\<forall>i. spfDom\<cdot>(Y i) = sbDom\<cdot>(sb)"
    using assms spfdom_eq_lub by auto
  have chain:"chain (\<lambda>i. Y i \<rightleftharpoons> sb)"
    by (simp add: op_the_chain assms)
  have "\<forall>i. Y i  \<rightleftharpoons> sb \<sqsubseteq> (\<Squnion>i. Y i \<rightleftharpoons> sb)"
    using below_lub chain by blast
  show ?thesis
    (*
  proof(rule sb_below)
    show "sbDom\<cdot>((\<Squnion>i. Y i) \<rightleftharpoons> sb) = sbDom\<cdot>(\<Squnion>i. Y i \<rightleftharpoons> sb)"
      by (metis True \<open>\<forall>i. spfDom\<cdot>(Y i) = sbDom\<cdot>sb\<close> \<open>chain (\<lambda>i. Y i \<rightleftharpoons> sb)\<close> assms sbChain_dom_eq2 spf_ran_2_tsbdom2 spfran_eq_lub)
  next
    fix c::channel
    show "c \<in> sbDom\<cdot>((\<Squnion>i. Y i) \<rightleftharpoons> sb) \<Longrightarrow> ((\<Squnion>i. Y i) \<rightleftharpoons> sb) . c \<sqsubseteq> (\<Squnion>i. Y i \<rightleftharpoons> sb) . c "
      apply (subst sbgetch_lub, simp_all add: chain)*)
      sorry
next
  case False
  then have "\<forall>i. spfDom\<cdot>(Y i) \<noteq> sbDom\<cdot>(sb)"
    using assms spfdom_eq_lub by blast
  then show ?thesis 
    by (metis (mono_tags, lifting) spf_pref_eq_2 False assms lub_chain_maxelem option.exhaust_sel po_class.chainE spfdom2sbdom)
qed
    
lemma spf_sbDom: assumes "spfDom\<cdot>f = In" and "spfRan\<cdot>f = Out" and "sbDom\<cdot>sb= In" shows "sbDom\<cdot>(f \<rightleftharpoons> sb) = Out"
  by (simp add: assms(1) assms(2) assms(3))
lemma spfStep_cont:"cont (\<lambda> h. Abs_SPF (\<Lambda>  sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot> h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
proof(rule Cont.contI2, simp)
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
  have cont_lub:"\<forall>i. cont (\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
    by simp
  have spf_well:"\<forall>i. spf_well (\<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
    by simp
  have chain_h0:"chain (\<lambda>i. \<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
  proof(rule chainI)
    fix i::nat
    show "(\<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb) \<sqsubseteq> (\<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y (Suc i))\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
      apply(simp add: below_cfun_def)
      by (smt below_option_def cfun_below_iff chain_1 fun_belowI po_class.chain_def some_below spf_pref_eq_2)
  qed    
  have cont_lub:"cont (\<lambda>x. \<Squnion>i. (\<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)\<cdot>x)"
    apply(subst beta_cfun, simp)
    apply(rule cont2cont_lub,simp_all)
    apply(rule chainI)
    by (smt below_option_def cfun_below_iff chain_1 fun_belowI po_class.chain_def some_below spf_pref_eq_2)
  have cont_lub2:"cont (\<lambda>x. \<Squnion>i. (sbDom\<cdot>x = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>x) \<rightleftharpoons> x)"
    apply(rule cont2cont_lub,simp_all)
    apply(rule chainI)
    by (smt below_option_def cfun_below_iff chain_1 fun_belowI po_class.chain_def some_below spf_pref_eq_2)
  have "\<And>b.  sbDom\<cdot>b= In \<Longrightarrow> \<forall>i . sbDom\<cdot>(spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>b) \<rightleftharpoons> b) = Out"
  by auto
  then have "\<And>b. sbDom\<cdot>b= In \<Longrightarrow> sbDom\<cdot>(\<Squnion>i. (spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>b) \<rightleftharpoons> b)) = Out"
    by (metis (no_types, lifting) chain_4 sbChain_dom_eq2)
  have spf_well:"spf_well (\<Lambda> x. \<Squnion>i. (\<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)\<cdot>x)"
    apply(subst beta_cfun,simp)
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
   apply(subst rep_abs_cspf, simp, simp,simp only: cont_lub2)
   apply(subst rep_abs_cspf,simp,simp, simp only:spf_well2)
   apply(subst rep_abs_cspf, simp, simp)
   apply(subst contlub_lambda,simp_all)
   apply(rule chainI)
   by (smt below_option_def cfun_below_iff chain_1 fun_belowI po_class.chain_def some_below spf_pref_eq_2)
  have h1:"(\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(\<Squnion>i. Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb) \<sqsubseteq> Rep_CSPF (\<Squnion>i. Abs_CSPF (\<lambda>sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out\<cdot>(Y i)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
    apply(simp add: h0, subst h0_1)
  proof(rule fun_belowI)
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
    by(simp add: below_SPF_def below_cfun_def h1)
qed
  

lemma spfstep_insert: "spfStep In Out\<cdot>h= Abs_SPF (\<Lambda>  sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out\<cdot> h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
  by(simp add: spfStep_cont spfStep_def)

thm spfStep_h2_def
lemma abcc:"sbHdElem\<cdot>sb = convDiscrUp a \<Longrightarrow> spfStep_h2 (sbDom\<cdot>sb) (sbHdElem\<cdot>sb) = a"
  apply(auto simp add: spfStep_h2_def convDiscrUp_def)
  sorry

(* Any idea how we can write the final lemma nicer? *)
lemma spfStep_final: assumes "sbDom\<cdot>sb = In" and "sbHdElem\<cdot>sb = convDiscrUp a" and "spfDom\<cdot>(h a) = In" and "spfRan\<cdot>(h a) = Out" 
  (* and  "\<forall>c\<in>In. (sbHdElem\<cdot>sb \<rightharpoonup> c) \<noteq> \<bottom>" *) and "sbLen\<cdot>sb > 0"
  shows "spfStep In Out\<cdot>h\<rightleftharpoons>sb = (h a)\<rightleftharpoons>sb"
  apply(simp add: spfstep_insert assms)
  apply(simp add: spfstep_h1_insert)
proof-
  have h1:"(spfStep_h2 In (convDiscrUp a)) = a"
  proof-
    show ?thesis
      using abcc[of sb a] by (simp add: assms)
  qed
  show "(In \<subseteq> dom (convDiscrUp a) \<and> (\<forall>c\<in>In. convDiscrUp a\<rightharpoonup>c \<noteq> \<bottom>) \<longrightarrow> spfRestrict In Out\<cdot>(h (spfStep_h2 In (convDiscrUp a))) \<rightleftharpoons> sb = h a \<rightleftharpoons> sb) \<and>
    ((In \<subseteq> dom (convDiscrUp a) \<longrightarrow> (\<exists>c\<in>In. convDiscrUp a\<rightharpoonup>c = \<bottom>)) \<longrightarrow> spfLeast In Out \<rightleftharpoons> sb = h a \<rightleftharpoons> sb)"
  proof(simp add: h1 assms)
    have "\<forall>c\<in>In. (convDiscrUp a\<rightharpoonup>c) \<noteq> \<bottom>"
      using assms(5) assms(2) by simp
    then have "(\<exists>c\<in>In. convDiscrUp a\<rightharpoonup>c = \<bottom>) = False"
      by simp
    then show "(In \<subseteq> dom (convDiscrUp a) \<longrightarrow> (\<exists>c\<in>In. convDiscrUp a\<rightharpoonup>c = \<bottom>)) \<longrightarrow> Out^\<bottom> = h a \<rightleftharpoons> sb"
      sorry
  qed
qed
    
  
(* spfStep mono and cont end*)

(* spfStep Test Lemma*)
    
    
(* spfStep Test Lemma end*)

    
(* Defined by SWS *)
definition spfRt :: "'m SPF \<rightarrow> 'm SPF" where
"spfRt = undefined"

(* Defined by JCB *)
definition spfCons :: "'m SB \<Rightarrow> 'm SPF \<rightarrow> 'm SPF" where
"spfCons = undefined"

(* Converter function. *)
  (* definition should be right, but needs to be nicer *)
definition helper:: "(('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message SB)) \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> 'm SPF) \<rightarrow> ('e \<Rightarrow> 'm SPF)" where
"helper f s \<equiv> \<Lambda> h. (\<lambda> e. spfRt\<cdot>(spfCons (snd (f (s,e)))\<cdot>(h (fst (f (s,e))))))" 

lemma "cont (\<lambda>h. (\<lambda> e. spfCons (snd (f (s,e)))\<cdot>(h (fst (f (s,e))))))"
  oops

(* As defined in Rum96 *)
definition h :: "('s::type, 'm::message) automaton \<Rightarrow> ('s \<Rightarrow> 'm SPF)" where
"h automat = myFixer (getDom automat)(getRan automat)\<cdot>(\<Lambda> h. (\<lambda>s. spfStep{}{}\<cdot>(helper undefined s\<cdot>h)))"

lemma "cont (\<lambda> h. (\<lambda>s. spfStep{}{}\<cdot>(helper automat s\<cdot>h)))"
  by simp

(* This function also prepends the first SB ... *)
(* But basically she just calls h *)
definition H :: "('s, 'm::message) automaton \<Rightarrow> 'm SPF" where
"H automat = h automat (getInitialState automat)"






(* From here everything should be automatically transformed from MontiArc-Automaton *)
section \<open>Automaton Datatypes\<close>

(* Only on idea how the states could be implemented *)
datatype substate = singleState | \<NN>  (* This are the actual states from MAA *)
datatype myState = State substate nat (* And these have also the variables *)

fun getVarI :: "myState \<Rightarrow> nat" where
"getVarI (State s n ) = n"

fun getSubState :: "myState \<Rightarrow> substate" where
"getSubState (State s n ) = s"


datatype myM = N nat | B bool

instance myM :: countable
apply(intro_classes)
by(countable_datatype)


instantiation myM :: message
begin
  fun ctype_myM :: "channel \<Rightarrow> myM set" where
  "ctype_myM c1 = range N"  |
  "ctype_myM c2 = range B"

instance
by(intro_classes)
end



section \<open>Automaton Functions\<close>

(* Creates a fitting SB given the right output values *)
(* Parameter: 
  channel set \<Rightarrow> domain of the output
  nat         \<Rightarrow> maps to channel c1, in MAA called "XXXX"
  bool        \<Rightarrow> maps to channel c2, in MAA calles "YYYY" *)
fun createOutput :: "channel set \<Rightarrow> nat \<Rightarrow> nat  \<Rightarrow> myM SB" where
"createOutput cs n var = Abs_SB(\<lambda>c. (c \<in> cs) \<leadsto> \<up>(B (((n + var) mod 2) = 0) ))"

definition myTr_h::"(channel \<rightharpoonup> myM) \<Rightarrow> channel \<Rightarrow> nat" where
"myTr_h f c =  (THE a. Some (N a) =(f c))"
(* Somehow define the transition function *)
(* use the createOutput function *)
definition myTransition :: "(myState \<times>(channel \<rightharpoonup> myM)) \<Rightarrow> (myState \<times> myM SB)" where
"myTransition x =   (if  ((getSubState (fst x) = singleState) \<and> (snd x c1 \<noteq> None)) 
                     then (State singleState (myTr_h (snd x) c1 + getVarI (fst x)), 
                            (createOutput {c1} (getVarI (fst x)) (myTr_h(snd x) c1)))
                     else (State \<NN> 0, (sbLeast {c1})))"

lift_definition myAutomaton :: "(myState, myM) automaton" is "(myTransition, State singleState 0, sbLeast {}, {}, {})"
 by simp

definition mySPF :: "myM SPF" where
"mySPF = H myAutomaton"




section \<open>Automaton Lemma\<close>


end
