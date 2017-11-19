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
definition spfStep_h1::"channel set \<Rightarrow> channel set \<Rightarrow>((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF) \<Rightarrow>((channel\<rightharpoonup>'m discr\<^sub>\<bottom>)\<rightarrow> 'm SPF)" where
"spfStep_h1 In Out= (\<lambda> h. (\<Lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In f)) else spfLeast In Out))"

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
        have "\<forall>c. chain (\<lambda>i. Y i\<rightharpoonup>c)"
          using a1 by (metis part_the_chain)
        then have "\<forall>i c. Y i\<rightharpoonup>c \<sqsubseteq> Y (Suc i) \<rightharpoonup>c"
          using po_class.chainE by blast
        have "\<forall>i c. Y i\<rightharpoonup>c = \<bottom> \<Longrightarrow>\<forall>c.  (\<Squnion>i. Y i) \<rightharpoonup> c = \<bottom>"
          by (simp add: a1 part_the_lub)
        have "\<forall>c\<in>In. \<exists>i. Y i \<rightharpoonup> c \<noteq> \<bottom>"
        proof-
          have a11:"\<forall>c\<in>In. (\<Squnion>i. Y i)\<rightharpoonup>c \<noteq> \<bottom>" 
            by (simp add: True)
          have a12:"\<exists>c\<in>In. \<forall>i. Y i\<rightharpoonup>c = \<bottom> \<Longrightarrow>\<not>(\<forall>c\<in>In.  (\<Squnion>i. Y i) \<rightharpoonup> c \<noteq> \<bottom>)"
            by (simp add: a1 lub_eq_bottom_iff part_the_chain part_the_lub)
          have a13:"\<not>(\<exists>i. \<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>) \<Longrightarrow> \<forall>c\<in>In. (\<Squnion>i. Y i)\<rightharpoonup>c \<noteq> \<bottom>"
            by (simp add: a11)
          then show " \<forall>c\<in>In. \<exists>i. Y i\<rightharpoonup>c \<noteq> \<bottom>"
            using a12 by blast
        qed
        have "\<exists>i. \<forall>c\<in>In. Y i \<rightharpoonup> c \<noteq> \<bottom>"
          proof-
          have "\<And>i c. Y i \<rightharpoonup> c \<noteq> \<bottom> \<Longrightarrow> Y(Suc i) \<rightharpoonup> c \<noteq> \<bottom>"
            by (metis \<open>\<forall>i c. Y i\<rightharpoonup>c \<sqsubseteq> Y (Suc i)\<rightharpoonup>c\<close> below_bottom_iff)
          show "\<exists>i. \<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>"
          proof-
            have h1:"\<not>(\<exists>i. \<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>) \<Longrightarrow> \<exists>c\<in>In. (\<Squnion>i. Y i)\<rightharpoonup>c = \<bottom>"
              sorry      
            then show ?thesis
              using True by blast
          qed
        qed
        have "\<And> c. c\<in>In \<Longrightarrow>\<exists>i.  Y i \<rightharpoonup> c = (\<Squnion>i. Y i)\<rightharpoonup>c"
        proof-
          fix c::channel
          assume a11:"c \<in> In"
          have h1:"\<exists>i.  Y i \<rightharpoonup> c \<noteq> \<bottom>"
            using \<open>\<exists>i. \<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>\<close> a11 by auto
          have h2:"\<forall>c i. Y i\<rightharpoonup>c \<sqsubseteq> (\<Squnion>i. Y i)\<rightharpoonup>c"
            by (metis  a1 is_ub_thelub part_the_chain part_the_lub)
          show "\<exists>i.  Y i \<rightharpoonup> c = (\<Squnion>i. Y i)\<rightharpoonup>c" 
            using discr_u_below_eq h1 h2 by blast
        qed
        obtain n where "(\<lambda>i. if (In \<subseteq> dom (Y i) \<and> (\<forall>c\<in>In. ((Y i)\<rightharpoonup>c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else spfLeast In Out) n = spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y n)))"
          by (meson \<open>\<exists>i. \<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>\<close> \<open>\<forall>i. In \<subseteq> dom (Y i)\<close>)
        have "\<forall>i. n \<le> i \<longrightarrow> (\<forall>c\<in>In. ((Y i)\<rightharpoonup>c \<noteq> \<bottom>))" 
        proof-
          have " \<forall>c\<in>In. Y n\<rightharpoonup>c \<noteq> \<bottom>"
               sorry
            show"\<forall>i\<ge>n. \<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>"
              by (metis (no_types, lifting) \<open>\<forall>c\<in>In. Y n\<rightharpoonup>c \<noteq> \<bottom>\<close> a1 discr_u_below_eq part_the_chain po_class.chain_mono)
        qed  
        have "\<forall>i. n \<le> i \<longrightarrow> (\<lambda>i. if (In \<subseteq> dom (Y i) \<and> (\<forall>c\<in>In. ((Y i)\<rightharpoonup>c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else spfLeast In Out) i = spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y i)))"
          apply auto
           apply (metis True a1 domD part_dom_lub set_rev_mp)
          using \<open>\<forall>i\<ge>n. \<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>\<close> by blast
        have "\<forall>i. spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) \<sqsubseteq> (\<Squnion>i. if In \<subseteq> dom (Y i) \<and> (\<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>) then spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else spfLeast In Out)" 
            sorry
        have h4:"(\<Squnion>i. if In \<subseteq> dom (Y i) \<and> (\<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>) then spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))) else spfLeast In Out) = (\<Squnion>i. spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))))"
          sorry
       have h5:"(if In \<subseteq> dom (\<Squnion>i. Y i) \<and> (\<forall>c\<in>In. (\<Squnion>i. Y i)\<rightharpoonup>c \<noteq> \<bottom>) then spfRestrict In Out\<cdot>(h (spfStep_h2 In (\<Squnion>i. Y i))) else spfLeast In Out) = spfRestrict In Out\<cdot>(h (spfStep_h2 In (\<Squnion>i. Y i)))"
         by (simp add: True)
       have "\<forall>i\<ge>n. (\<lambda>c. (c \<in> In)\<leadsto>inv updis (\<Squnion>i. Y i)\<rightharpoonup>c) = (\<lambda>c. (c \<in> In)\<leadsto>inv updis Y i\<rightharpoonup>c)"
       proof -
         { fix cc :: channel and cca :: channel and nn :: nat
           have "\<And>n c. ((Y n)\<rightharpoonup>c \<sqsubseteq> (Lub (\<lambda>i. (Y i)\<rightharpoonup>c)))"
             using \<open>\<forall>c. chain (\<lambda>i. Y i\<rightharpoonup>c)\<close> is_ub_thelub by blast
           then have "\<And>n c. Y n\<rightharpoonup>c \<sqsubseteq> Lub Y\<rightharpoonup>c"
             by (metis (no_types) a1 part_the_lub)
           then have "cc \<notin> In \<or> cca \<notin> In \<or> \<not> n \<le> nn \<or> cc \<in> In \<and> cca \<in> In \<and> Some (inv updis Y nn\<rightharpoonup>cca) = Some (inv updis Lub Y\<rightharpoonup>cca)"
             by (metis (no_types) \<open>\<forall>i\<ge>n. \<forall>c\<in>In. Y i\<rightharpoonup>c \<noteq> \<bottom>\<close> discr_u_below_eq) }
         then show ?thesis
           by fastforce
       qed
       then have h6:"(h (\<lambda>c. (c \<in> In)\<leadsto>inv updis (\<Squnion>i. Y i)\<rightharpoonup>c)) = (\<Squnion>i. h (\<lambda>c. (c \<in> In)\<leadsto>inv updis Y i\<rightharpoonup>c))"
         sorry
       have h_chain:"chain (\<lambda>i. h (\<lambda>c. (c \<in> In)\<leadsto>inv updis Y i\<rightharpoonup>c))"
         sorry
       show ?thesis 
       proof(simp only: h5 h4)
         show "spfRestrict In Out\<cdot>(h (spfStep_h2 In (\<Squnion>i. Y i))) \<sqsubseteq> (\<Squnion>i. spfRestrict In Out\<cdot>(h (spfStep_h2 In (Y i))))"
           by(simp add: contlub_cfun_arg h_chain spfStep_h2_def h6)
       qed  
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
      
        
lemma spfStep_h1_mono:"monofun (\<lambda> h. (\<Lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In f)) else spfLeast In Out))"
  apply(rule monofunI)
  sorry
      
lemma spfStep_h1_cont:"cont (\<lambda> h. (\<Lambda> f. if (In \<subseteq> dom f \<and> (\<forall>c \<in> In. (f \<rightharpoonup> c \<noteq> \<bottom>))) then spfRestrict In Out\<cdot>(h (spfStep_h2 In f)) else spfLeast In Out))"
  apply(rule Cont.contI2)
  sorry
      
      
lemma[simp]: "spfDom\<cdot>(spfStep_h1 In Out h \<cdot> f) = In"
  by(simp add: spfStep_h1_def)
    

lemma[simp]: "spfRan\<cdot>(spfStep_h1 In Out h \<cdot> f) = Out"
  by(simp add: spfStep_h1_def)
    
(*spfStep_h1 mono cont end*)     
      
thm spfRestrict_def
(* Skeleton of spfStep. Returns the SPF that switches depending on input *)
definition spfStep :: "channel set \<Rightarrow> channel set \<Rightarrow> ((channel\<rightharpoonup>'m::message) \<Rightarrow> 'm SPF) \<rightarrow> 'm SPF" where
"spfStep In Out \<equiv> \<Lambda> h. Abs_SPF (\<Lambda>  sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"


(* spfStep mono and cont*)


(* spfStep inner SPF spf_well and cont*)

lemma spfStep_inSPF_mono[simp]:"monofun (\<lambda>b. spfStep_h1 In Out h\<cdot>(sbHdElem\<cdot>b) \<rightleftharpoons> b)"
  apply(rule monofunI) 
  by (smt below_SPF_def domIff monofun_cfun option.exhaust_sel po_eq_conv sbdom_eq some_below2 spfLeastIDom spf_below_sbdom spf_sbdom2dom)


lemma spfStep_inSPF_cont[simp]:"cont (\<lambda> sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)"
proof(rule spf_contI2,rule Cont.contI2,auto)
  fix Y::"nat \<Rightarrow> 'a SB"
  assume chain:"chain Y"
  assume chain2:"chain (\<lambda>i. spfStep_h1 In Out h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> Y i)"
  have h1:"spfStep_h1 In Out h\<cdot>(sbHdElem\<cdot>(\<Squnion>i. Y i)) = (\<Squnion>i. spfStep_h1 In Out h\<cdot>(sbHdElem\<cdot>(Y i)))"
    by(simp add: chain contlub_cfun_fun contlub_cfun_arg)
  have h_true:"sbDom\<cdot>(\<Squnion>i. Y i) = In \<Longrightarrow> \<forall>i. sbDom\<cdot>(Y i) = In"
    by (simp add: chain sbChain_dom_eq2)
  have h_false:"sbDom\<cdot>(\<Squnion>i. Y i) \<noteq> In \<Longrightarrow> \<forall>i. sbDom\<cdot>(Y i) \<noteq> In"
    by (simp add: chain sbChain_dom_eq2)
  have "(\<Squnion>i. spfStep_h1 In Out h\<cdot>(sbHdElem\<cdot>(Y i))) \<rightleftharpoons> (\<Squnion>i. Y i) = (\<Squnion>i. spfStep_h1 In Out h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> Y i)"
    sorry
  then show "spfStep_h1 In Out h\<cdot>(sbHdElem\<cdot>(\<Squnion>i. Y i)) \<rightleftharpoons> (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. spfStep_h1 In Out h\<cdot>(sbHdElem\<cdot>(Y i)) \<rightleftharpoons> Y i)"
    by(simp add: h1)
qed   
    
lemma spfStep_inSPF_well[simp]:"spf_well (\<Lambda>  sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)" 
  proof(rule spf_wellI)
    fix b::"'a SB"
    assume "b \<in> dom (Rep_cfun (\<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out h\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
    hence b_def:" b \<in> dom (\<lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out h\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)" 
      by simp
    thus "sbDom\<cdot>b = In"
      proof -
        show ?thesis
        by (meson b_def if_then_sbDom)
      qed
      thus "sbDom\<cdot>(the ((\<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out h\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb)\<cdot>b)) = Out" 
        by simp
  next
    fix b2::"'a SB"
    assume "sbDom\<cdot>b2 = In"
    thus "b2 \<in> dom (Rep_cfun (\<Lambda> sb. (sbDom\<cdot>sb = In)\<leadsto>spfStep_h1 In Out h\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))" 
      by (simp add: domIff)
qed

(*spfStep outer cont*)
    
lemma spfStep_mono:"monofun (\<lambda> h. Abs_SPF (\<Lambda>  sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))"
  sorry
  
lemma spfStep_cont:"cont (\<lambda> h. Abs_SPF (\<Lambda>  sb.  (sbDom\<cdot>sb = In) \<leadsto> (spfStep_h1 In Out h)\<cdot>(sbHdElem\<cdot>sb) \<rightleftharpoons> sb))" 
  sorry
    
    
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
