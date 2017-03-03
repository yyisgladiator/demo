(*  Title:  SerComp_JB.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: additional  lemmas for composition
*)

theory SPF_Composition_JB
imports SPF SBTheorie SPF_Templates
begin
  
(* ----------------------------------------------------------------------- *)
section \<open>spfCompHelp2\<close>
(* ----------------------------------------------------------------------- *) 
  
lemma sbdom_le_eq:  assumes "x \<sqsubseteq> y"
  shows "sbDom\<cdot>x = sbDom\<cdot>y"
      by (metis assms(1) sbdom_eq)
  
lemma spfcomp_tospfH2: "(spfcomp f1 f2) 
                   = Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> 
                      (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2)"
  apply (subst spfcomp_def, subst spfCompHelp2_def, subst C_def, subst I_def, subst Oc_def)
  by (metis (no_types) C_def I_def Oc_def)
  
lemma spfCompH2_mono[simp]: "monofun (\<lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> spfDom\<cdot>f1)) 
                                             \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> spfDom\<cdot>f2)))"
  using cont2mono spfCompHelp_cont by blast

lemma spfCompH2_cont[simp]: "cont (\<lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> spfDom\<cdot>f1)) 
                                          \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> spfDom\<cdot>f2)))"
  using spfCompHelp_cont by blast

lemma helpermonoinX: shows "monofun (\<lambda> x. spfCompHelp2 f1 f2 x)"
by(simp add: spfCompHelp2_def)

lemma helpercontinX[simp]: shows "cont (\<lambda> x. spfCompHelp2 f1 f2 x)"
apply(simp add: spfCompHelp2_def)
proof -
   have "\<forall>x. cont (\<lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1))  \<uplus> (f2 \<rightleftharpoons>(z \<bar> spfDom\<cdot>f2)))"
   by simp
   thus "cont (\<lambda>x. \<Lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1))  \<uplus> (f2 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f2)))"
   by (simp add: cont2cont_LAM)
qed

  
(* ----------------------------------------------------------------------- *)
section \<open>iter_spfCompHelp2\<close>
(* ----------------------------------------------------------------------- *) 
abbreviation iter_spfcompH2 :: "'a SPF \<Rightarrow> 'a SPF \<Rightarrow> nat \<Rightarrow> 'a SB  \<Rightarrow> 'a SB" where
"(iter_spfcompH2 f1 f2 i) \<equiv> (\<lambda> x. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"  

lemma iter_spfcompH2_cont[simp]: "\<forall> i. cont (\<lambda> x. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"
proof -
    have "\<forall> i. cont (\<lambda> x. iterate i\<cdot>(spfCompHelp2 f1 f2 x))"
      using cont_Rep_cfun2 cont_compose helpercontinX by blast
    thus ?thesis
      by simp
  qed

lemma  iter_spfcompH2_cont2[simp]: "\<And>i. cont (\<lambda>x. iter_spfcompH2 f1 f2 i x)"
  by simp
    
lemma iter_spfcompH2_mono[simp]:  "monofun (\<lambda> x. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"
  by (simp add: cont2mono)
    
(* replaced spfComp_serialnf_chain *)
lemma iter_spfcompH2_chain[simp]: assumes "sbDom\<cdot>x = I f1 f2"
  shows "chain (\<lambda>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"
  apply(rule sbIterate_chain)
  apply (simp add: assms C_def I_def)
  by blast
        


(* ----------------------------------------------------------------------- *)
section \<open>lub_iter_spfCompHelp2\<close>
(* ----------------------------------------------------------------------- *) 
  
subsection \<open>mono\<close>  


lemma lub_iter_spfCompHelp2_mono: assumes "x \<sqsubseteq> y" and  "sbDom\<cdot>x = I f1 f2"
  shows "(\<Squnion>i.(iter_spfcompH2 f1 f2 i) x) \<sqsubseteq> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) y)"
proof-
  have  "\<forall>i. ((iter_spfcompH2 f1 f2 i) x) \<sqsubseteq> ((iter_spfcompH2 f1 f2 i) y)"
    using assms monofun_def by fastforce
  moreover
  have "sbDom\<cdot>y = sbDom\<cdot>x"
    by (metis assms(1) sbdom_eq)
  ultimately
  show ?thesis
     by (simp add: assms(2) iter_spfcompH2_chain lub_mono)
 qed
   
lemma if_lub_iter_spfCompHelp2_mono: assumes "x \<sqsubseteq> y" 
  shows "((\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) x)) x) 
              \<sqsubseteq> ((\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) x)) y)"
proof (cases "sbDom\<cdot>x = I f1 f2")
  case True
    have  "\<forall>i. ((iter_spfcompH2 f1 f2 i) x) \<sqsubseteq> ((iter_spfcompH2 f1 f2 i) y)"
      using assms monofun_def by fastforce
    moreover
    have f1: "sbDom\<cdot>y = sbDom\<cdot>x"
      by (metis assms(1) sbdom_eq)
    ultimately
    have "(\<Squnion>i.(iter_spfcompH2 f1 f2 i) x) \<sqsubseteq> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) y)"
        by (simp add: assms True iter_spfcompH2_chain lub_mono)
    thus ?thesis
      by (simp add: f1 some_below)
next
  case False
   have "sbDom\<cdot>y = sbDom\<cdot>x"
      by (metis assms(1) sbdom_eq)
   thus ?thesis     
      by (simp add: False some_below)
  qed
    
  subsection \<open>cont\<close>  
    

  
(* ----------------------------------------------------------------------- *)
section \<open>spfComp\<close>
(* ----------------------------------------------------------------------- *) 
  

  
subsection \<open>mono\<close>  

lemma spf_comp_mono[simp]: "monofun (\<lambda> x. (sbDom\<cdot>x = I f1 f2) 
                                          \<leadsto> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) x)  \<bar> Oc f1 f2 )" 
proof -
  have "monofun (\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) x) )"
    by (metis (no_types, lifting) lub_eq monofun_def if_lub_iter_spfCompHelp2_mono)
  thus ?thesis
    by (smt monofun_cfun_arg monofun_def sbdom_eq some_below some_below2)
qed

subsection \<open>cont\<close>   

lemma test15:
  assumes cont: "\<And>i. cont (\<lambda>x. F i x)" 
  shows "chain Y\<longrightarrow>  (\<Squnion>i. F i (\<Squnion>i. Y i)) = (\<Squnion>i ia. F i (Y ia))"
proof -
  { assume "\<exists>a. (\<Squnion>n. F a (Y n)) \<noteq> F a (Lub Y)"
    have ?thesis
      by (simp add: cont cont2contlubE) }
  then show ?thesis
    by force
qed
  


lemma test14: assumes "(sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)"
        shows "chain Y \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)\<leadsto>(\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i))  \<bar> Oc f1 f2 \<sqsubseteq>
        (\<Squnion>i. (sbDom\<cdot>(Y i) = I f1 f2)\<leadsto>(\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i))  \<bar> Oc f1 f2)"
proof -
    have f1: "\<And>i. cont (\<lambda>x. iter_spfcompH2 f1 f2 i x)"
      by (simp) 
    hence f2: "chain Y \<longrightarrow> (\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i)) =  (\<Squnion> ia i.  iter_spfcompH2 f1 f2 ia (Y i))"
      by (rule test15)
    have f3: "\<forall>ia. chain Y \<longrightarrow>  sbDom\<cdot>(Y ia) = I f1 f2"
          proof -
            have "\<forall>i. chain Y \<longrightarrow> ( Y i) \<sqsubseteq> (\<Squnion>i. Y i)" 
              by (simp add: is_ub_thelub)
            hence "\<forall>i. chain Y \<longrightarrow> (sbDom\<cdot>(Y i)) = (sbDom\<cdot>(\<Squnion>i. Y i))"
             by (simp add: sbChain_dom_eq2)
           thus ?thesis
             by (simp add: assms(1))
         qed
    hence f4: "chain Y \<longrightarrow> (\<Squnion>i ia. iter_spfcompH2 f1 f2 i (Y ia))  \<sqsubseteq> (\<Squnion>i ia.  iter_spfcompH2 f1 f2 ia (Y i))"
      by(simp add: diag_lub ch2ch_cont f1 f2 f3 assms)
    hence f5: "chain Y \<longrightarrow> (\<Squnion>i ia. iter_spfcompH2 f1 f2 i (Y ia)) \<bar> Oc f1 f2  \<sqsubseteq> (\<Squnion>i ia.  iter_spfcompH2 f1 f2 ia (Y i)) \<bar> Oc f1 f2"
      using monofun_cfun_arg by blast
 
    have f20: "chain Y \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)\<leadsto>(\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i)) \<bar> Oc f1 f2
          = Some ((\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i)) \<bar> Oc f1 f2)"
      by (simp add: assms)
    have f21: "chain Y \<longrightarrow> (\<Squnion>i. (sbDom\<cdot>(Y i) = I f1 f2)\<leadsto>(\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i)) \<bar> Oc f1 f2 ) 
                = Some( (\<Squnion>i ia. iter_spfcompH2 f1 f2 ia (Y i)) \<bar> Oc f1 f2)"
      proof -
        have f211: "chain Y \<longrightarrow> (\<Squnion>i. (sbDom\<cdot>(Y i) = I f1 f2)\<leadsto>(\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i)) \<bar> Oc f1 f2)
                     = (\<Squnion>i. Some ((\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i))\<bar> Oc f1 f2))"
          by (simp add: f3 assms)
        have f212: "(\<Squnion>i. Some ((\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i))\<bar> Oc f1 f2))
                      =  Some( (\<Squnion>i ia. iter_spfcompH2 f1 f2 ia (Y i)) \<bar> Oc f1 f2)"
         sorry
        thus ?thesis
        using f211 by auto
      qed
      
    thus ?thesis
      by (simp add: f2 f20 f5 some_below)
qed

lemma test20: "chain Y \<longrightarrow>
        (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)\<leadsto>(\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i))  \<bar> Oc f1 f2  \<sqsubseteq>
        (\<Squnion>i. (sbDom\<cdot>(Y i) = I f1 f2)\<leadsto>(\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i))  \<bar> Oc f1 f2)"   
proof -
     have f1: "chain Y \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) \<noteq> I f1 f2) \<longrightarrow>
        (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)\<leadsto>(\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i))  \<bar> Oc f1 f2 \<sqsubseteq>
        (\<Squnion>i. (sbDom\<cdot>(Y i) = I f1 f2)\<leadsto>(\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i))  \<bar> Oc f1 f2)"
       by (smt below_refl is_ub_thelub po_class.chain_def sbChain_dom_eq2)
     moreover
       have f2: "chain Y \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2) \<longrightarrow>
        (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)\<leadsto>(\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i))  \<bar> Oc f1 f2 \<sqsubseteq>
        (\<Squnion>i. (sbDom\<cdot>(Y i) = I f1 f2)\<leadsto>(\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i))  \<bar> Oc f1 f2)"
         using test14 by blast
       thus ?thesis 
         using f1 f2 by blast
qed
 
lemma spf_comp_cont[simp]:
  "cont (\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) x) \<bar> Oc f1 f2)"
  apply (rule contI2)
  apply(simp)
    using test20 by blast



(*
BACKUPS 


      
lemma test35:
  shows "chain Y \<longrightarrow> (\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i)) =  (\<Squnion>i ia.  iter_spfcompH2 f1 f2 i (Y ia))"
proof -
  have f1:" \<And>i. cont (\<lambda>x. iter_spfcompH2 f1 f2 i x)"
    by(simp add: test15) 
  thus ?thesis
    by(rule test15)
qed



(\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i)) = (\<Squnion>i ia.  iter_spfcompH2 f1 f2 i (Y ia))

have "chain Y \<longrightarrow> sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2 \<longrightarrow> 
        ((\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i)) \<sqsubseteq>
        (\<Squnion>i. \<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i)))"
      apply (simp add: cont2contlubE)
      apply (simp add: diag_lub)
     apply (simp add: diag_lub ch2ch_cont)
       

 \<forall>Y. chain Y \<longrightarrow>
        (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)\<leadsto>\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i) \<sqsubseteq>
        (\<Squnion>i. (sbDom\<cdot>(Y i) = I f1 f2)\<leadsto>\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i)) 
\<forall>Y. chain Y \<longrightarrow> (\<Squnion>i ia. F i (Y ia)) = (\<Squnion>i. F i (\<Squnion>i. Y i))

lemma cont2cont_lub [simp]:
  assumes chain: "\<And>x. chain (\<lambda>i. F i x)" and cont: "\<And>i. cont (\<lambda>x. F i x)"
  shows "cont (\<lambda>x. \<Squnion>i. F i x)"
apply (rule contI2)
apply (simp add: monofunI cont2monofunE [OF cont] lub_mono chain)
apply (simp add: cont2contlubE [OF cont])
apply (simp add: diag_lub ch2ch_cont [OF cont] chain)
done

proof  -
  fix Y
  have "chain Y \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) \<noteq> I f1 f2) \<longrightarrow>
        (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)\<leadsto>\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i) \<sqsubseteq>
        (\<Squnion>i. (sbDom\<cdot>(Y i) = I f1 f2)\<leadsto>\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i))"
    by (smt below_refl is_ub_thelub po_class.chain_def sbChain_dom_eq2)
  have "chain Y \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2) \<longrightarrow>
        (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)\<leadsto>\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i) \<sqsubseteq>
        (\<Squnion>i. (sbDom\<cdot>(Y i) = I f1 f2)\<leadsto>\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i))"
  proof -
    have f1: "chain Y \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2) \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)\<leadsto>\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i)
          = Some (\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i))"
      by simp
    have "chain Y \<longrightarrow> sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2 \<longrightarrow> 
        ((\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i)) =
        (\<Squnion>i ia. iter_spfcompH2 f1 f2 i (Y ia)))"
     oops


lemma test35:
  shows "chain Y \<longrightarrow> (\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i)) =  (\<Squnion>i ia.  iter_spfcompH2 f1 f2 i (Y ia))"
proof -
  have f1:" \<And>i. cont (\<lambda>x. iter_spfcompH2 f1 f2 i x)"
    by(simp add: test15) 
  hence f2: ""
  thus ?thesis
    by(rule test15)

*)
end