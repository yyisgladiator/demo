(*  Title:  SerComp_JB.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: additional  lemmas for composition, especially monofun and cont proof for spfComp
*)

theory SPF_Composition_JB
imports SPF SB SPF_Templates
begin

(* ----------------------------------------------------------------------- *)
section \<open>general lemmas\<close>
(* ----------------------------------------------------------------------- *)
  
subsection \<open>sbdom\<close>  

(* The sbDom of the lub of a chain is equals to the sbDom of every chain link *)
  (* Used in cont proof of spfcomp *)
lemma sbdom_lub_eq: assumes "chain Y" 
                    and  "(sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)"
  shows "\<forall>ia. sbDom\<cdot>(Y ia) = I f1 f2"
proof -
  have "\<forall>i. ( Y i) \<sqsubseteq> (\<Squnion>i. Y i)" 
    by (simp add: is_ub_thelub assms(1))
  have "\<forall>i. (sbDom\<cdot>(Y i)) = (sbDom\<cdot>(\<Squnion>i. Y i))"
   by (simp add: sbChain_dom_eq2 assms(1))
 thus ?thesis
   by (simp add: assms(2))
qed  
  
  
subsection \<open>Some\<close>  
  
(* Some can be pulled out when applied to a chain *)  
lemma some_lub_chain_eq: fixes Y :: "nat \<Rightarrow> 'a::cpo"
            assumes "chain Y"
            shows " Some (\<Squnion> i. Y i) = (\<Squnion> i. Some (Y i))"
  using assms cont2contlubE some_cont by blast
    
lemma some_lub_chain_eq3: fixes Y :: "nat \<Rightarrow> 'a::cpo"
            assumes "chain Y"
            shows "(\<Squnion> i. Some (Y i)) = Some (\<Squnion> i. Y i)"
 by (simp add: some_lub_chain_eq assms)

(* Some can be pulled out when applied to a function which is applied to a chain *)   
lemma some_lub_chain_eq2: fixes Y:: "nat \<Rightarrow> 'a::cpo"
             fixes f:: "'a \<Rightarrow> 'b::cpo"
             assumes "chain (\<lambda>i. f (Y i))"
             shows " Some (\<Squnion> i. f (Y i)) = (\<Squnion> i. Some (f (Y i)))"
  using assms(1) some_lub_chain_eq by blast

    
subsection \<open>Lub\<close>     
    
(* two lubs can be merged together if a function F is cont in x for every i *)
lemma cont2lub_lub_eq: assumes cont: "\<And>i. cont (\<lambda>x. F i x)" 
  shows "chain Y\<longrightarrow>  (\<Squnion>i. F i (\<Squnion>i. Y i)) = (\<Squnion>i ia. F i (Y ia))"
proof -
  { assume "\<exists>a. (\<Squnion>n. F a (Y n)) \<noteq> F a (Lub Y)"
    have ?thesis
      by (simp add: cont cont2contlubE) }
  then show ?thesis
    by force
qed
  
subsection \<open>NEW\<close>
  (* TODO port general lemmas to corresponding production theories! ! ! *)
  
lemma lub_suc_shift: fixes Y:: "nat \<Rightarrow> 'a::cpo" assumes "chain Y"
  shows "(\<Squnion>i. Y (Suc i)) = (\<Squnion>i. Y i)"
proof-
  have f1: "(\<Squnion>i. Y (Suc i)) = (\<Squnion>i. Y (i + 1))"
    by auto
  thus ?thesis
    apply (subst f1)
    by (subst lub_range_shift, simp_all add: assms)
qed
  
      
(* two chain lubs are equal if one is the shifted by one version of the other *)
lemma lub_suc_shift_eq: fixes Y:: "nat \<Rightarrow> 'a::cpo" fixes Z:: "nat \<Rightarrow> 'a::cpo" 
              assumes "chain Y" and "chain Z" 
              and "\<And> i. (Y (Suc i) = Z (Suc (Suc(i))))"
shows "(\<Squnion>i. (Y i)) = (\<Squnion>i. (Z i))"
proof -  
  have f1: "(\<Squnion>i. (Y (Suc(i)))) = (\<Squnion>i. (Z i))"
    apply (simp only: assms(3))
    apply (subst lub_suc_shift)
    using assms(2) po_class.chain_def 
    apply blast
    by (subst lub_suc_shift, simp_all add: assms)
      
  have f2: "(\<Squnion>i. Y (Suc i)) = (\<Squnion>i. Y i)"
    by (simp add: assms(1) lub_suc_shift)
  thus ?thesis
    by (simp add: f1)
qed
  
(* two interleaved chains have the same least upper bound *)
lemma lub_interl_chain_eq:  fixes Y:: "nat \<Rightarrow> 'a::cpo" fixes Z:: "nat \<Rightarrow> 'a::cpo" 
  assumes "\<And> i. Y i \<sqsubseteq> Z i" and "\<And> i. Z i \<sqsubseteq> Y (Suc i)"
  shows "(\<Squnion>i. (Y i)) = (\<Squnion>i. (Z i))"
proof -
  have f1: "(\<Squnion>i. (Y i)) \<sqsubseteq> (\<Squnion>i. (Z i))"
    by (meson assms(1) assms(2) below_trans lub_mono po_class.chain_def)
  moreover 
  have f2: "(\<Squnion>i. (Z i)) \<sqsubseteq> (\<Squnion>i. (Y i))"
  proof (rule ccontr)
    assume "\<not> ((\<Squnion>i. (Z i)) \<sqsubseteq> (\<Squnion>i. (Y i)))"
    then show False
      by (meson assms(1) assms(2) below_lub lub_below_iff po_class.chain_def rev_below_trans)
  qed
  ultimately    
  show ?thesis
    by (simp add: below_antisym)
qed
  
lemma sbunion_pref_eq2: assumes "(a \<sqsubseteq> b)"
  shows "(x \<uplus> a \<sqsubseteq> x \<uplus> b)"
     by (metis assms monofun_cfun_arg)
  
lemma sbunion_assoc2: "(sb1 \<uplus> sb2) \<uplus> sb3 = sb1 \<uplus> (sb2 \<uplus> sb3)"
  by (simp add: sbunion_associative)
    
lemma spf_pref_eq: assumes "(a \<sqsubseteq> b)"
  shows "f \<rightleftharpoons> a \<sqsubseteq> f \<rightleftharpoons> b"
  by (metis Rep_CSPF_def assms cont2mono monofun_cfun_arg monofun_def op_the_cont)
    
lemma sbunion_pref_eq: assumes "(a \<sqsubseteq> b)" and "(c \<sqsubseteq> d)"
  shows "(a \<uplus> c \<sqsubseteq> b \<uplus> d)"
  by (simp add: assms(1) assms(2) monofun_cfun)
    
lemma sbres_pref_eq: assumes "(a \<sqsubseteq> b)"
  shows "(a \<bar> cs) \<sqsubseteq> (b \<bar> cs)"
     by (metis assms monofun_cfun_arg)
  
       
(* ----------------------------------------------------------------------- *)
section \<open>definitions\<close>
(* ----------------------------------------------------------------------- *)
(* abbrv for the part behind  \<leadsto> in spfcomp but without the restriction to Oc *) 
abbreviation iter_spfcompH2 :: "'a SPF \<Rightarrow> 'a SPF \<Rightarrow> nat \<Rightarrow> 'a SB  \<Rightarrow> 'a SB" where
"(iter_spfcompH2 f1 f2 i) \<equiv> (\<lambda> x. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"  


(* newer spfcopmp definition: input is not iterated *)
definition spfCompH3 :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SB \<Rightarrow> 'm SB  \<rightarrow> 'm SB" where
"spfCompH3 f1 f2 x \<equiv> (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f2)))"


abbreviation iter_spfCompH3 :: "'a SPF \<Rightarrow> 'a SPF \<Rightarrow> nat \<Rightarrow> 'a SB  \<Rightarrow> 'a SB" where
"(iter_spfCompH3 f1 f2 i) \<equiv> (\<lambda> x. iterate i\<cdot>(spfCompH3 f1 f2 x)\<cdot>((spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)^\<bottom>))" 


(* adds the input to the original sbFix definition *)
  (* makes old sbfix obsolete *)
definition sbFix2 :: "('m SB \<Rightarrow> 'm SB \<rightarrow> 'm SB) \<Rightarrow> 'm SB  \<Rightarrow> channel set \<Rightarrow> 'm SB" where
"sbFix2 F x cs \<equiv>  (\<Squnion>i. iterate i\<cdot>(F x)\<cdot>(cs^\<bottom>))"

abbreviation iter_sbfix:: "('m SB \<Rightarrow> 'm SB \<rightarrow> 'm SB) \<Rightarrow> nat \<Rightarrow> channel set \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
"iter_sbfix F i cs \<equiv> (\<lambda> x. iterate i\<cdot>(F x)\<cdot>(cs^\<bottom>))"

abbreviation sbfun_io_eq :: "('m SB \<rightarrow> 'm SB)  \<Rightarrow> channel set \<Rightarrow> bool" where
"sbfun_io_eq f cs \<equiv> sbDom\<cdot>(f\<cdot>(cs^\<bottom>)) = cs"
       
(* ----------------------------------------------------------------------- *)
section \<open>spfCompHelp2\<close>
(* ----------------------------------------------------------------------- *) 

(* The actual definition of spfcomp is equal to more proof friendly notation with spfCompHelp2 *)
lemma spfcomp_tospfH2: "(spfcomp f1 f2) 
                   = Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> 
                      (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2)"
  apply (subst spfcomp_def, subst spfCompHelp2_def, subst C_def I_def Oc_def)
  by (metis (no_types) C_def I_def Oc_def)

    
lemma spfCompH2_mono[simp]: "monofun (\<lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> spfDom\<cdot>f1)) 
                                             \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> spfDom\<cdot>f2)))"
  using cont2mono spfCompHelp_cont by blast

lemma spfCompH2_cont[simp]: "cont (\<lambda> z. x \<uplus> ((Rep_CSPF f1)\<rightharpoonup>(z \<bar> spfDom\<cdot>f1)) 
                                          \<uplus> ((Rep_CSPF f2)\<rightharpoonup>(z \<bar> spfDom\<cdot>f2)))"
  using spfCompHelp_cont by blast

(* spfCompHelp2 is montone in x independent from the input *)
lemma helpermonoinX: shows "monofun (\<lambda> x. spfCompHelp2 f1 f2 x)"
  by (simp add: spfCompHelp2_def)

(* spfCompHelp2 is cont in x independent from the input *)
lemma helpercontinX[simp]: shows "cont (\<lambda> x. spfCompHelp2 f1 f2 x)"
  proof -
     have "\<forall>x. cont (\<lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1))  \<uplus> (f2 \<rightleftharpoons>(z \<bar> spfDom\<cdot>f2)))"
     by simp
     hence "cont (\<lambda>x. \<Lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1))  \<uplus> (f2 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f2)))"
       by (simp add: cont2cont_LAM)
     thus ?thesis
       by (simp add: spfCompHelp2_def)
  qed

 
    
(* ----------------------------------------------------------------------- *)
section \<open>iter_spfCompHelp2\<close>
(* ----------------------------------------------------------------------- *) 
  



(* for all i the i'th iteration on spfcomp is cont as application iterate is cont on cont fun *) 
lemma iter_spfcompH2_cont2[simp]: "cont (\<lambda>x. iter_spfcompH2 f1 f2 i x)"
  by simp
    
lemma iter_spfcompH2_mono[simp]:  "monofun 
                                      (\<lambda> x. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"
  by (simp add: cont2mono)
    
(* replaced spfComp_serialnf_chain *)
lemma iter_spfcompH2_chain[simp]: assumes "sbDom\<cdot>x = I f1 f2"
  shows "chain (\<lambda>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"
  apply (rule sbIterate_chain)
  apply (simp add: assms C_def I_def)
  by blast
        


(* ----------------------------------------------------------------------- *)
section \<open>lub_iter_spfCompHelp2\<close>
(* ----------------------------------------------------------------------- *) 
  
subsection \<open>mono\<close>  

(* the lub over the iterations of spfcompH2 is monotone if the assumtions hold *)
  (* requires chain property, hence the input must have the right domain *)
lemma lub_iter_spfCompHelp2_mono_req: assumes "x \<sqsubseteq> y" and  "sbDom\<cdot>x = I f1 f2"
  shows "(\<Squnion>i.(iter_spfcompH2 f1 f2 i) x) \<sqsubseteq> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) y)"
  proof-
    have  "\<forall>i. ((iter_spfcompH2 f1 f2 i) x) \<sqsubseteq> ((iter_spfcompH2 f1 f2 i) y)"
      using assms monofun_def by fastforce
    moreover
    have "sbDom\<cdot>y = sbDom\<cdot>x"
      by (metis assms(1) sbdom_eq)
    ultimately
    (* if for each iteration the left side is smaller than the right one, so must be the lubs *)
    show ?thesis
       by (simp add: assms(2) iter_spfcompH2_chain lub_mono)
   qed

(* the lub over the iteration is always mono, the correct domain is assured via \<leadsto> *)
lemma if_lub_iter_spfCompHelp2_mono_req: assumes "x \<sqsubseteq> y" 
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

(* the lub of iter_spfcompH2, when applied to a chain, is again a chain *)
  (* this property follows from the monotonicy of lub_iter_spfCompHelp2 *)
lemma chain_lub_iter_spfcompH2: assumes  "chain Y" 
                                and  "(sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)"
  shows "chain (\<lambda>i. \<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i))"   
  proof -
    have f1: "\<forall>i. (Y i) \<sqsubseteq> (Y (Suc i))"
      using assms po_class.chain_def by blast
    have f2: "\<forall>ia. sbDom\<cdot>(Y ia) = I f1 f2"
      by (simp add: sbdom_lub_eq assms)
    thus ?thesis
      apply (subst chainI, simp_all)
      using  sbdom_lub_eq f1 lub_iter_spfCompHelp2_mono_req by blast
  qed
    

  
(* ----------------------------------------------------------------------- *)
section \<open>spfComp\<close>
(* ----------------------------------------------------------------------- *) 
  
subsection \<open>mono\<close>  

(* Show that spfComp is monofun in x independent from the function it's applied to *)
  (* Used in cont proof, hence must be proofed independently *)
lemma spf_comp_mono[simp]: "monofun (\<lambda> x. (sbDom\<cdot>x = I f1 f2) 
                                          \<leadsto> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) x)  \<bar> Oc f1 f2 )" 
  proof -
    have "monofun (\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) x) )"
      by (metis (no_types, lifting) lub_eq monofun_def if_lub_iter_spfCompHelp2_mono_req)
    thus ?thesis
      by (smt monofun_cfun_arg monofun_def sbdom_eq some_below some_below2)
  qed

    
subsection \<open>cont\<close>   
(* General proof Idea: show that part behind \<leadsto> is cont if input has correct domain and otherwise. 
   This procedure is necessary as the chain properties of iter_spcompH2 only hold if the input 
   domain is correct *)
  
(* Show that 2nd goal from contI holds if input on spfcomp has the correct domain *)     
lemma chain_if_lub_iter_spfcompH2_domI: assumes "(sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)"
  shows "chain Y \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)
                              \<leadsto>(\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i))  \<bar> Oc f1 f2 
                      \<sqsubseteq> (\<Squnion>i. (sbDom\<cdot>(Y i) = I f1 f2)
                              \<leadsto>(\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i))  \<bar> Oc f1 f2)"
  proof -
      (* Part I: Show that part after \<leadsto> has 2nd property of compI *)
      have f1: "\<And>i. cont (\<lambda>x. iter_spfcompH2 f1 f2 i x)"
        by (simp) 
      hence f2: "chain Y \<longrightarrow> (\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i)) 
                              = (\<Squnion> ia i.  iter_spfcompH2 f1 f2 ia (Y i))"
        by (rule cont2lub_lub_eq)
      moreover
      have f3: "\<forall>ia. chain Y \<longrightarrow>  sbDom\<cdot>(Y ia) = I f1 f2"
        by (simp add: sbdom_lub_eq assms)
      ultimately
      have f4: "chain Y \<longrightarrow> (\<Squnion>i ia. iter_spfcompH2 f1 f2 i (Y ia))  
                              \<sqsubseteq> (\<Squnion>i ia.  iter_spfcompH2 f1 f2 ia (Y i))"
        by (simp add: diag_lub ch2ch_cont f1 f2 f3 assms)
          (* now show that property also holds if result is restricted to Oc *)
      hence f5: "chain Y \<longrightarrow> (\<Squnion>i ia. iter_spfcompH2 f1 f2 i (Y ia)) \<bar> Oc f1 f2  
                              \<sqsubseteq> (\<Squnion>i ia.  iter_spfcompH2 f1 f2 ia (Y i)) \<bar> Oc f1 f2"
        using monofun_cfun_arg by blast
   
      (*  Part II: Show that Some packaging does not change \<sqsubseteq> relation from before*)    
      have f10: "chain Y \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)
                                            \<leadsto>(\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i)) \<bar> Oc f1 f2
            = Some ((\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i)) \<bar> Oc f1 f2)"
        by (simp add: assms)
      have f11: "chain Y \<longrightarrow> (\<Squnion>i. (sbDom\<cdot>(Y i) = I f1 f2)
                                            \<leadsto>(\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i)) \<bar> Oc f1 f2) 
                  = Some((\<Squnion>i ia. iter_spfcompH2 f1 f2 ia (Y i)) \<bar> Oc f1 f2)"
        proof -
          have f111: "chain Y \<longrightarrow> (\<Squnion>i. (sbDom\<cdot>(Y i) = I f1 f2)
                                             \<leadsto>(\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i)) \<bar> Oc f1 f2)
                       = (\<Squnion>i. Some ((\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i))\<bar> Oc f1 f2))"
            by (simp add: f3 assms)
          (* with chain_lub_iter_spfcompH2 some can now be pulled out *)
          have f212: "chain Y \<longrightarrow> (\<Squnion>i. Some ((\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i))\<bar> Oc f1 f2))
                        = Some((\<Squnion>i ia. iter_spfcompH2 f1 f2 ia (Y i)) \<bar> Oc f1 f2)"
             by (simp add: contlub_cfun_arg some_lub_chain_eq chain_lub_iter_spfcompH2 assms)
              thus ?thesis
          using f111 by auto
      qed   
        (* PART III: as Some on both sides can be pulled out (Part II) the thesis follows 
            directly with Part I *)
      thus ?thesis
        by (simp add: f2 f10 f5 some_below)
  qed

    
(* Show that 2nd goal from contI holds independent from the input *)    
lemma chain_if_lub_iter_spfcompH2: "chain Y \<longrightarrow>
        (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)\<leadsto>(\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i))  \<bar> Oc f1 f2  \<sqsubseteq>
        (\<Squnion>i. (sbDom\<cdot>(Y i) = I f1 f2)\<leadsto>(\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i))  \<bar> Oc f1 f2)"   
  proof -
       have case1: "chain Y \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) \<noteq> I f1 f2) \<longrightarrow>
          (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)\<leadsto>(\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i))  \<bar> Oc f1 f2 \<sqsubseteq>
          (\<Squnion>i. (sbDom\<cdot>(Y i) = I f1 f2)\<leadsto>(\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i))  \<bar> Oc f1 f2)"
         by (smt below_refl is_ub_thelub po_class.chain_def sbChain_dom_eq2)
       moreover
       have case2: "chain Y \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2) \<longrightarrow>
        (sbDom\<cdot>(\<Squnion>i. Y i) = I f1 f2)\<leadsto>(\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i))  \<bar> Oc f1 f2 \<sqsubseteq>
        (\<Squnion>i. (sbDom\<cdot>(Y i) = I f1 f2)\<leadsto>(\<Squnion>ia. iter_spfcompH2 f1 f2 ia (Y i))  \<bar> Oc f1 f2)"
         using chain_if_lub_iter_spfcompH2_domI by blast
         thus ?thesis 
           using case1 case2 by blast
  qed

(* Show that spfComp is cont in x independent from the function it's applied to *)
(* I cannot believe I finally proved this :) *)
lemma spf_comp_cont[simp]:
  "cont (\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) x) \<bar> Oc f1 f2)"
  apply (rule contI2)
  apply (simp)
    using chain_if_lub_iter_spfcompH2 by blast

lemma iter_spfcompH2_ran[simp]: assumes "sbDom\<cdot>b = I f1 f2"
  shows  "sbDom\<cdot>(\<Squnion>i. iter_spfcompH2 f1 f2 i b) = C f1 f2"
  by (metis (mono_tags, lifting) I_commu assms iter_spfcompH2_chain lub_eq sbChain_dom_eq2 
      spfCompHelp2_iter_dom)
 
lemma spf_comp_well[simp]: 
  "spf_well (\<Lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) x) \<bar> Oc f1 f2)"
  apply (simp add: spf_well_def)
  apply (simp only: domIff2)
  apply (simp add: sbdom_rep_eq)
      by (auto)  

                                
(* used abbreviations are equal to comp function *)
   (* together with the lemma  spfcomp_tospfH2, the complete equality with spfcomp is proven *)
lemma spfcomp_abbrv_tospfH2: "(\<lambda> x. (sbDom\<cdot>x = I f1 f2) 
                                \<leadsto> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) x) \<bar> Oc f1 f2)
                       = (\<lambda> x. (sbDom\<cdot>x = I f1 f2) 
                          \<leadsto> (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2)"      
  by simp
    
lemma spfcomp_abbrv_tospfH22: "(spfcomp f1 f2)
                       = Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I f1 f2) 
                          \<leadsto> (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2)"      
  by (simp add: spfcomp_tospfH2)
          
    
lemma spfComp_ran: assumes "spfRan\<cdot>f1 \<inter> spfRan\<cdot>f2 = {}" 
  shows "spfRan\<cdot>(spfcomp f1 f2) = Oc f1 f2"
   apply (simp add: spfcomp_def)  
   oops

     
(* ----------------------------------------------------------------------- *)
section \<open>spfcomp2\<close>
(* ----------------------------------------------------------------------- *)




subsection \<open>spfCompHelp3\<close>
  
subsubsection \<open>cont\<close>
  
lemma spfCompH3_cont[simp]: 
  shows "cont (\<lambda> z. (f1\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f2)))"
proof -
  have f1: "cont (\<lambda> z. (Rep_cfun (Rep_SPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f1)))"
    by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
  moreover 
  have f2: "cont (\<lambda> z. (Rep_cfun (Rep_SPF f2)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f2)))"
    by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
  ultimately
  have "cont (\<lambda>z. sbUnion\<cdot>(Rep_cfun (Rep_SPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f1))) 
        \<and> cont (\<lambda>z. Rep_SPF f2\<cdot>((x \<uplus> z)\<bar>spfDom\<cdot>f2))"
    by simp
  hence "cont (\<lambda> z. (Rep_cfun (Rep_SPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f1)) 
                          \<uplus> (Rep_cfun (Rep_SPF f2)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f2)))"
    using cont2cont_APP cont_compose op_the_cont by blast
  thus ?thesis
    by (simp add: Rep_CSPF_def)
qed
  
lemma spfCompH3_cont2[simp]: 
  shows "cont (\<lambda> x. (f1\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f2)))"
proof -
  have f0: "cont (\<lambda>x. (x \<uplus> z))"
    by simp
      
  have f1: "cont (\<lambda> x. (Rep_cfun (Rep_SPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f1)))"
    by (metis (no_types) f0 cont_Rep_cfun2 cont_compose op_the_cont)
  moreover
  have f2: "cont (\<lambda> x. (Rep_cfun (Rep_SPF f2)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f2)))"
    by (metis (no_types) f0 cont_Rep_cfun2 cont_compose op_the_cont)
  ultimately
  have "cont (\<lambda>x. sbUnion\<cdot>(Rep_cfun (Rep_SPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f1))) 
        \<and> cont (\<lambda>x. Rep_SPF f2\<cdot>((x \<uplus> z)\<bar>spfDom\<cdot>f2))"
    by simp
  hence "cont (\<lambda> x. (Rep_cfun (Rep_SPF f1)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f1)) 
                                                   \<uplus> (Rep_cfun (Rep_SPF f2)\<rightharpoonup>((x \<uplus> z)\<bar>spfDom\<cdot>f2)))"
    using cont2cont_APP cont_compose op_the_cont by blast
  thus ?thesis
    by (simp add: Rep_CSPF_def)
qed
  
  
lemma spfCompH3_continX[simp]: "cont (\<lambda> x. spfCompH3 f1 f2 x)"
proof -
  have "cont (\<lambda> x. \<Lambda> z. ((f1\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f2))))"
    by (simp add: cont2cont_LAM)
  thus ?thesis
    by (simp add: spfCompH3_def)
qed
  
      
  
subsubsection \<open>dom\<close>
  
lemma spfCompH3_dom [simp]: assumes "sbDom\<cdot>x = I f1 f2"
                            and "sbDom\<cdot>sb = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
                          shows "sbDom\<cdot>((spfCompH3 f1 f2 x)\<cdot>sb) = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
proof -
  have f1: "sbDom\<cdot>(f1 \<rightleftharpoons> ((x \<uplus> sb)  \<bar> spfDom\<cdot>f1)) = spfRan\<cdot>f1"
    by (simp add: I_def assms(1) assms(2) inf_sup_aci(6))
      moreover
  have f2: "sbDom\<cdot>(f2 \<rightleftharpoons> ((x \<uplus> sb)  \<bar> spfDom\<cdot>f2)) = spfRan\<cdot>f2"
    by (simp add: I_def assms(1) assms(2) sup.coboundedI1)
      ultimately
  show ?thesis
    by (simp add: f1 f2 spfCompH3_def assms)
qed
  

subsection \<open>iter_spfCompH3\<close>
  
lemma iter_spfCompH3_cont[simp]: "cont (\<lambda>x. iter_spfCompH3 f1 f2 i x)"
  by simp
    
lemma iter_spfCompH3_mono[simp]: "monofun (\<lambda>x. iter_spfCompH3 f1 f2 i x)"
  by (simp add: cont2mono)
    
lemma iter_spfCompH3_mono2:  assumes "x \<sqsubseteq> y"
  shows "\<forall>i. ((iter_spfCompH3 f1 f2 i) x) \<sqsubseteq> ((iter_spfCompH3 f1 f2 i) y)"
  using assms monofun_def by fastforce
  
lemma iter_spfCompH3_chain[simp]: assumes "sbDom\<cdot>x = I f1 f2"
  shows "chain (\<lambda> i. iter_spfCompH3 f1 f2 i x)"
  apply (rule sbIterate_chain)
  by (simp add: assms)
    
lemma iter_spfCompH3_dom[simp]: assumes "sbDom\<cdot>x = I f1 f2" 
  shows "sbDom\<cdot>(iter_spfCompH3 f1 f2 i x) = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
  apply (induct_tac i)
   apply auto[1]
  by (simp add: assms)
    
    
subsection \<open>lub_iter_spfCompH3\<close>
  
lemma lub_iter_spfCompH3_dom[simp]: assumes "sbDom\<cdot>x = I f1 f2" 
  shows "sbDom\<cdot>(\<Squnion>i. iter_spfCompH3 f1 f2 i x) = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
    by (metis (mono_tags, lifting) assms iter_spfCompH3_chain iter_spfCompH3_dom sbChain_dom_eq2)
    
    
subsection \<open>old2new spfcomp eq\<close>

  
lemma iter_spfCompH3_px_chain[simp]: assumes "sbDom\<cdot>x = I f1 f2"
  shows "chain (\<lambda> i. x \<uplus> iter_spfCompH3 f1 f2 i x)"
  by (simp add: assms)
    
lemma lub_iter_spfCompH3_eq: assumes "sbDom\<cdot>x = I f1 f2"
  shows "((\<Squnion>i. ( x \<uplus> iter_spfCompH3 f1 f2 i x))\<bar> Oc f1 f2) = (\<Squnion>i. (iter_spfCompH3 f1 f2 i) x)"
proof -
  have f1: "(\<Squnion>i. ( x \<uplus> iter_spfCompH3 f1 f2 i x)) = x \<uplus> (\<Squnion>i. iter_spfCompH3 f1 f2 i x)"
    by (simp add: assms contlub_cfun_arg)
  thus ?thesis
    by (simp add: assms lub_iter_spfCompH3_dom Oc_def)
qed
 
  
  
lemma lub_iter_spfCompH2_spfCompH3wX_eq_req_1: assumes "sbDom\<cdot>x = I f1 f2" 
  shows "(iter_spfcompH2 f1 f2 i x) \<sqsubseteq> (x \<uplus> (iter_spfCompH3 f1 f2 i x))"
proof (induction i)
  case 0
  then show ?case
    by (simp add: C_def I_def assms sup.assoc)
next
  case (Suc i)
  then show ?case     
    apply (unfold iterate_Suc)
    apply (subst spfCompHelp2_def, subst spfCompH3_def)
    apply (auto)
    apply (subst sbunion_assoc2, rule sbunion_pref_eq2) (* remove x *)
    apply (rule sbunion_pref_eq) (* split up sbunion *)
     apply (rule spf_pref_eq, rule sbres_pref_eq, simp)
     by (rule spf_pref_eq, rule sbres_pref_eq, simp)    
qed


lemma lub_iter_spfCompH2_spfCompH3wX_eq_req_2: assumes "sbDom\<cdot>x = I f1 f2"  
  shows "(x \<uplus> iter_spfCompH3 f1 f2 i x) \<sqsubseteq> (iter_spfcompH2 f1 f2 (Suc i) x)"
proof (induction i)
  case 0
  then show ?case
    apply (simp add: spfCompHelp2_def)
    apply (subst sbunion_assoc2, subst sbunion_pref_eq2)
    apply (simp_all add: assms)
    by (metis (no_types, lifting) C_def sbleast_least sbleast_sbdom sbunionDom 
               spfRanRestrict sup.bounded_iff sup.cobounded1)   
next
  case (Suc i)
  then show ?case
    apply (unfold iterate_Suc)
    apply (subst spfCompHelp2_def, subst spfCompH3_def)
    apply (auto)
    apply (subst sbunion_assoc2, rule sbunion_pref_eq2)
    apply (rule sbunion_pref_eq)
     apply (rule spf_pref_eq, rule sbres_pref_eq, simp)
     by (rule spf_pref_eq, rule sbres_pref_eq, simp)
qed

  

  
lemma lub_iter_spfCompH2_spfCompH3wX_eq: assumes "sbDom\<cdot>x = I f1 f2" 
  shows "(\<Squnion>i. (iter_spfcompH2 f1 f2 i x)) = (\<Squnion>i. ( x \<uplus> iter_spfCompH3 f1 f2 i x))"
  by (meson assms lub_interl_chain_eq lub_iter_spfCompH2_spfCompH3wX_eq_req_1 
      lub_iter_spfCompH2_spfCompH3wX_eq_req_2)

    
    
lemma lub_iter_spfCompH2_spfCompH3_eq: assumes "sbDom\<cdot>x = I f1 f2" 
  shows "(\<Squnion>i. (iter_spfCompH3 f1 f2 i) x)  = (\<Squnion>i. (iter_spfcompH2 f1 f2 i x))  \<bar> Oc f1 f2"
  using assms lub_iter_spfCompH2_spfCompH3wX_eq lub_iter_spfCompH3_eq by fastforce
    
    
(* both definitions of spfcomp are equal independent from the input *)
lemma spfcomp_and_spfcomp2_eq_req: "(sbDom\<cdot>x = I f1 f2) \<leadsto> (\<Squnion>i. (iter_spfCompH3 f1 f2 i) x) 
                            =(sbDom\<cdot>x = I f1 f2) \<leadsto> ((\<Squnion>i. (iter_spfcompH2 f1 f2 i x))  \<bar> Oc f1 f2)"
proof (cases "sbDom\<cdot>x = I f1 f2")
  case True
  then show ?thesis
    by (simp add: lub_iter_spfCompH2_spfCompH3_eq)
next
  case False
  then show ?thesis
    by simp
qed
 
  
(* show that new definition is cont and spf_well based on the proof for the old one *)
lemma spf_compH3_cont[simp]: 
  shows "cont (\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> (\<Squnion>i. (iter_spfCompH3 f1 f2 i) x))"
  apply (subst spfcomp_and_spfcomp2_eq_req)
  by simp
    
lemma spf_compH3_well[simp]: 
  shows "spf_well (\<Lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> (\<Squnion>i. (iter_spfCompH3 f1 f2 i) x))"
  apply (subst spfcomp_and_spfcomp2_eq_req)
  by simp


(* used abbreviations are equal to spfcomp2 function *)   
    (* Substitute with this lemma if you need cont properties for spfcomp *)
lemma spfcompH3_abbrv_tospfH32: "(spfcomp2 f1 f2)
                       = Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I f1 f2) 
                          \<leadsto>  (\<Squnion>i. iterate i\<cdot>(spfCompH3 f1 f2 x)\<cdot>((spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)^\<bottom>)))" 
  apply (simp add: spfcomp2_def)
  apply (subst spfCompH3_def)
    by simp
    
(* both definitions deliver an equal result *)
lemma spfcomp_and_spfcomp2_eq: "(spfcomp f1 f2) = (spfcomp2 f1 f2)"
  apply (subst spfcomp_abbrv_tospfH22)
  apply (subst spfcompH3_abbrv_tospfH32)
  by (simp add: spfcomp_and_spfcomp2_eq_req)
    
    
  
(* ----------------------------------------------------------------------- *)
section \<open>sbFix\<close>
(* ----------------------------------------------------------------------- *) 
  
(* the proof strategy is very similar to the one in SPF_Feedback_JB *)




lemma sbfix2_iter_eq: "sbFix2 F x cs = (\<Squnion>i. iter_sbfix F i cs x)"
  by (simp add: sbFix2_def)
    

    
subsection \<open>iter_sbfix\<close>
  
lemma iter_sbfix_cont[simp]: assumes "cont F"
 shows "cont (\<lambda> x. iter_sbfix F i cs x)"
  by (simp add: assms)
    
lemma iter_sbfix_mono[simp]: assumes "cont F"
 shows "monofun (\<lambda> x. iter_sbfix F i cs x)"
  by (simp add: assms cont2mono)
    
    
lemma iter_sbfix_mono2: assumes "cont F" and "x \<sqsubseteq> y"
  shows "\<forall>i . (iter_sbfix F i cs x) \<sqsubseteq> (iter_sbfix F i cs y)"
  by (simp add: assms(1) assms(2) cont2monofunE monofun_cfun_fun)
    
lemma iter_sbfix_chain: assumes "sbfun_io_eq (F x) cs"
  shows "chain (\<lambda>i. iter_sbfix F i cs x)"
    apply (rule sbIterate_chain)
  by (simp add: assms)
    
lemma iter_sbfix_dom: assumes "sbfun_io_eq (F x) cs"
  shows "sbDom\<cdot>(iter_sbfix F i cs x) =  sbDom\<cdot>((F x)\<cdot>(cs^\<bottom>))"
  apply (induct_tac i)
   apply (simp_all add: assms)
  by (metis (no_types, lifting) assms cfcomp2 cfcomp2 monofun_cfun_arg rev_below_trans 
            sbdom_eq sbleast_least sbleast_sbdom sbtake_zero)
          
 
subsection \<open>lub_iter_sbfix\<close>

subsubsection \<open>mono\<close>
  
lemma lub_iter_sbfix_mono_req: assumes "x \<sqsubseteq> y" and "cont F" and "sbfun_io_eq (F x) cs"
  shows "(\<Squnion>i. (iter_sbfix F i cs) x) \<sqsubseteq> (\<Squnion>i. (iter_sbfix F i cs) y)"
proof -
  have "\<forall>i. ((iter_sbfix F i cs) x) \<sqsubseteq> ((iter_sbfix F i cs) y)"
    by (simp add: iter_sbfix_mono2 assms(1) assms(2))
  moreover
  have "sbDom\<cdot>x = sbDom\<cdot>y"
    using assms(1) sbdom_eq by auto
  moreover
  have "sbfun_io_eq (F y) cs"
    by (metis assms(1) assms(2) assms(3) cont2monofunE monofun_cfun_fun sbdom_eq)
  ultimately
  show ?thesis
    by (simp add: lub_mono assms iter_sbfix_mono2 iter_sbfix_chain)
qed
  
(* TODO: if lub mono lemmas *)
  
subsubsection \<open>cont\<close>
  
lemma chain_lub_iter_sbfix: assumes "chain Y" and "cont F" and "sbfun_io_eq (F (\<Squnion>i. Y i)) cs"
  shows "chain (\<lambda>i. \<Squnion>ia. iter_sbfix F ia cs (Y i))"
proof -
  have f1: "\<forall>i. (Y i) \<sqsubseteq> (Y (Suc i))"
    using assms(1) po_class.chain_def by blast
  have f2: "\<forall>ia. sbfun_io_eq (F (Y ia)) cs"
    proof -
      have "(\<Squnion>n. F (Y n)\<cdot>(cs^\<bottom>)) = F (Lub Y)\<cdot>(cs^\<bottom>)"
      by (metis (no_types) assms(1) assms(2) ch2ch_cont cont2contlubE contlub_cfun_fun)
    thus ?thesis
      by (metis (no_types) assms(1) assms(2) assms(3) ch2ch_Rep_cfunL ch2ch_cont sbChain_dom_eq2)
  qed
    
  thus ?thesis
    apply(subst chainI,  simp_all add: assms)
    by (rule lub_iter_sbfix_mono_req, simp_all add: f1 assms)
qed
 
lemma chain_if_lub_iter_sbfix_req: assumes "chain Y" and "cont F" 
                                   and "sbfun_io_eq (F (\<Squnion>i. Y i)) cs"
  shows "(\<Squnion>i ia. iter_sbfix F i cs (Y ia)) \<sqsubseteq> (\<Squnion>i ia.  iter_sbfix F ia cs (Y i))"
proof -
  have f1: "\<And>i. cont (\<lambda>x. iter_sbfix F i cs x)"
    by (simp add: assms(2))
  moreover
  have f2: "(\<Squnion>i. iter_sbfix F i cs (\<Squnion>i. Y i)) = (\<Squnion> ia i. iter_sbfix F ia cs (Y i))"
    by (subst cont2lub_lub_eq, simp_all add: assms)
  moreover
  have f3: "\<forall>ia. sbfun_io_eq (F (Y ia)) cs"
    proof -
      have "(\<Squnion>n. F (Y n)\<cdot>(cs^\<bottom>)) = F (Lub Y)\<cdot>(cs^\<bottom>)"
      by (metis (no_types) assms(1) assms(2) ch2ch_cont cont2contlubE contlub_cfun_fun)
    thus ?thesis
      by (metis (no_types) assms(1) assms(2) assms(3) ch2ch_Rep_cfunL ch2ch_cont sbChain_dom_eq2)
    qed
  ultimately
  show ?thesis
    by (simp add: diag_lub ch2ch_cont assms iter_sbfix_chain)
qed
  
  
subsubsection \<open>dom\<close>
  
lemma lub_iter_sbfix_dom: assumes "sbfun_io_eq (F x) cs"
  shows "sbDom\<cdot>(\<Squnion>i. iter_sbfix F i cs x) =  sbDom\<cdot>((F x)\<cdot>(cs^\<bottom>))"
  by (metis (mono_tags, lifting) assms iter_sbfix_chain iter_sbfix_dom 
        lub_eq sbChain_dom_eq2)

      
subsection \<open>if_lub_iter_sbfix\<close>   
  

subsubsection \<open>mono\<close> 
  
lemma if_lub_iter_sbfix_mono_req: assumes "x \<sqsubseteq> y" and "cont F" 
                                  and "(P x) \<Longrightarrow> sbfun_io_eq (F x) cs" 
                                  and "sbDom\<cdot>x = sbDom\<cdot>y \<Longrightarrow> P x = P y"
  shows "((\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_sbfix F i cs) x)) x)
         \<sqsubseteq> ((\<lambda> x. (P x)  \<leadsto> (\<Squnion>i.(iter_sbfix F i cs) x)) y)"
proof (cases "(P x)")
  case True
  hence f1: "sbfun_io_eq (F x) cs"  
    by (simp add: assms(3))
  have "\<forall>i. ((iter_sbfix F i cs) x) \<sqsubseteq> ((iter_sbfix F i cs) y)"
    by (simp add: assms(1) assms(2) iter_sbfix_mono2)
  moreover
  have f2: "sbDom\<cdot>x = sbDom\<cdot>y"
    using assms(1) sbdom_eq by auto
  ultimately
  have "(\<Squnion>i.(iter_sbfix F i cs) x) \<sqsubseteq> (\<Squnion>i.(iter_sbfix F i cs) y)"
    by (simp add: assms(1) assms(2) f1 lub_iter_sbfix_mono_req)
  thus ?thesis
    using f2 some_below assms by auto
next
  case False
  have "sbDom\<cdot>y = sbDom\<cdot>x"
    by (metis assms(1) sbdom_eq)
  thus ?thesis     
    using False assms(4) by auto
qed
  
  
lemma sbfix_monoI [simp]: assumes  "cont F"  and "\<And> x. (P x) \<Longrightarrow> sbfun_io_eq (F x) cs" 
                          and "\<And> x y. sbDom\<cdot>x = sbDom\<cdot>y \<Longrightarrow> P x = P y"
  shows "monofun (\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_sbfix F i cs) x) )"
proof -
  have "\<And> x. \<And> y. x \<sqsubseteq> y \<Longrightarrow> ((\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_sbfix F i cs) x)) x) 
                              \<sqsubseteq> ((\<lambda> x. (P x)  \<leadsto> (\<Squnion>i.(iter_sbfix F i cs) x)) y)"
    proof -
      fix x :: "'a SB" and y :: "'a SB"
      assume a1: "x \<sqsubseteq> y"
      then have f2: "\<And>f p C. \<not> cont f \<or> \<not> p y \<or> \<not> p x \<or> sbDom\<cdot>(f x\<cdot>(C^\<bottom>)) \<noteq> C 
                                  \<or> (p x)\<leadsto>\<Squnion>n. iter_sbfix f n C x \<sqsubseteq> (p y)\<leadsto>\<Squnion>n. iter_sbfix f n C y"
      using if_lub_iter_sbfix_mono_req by blast
    have f3: "\<And>f p C. \<not> cont f \<or> p x \<or> (p x)\<leadsto>\<Squnion>n. iter_sbfix f n C x 
                                        \<sqsubseteq> (p y)\<leadsto>\<Squnion>n. iter_sbfix f n C y \<or> sbDom\<cdot>y = sbDom\<cdot>x"
      using a1 by (metis if_lub_iter_sbfix_mono_req)
    have f4: "\<And>p. (p x)\<leadsto>\<Squnion>n. iter_sbfix F n cs x \<sqsubseteq> (p y)\<leadsto>\<Squnion>n. iter_sbfix F n cs y \<or> p y \<or> p x"
      using a1 assms(1) if_lub_iter_sbfix_mono_req by blast
    have f5: "\<And>p. sbDom\<cdot>(F x\<cdot>(cs^\<bottom>)) \<noteq> cs \<or> 
              (p x)\<leadsto>\<Squnion>n. iter_sbfix F n cs x \<sqsubseteq> (p y)\<leadsto>\<Squnion>n. iter_sbfix F n cs y \<or> sbDom\<cdot>y = sbDom\<cdot>x"
      using a1 by (metis assms(1) if_lub_iter_sbfix_mono_req)
      { assume "P x"
        moreover
        { assume "sbfun_io_eq (F x) cs 
                            \<and> \<not>(Some (\<Squnion>n. iter_sbfix F n cs x) \<sqsubseteq> Some (\<Squnion>n. iter_sbfix F n cs y))"
          moreover
          { assume "P y \<and> P x \<and> sbfun_io_eq (F x) cs 
                             \<and> \<not>(True\<leadsto>\<Squnion>n. iter_sbfix F n cs x \<sqsubseteq> Some (\<Squnion>n. iter_sbfix F n cs y))"
            then have "\<not> P x"
            using f2 assms(1) by auto }
        ultimately have "\<not> P y \<or> \<not> P x"
          by metis }
      ultimately have "P x \<and> P y \<longrightarrow> (P x)\<leadsto>\<Squnion>n. iter_sbfix F n cs x 
                                   \<sqsubseteq> (P y)\<leadsto>\<Squnion>n. iter_sbfix F n cs y"
        using assms(2) by auto
      then have "sbDom\<cdot>y = sbDom\<cdot>x \<and> P x \<longrightarrow> (P x)\<leadsto>\<Squnion>n. iter_sbfix F n cs x 
                                          \<sqsubseteq> (P y)\<leadsto>\<Squnion>n. iter_sbfix F n cs y"
        by (meson assms(3)) }
    moreover
    { assume "\<not> P x"
      moreover
      { assume "\<exists>s. P y \<and> sbDom\<cdot>x = sbDom\<cdot>s \<and> \<not> P s"
        then have "sbDom\<cdot>y \<noteq> sbDom\<cdot>x"
          by (metis assms(3)) }
      ultimately have "sbDom\<cdot>y = sbDom\<cdot>x \<longrightarrow> (P x)\<leadsto>\<Squnion>n. iter_sbfix F n cs x 
                                          \<sqsubseteq> (P y)\<leadsto>\<Squnion>n. iter_sbfix F n cs y"
        using f4 by blast }
    moreover
    { assume "sbDom\<cdot>y \<noteq> sbDom\<cdot>x"
      moreover
      { assume "\<not> P x \<and> sbDom\<cdot>y \<noteq> sbDom\<cdot>x \<and> \<not> P x"
        then have "(P x)\<leadsto>\<Squnion>n. iter_sbfix F n cs x \<sqsubseteq> (P y)\<leadsto>\<Squnion>n. iter_sbfix F n cs y"
          using f3 assms(1) by blast }
      ultimately have "(P x)\<leadsto>\<Squnion>n. iter_sbfix F n cs x \<sqsubseteq> (P y)\<leadsto>\<Squnion>n. iter_sbfix F n cs y"
        using f5 assms(2) by blast }
    ultimately show "(P x)\<leadsto>\<Squnion>n. iter_sbfix F n cs x \<sqsubseteq> (P y)\<leadsto>\<Squnion>n. iter_sbfix F n cs y"
      by satx
  qed (* :) *)
  thus ?thesis
    by (simp add: monofunI)
qed


subsubsection \<open>cont\<close>   
  
lemma chain_if_lub_iter_sbfix_case: assumes "chain Y" and "cont F" and "P (\<Squnion>i. Y i)"
                                  and "\<And> x. (P x) \<Longrightarrow> sbfun_io_eq (F x) cs" 
                                  and "\<And> x y. sbDom\<cdot>x = sbDom\<cdot>y \<Longrightarrow> P x = P y"
  shows "(P (\<Squnion>i. Y i)) \<leadsto> (\<Squnion>i.(iter_sbfix F i cs) (\<Squnion>i. Y i)) 
          \<sqsubseteq> (\<Squnion>i. (P (Y i)) \<leadsto> (\<Squnion>ia. (iter_sbfix F ia cs) (Y i)))"
proof -
  have f1: "sbfun_io_eq (F (\<Squnion>i. Y i)) cs"
    by (simp add: assms(3) assms(4))
  have f2: "(\<Squnion>i. iter_sbfix F i cs (\<Squnion>i. Y i)) = (\<Squnion> ia i. iter_sbfix F ia cs (Y i))"
    by (subst cont2lub_lub_eq, simp_all add: assms)
  have f3: "\<forall>ia. sbfun_io_eq (F (Y ia)) cs"
    proof -
      have "(\<Squnion>n. F (Y n)\<cdot>(cs^\<bottom>)) = F (Lub Y)\<cdot>(cs^\<bottom>)"
        by (metis (no_types) assms(1) assms(2) ch2ch_cont cont2contlubE contlub_cfun_fun)
      thus ?thesis
        by (metis (no_types) assms(1) assms(2) f1 ch2ch_Rep_cfunL ch2ch_cont sbChain_dom_eq2)
    qed
  have f4: "(\<Squnion>i ia. iter_sbfix F i cs (Y ia)) \<sqsubseteq> (\<Squnion>i ia.  iter_sbfix F ia cs (Y i))"
    by (rule chain_if_lub_iter_sbfix_req, simp_all add: assms)
      
      
   (* PART II: show the equality for the packaging with some *)
  have f10: "(P (\<Squnion>i. Y i)) \<leadsto> (\<Squnion>i. iter_sbfix F i cs (\<Squnion>i. Y i)) 
              = Some (\<Squnion>i. iter_sbfix F i cs (\<Squnion>i. Y i))"
    by (simp add: assms(3))
  have f11: "(\<Squnion>i. (P (Y i)) \<leadsto>  \<Squnion>ia. iter_sbfix F ia cs (Y i)) 
              = Some (\<Squnion>i ia. iter_sbfix F ia cs (Y i))"
  proof -
    have f111: "(\<Squnion>i. (P (Y i)) \<leadsto>   \<Squnion>ia. iter_sbfix F ia cs (Y i)) 
                 = (\<Squnion>i. Some(\<Squnion>ia. iter_sbfix F ia cs (Y i)))"
      by (meson assms(1) assms(3) assms(5) sbChain_dom_eq2)
    have f112_chain: "chain (\<lambda>i. \<Squnion>ia. iter_sbfix F ia cs (Y i))"
      by (simp add: assms(1) assms(2) chain_lub_iter_sbfix f1)
    have f112: "(\<Squnion>i. Some(\<Squnion>ia. iter_sbfix F ia cs (Y i))) 
                = Some (\<Squnion>i ia. iter_sbfix F ia cs (Y i))"
      by (simp add: some_lub_chain_eq3 f112_chain)
    thus ?thesis
      using f111 by auto
  qed
    
  show ?thesis
    apply(subst f10, subst f11)
    by (simp add: some_below f2 f4)
qed
  
        
lemma chain_if_lub_iter_sbfix: assumes "chain Y" and "cont F"
                               and "\<And> x. (P x) \<Longrightarrow> sbfun_io_eq (F x) cs" 
                               and "\<And> x y. sbDom\<cdot>x = sbDom\<cdot>y \<Longrightarrow> P x = P y" 
  shows "(P (\<Squnion>i. Y i)) \<leadsto> (\<Squnion>i.(iter_sbfix F i cs) (\<Squnion>i. Y i)) 
          \<sqsubseteq> (\<Squnion>i. (P (Y i)) \<leadsto> (\<Squnion>ia. (iter_sbfix F ia cs) (Y i)))"
proof (cases "P (\<Squnion>i. Y i)")
  case True
  then show ?thesis
    using  chain_if_lub_iter_sbfix_case assms by blast
next
  case False
  hence f1: "(P (\<Squnion>i. Y i)) = False"
    by simp
  then show ?thesis
  proof -
    have f2: "\<forall>i. sbDom\<cdot>(Y i) = sbDom\<cdot>(\<Squnion>i. Y i)"
      by (simp add: sbChain_dom_eq2 assms(1))
    hence f3: "\<forall>i. (P (Y i)) = (P (\<Squnion>i. Y i))"
      by (metis assms(4))
    thus ?thesis
      by (simp add: f3 f1)
  qed
qed
  
 
  


(* Insertion lemma for cont sbfix *)
lemma sbfix_contI [simp]: assumes  "cont F" and "\<And> x. (P x) \<Longrightarrow> sbfun_io_eq (F x) cs" 
                          and "\<And> x y. sbDom\<cdot>x = sbDom\<cdot>y \<Longrightarrow> P x = P y"
  shows "cont (\<lambda> x. (P x) \<leadsto> (\<Squnion>i.(iter_sbfix F i cs) x) )"
  apply (rule contI2)
   apply (rule sbfix_monoI, simp add: assms(1), simp add: assms(2), metis assms(3))
  using chain_if_lub_iter_sbfix assms by blast
    


    
  
  
    
 (* DEMO: cont of spfcomp, now in two lines :) *)
  
lemma spf_compH3_mono2: 
  shows "monofun (\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> (\<Squnion>i. (iter_spfCompH3 f1 f2 i) x))"
  apply(rule sbfix_monoI)
  by (simp_all)
    
lemma spf_compH3_cont2: 
  shows "cont (\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> (\<Squnion>i. (iter_spfCompH3 f1 f2 i) x))"
  apply(rule sbfix_contI)
    by (simp_all)
  
end