(*  Title:  SerComp_JB.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: additional  lemmas for composition, especially monofun and cont proof for spfComp
*)

theory SPF_Composition_JB
imports SPF SBTheorie SPF_Templates
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
       by(simp add: spfCompHelp2_def)
  qed

 
    
(* ----------------------------------------------------------------------- *)
section \<open>iter_spfCompHelp2\<close>
(* ----------------------------------------------------------------------- *) 
  
(* abbrv for the part behind  \<leadsto> in spfcomp but without the restriction to Oc *) 
abbreviation iter_spfcompH2 :: "'a SPF \<Rightarrow> 'a SPF \<Rightarrow> nat \<Rightarrow> 'a SB  \<Rightarrow> 'a SB" where
"(iter_spfcompH2 f1 f2 i) \<equiv> (\<lambda> x. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"  


(* for all i the i'th iteration on spfcomp is cont as application iterate is cont on cont fun *) 
lemma iter_spfcompH2_cont2[simp]: "cont (\<lambda>x. iter_spfcompH2 f1 f2 i x)"
  by simp
    
lemma iter_spfcompH2_mono[simp]:  "monofun 
                                      (\<lambda> x. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"
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
      by(simp add: sbdom_lub_eq assms)
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
        by(simp add: sbdom_lub_eq assms)
      ultimately
      have f4: "chain Y \<longrightarrow> (\<Squnion>i ia. iter_spfcompH2 f1 f2 i (Y ia))  
                              \<sqsubseteq> (\<Squnion>i ia.  iter_spfcompH2 f1 f2 ia (Y i))"
        by(simp add: diag_lub ch2ch_cont f1 f2 f3 assms)
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

      
(* spf_well of spfcopmp, to be continued ... ;) *)

                                
(* used abbreviations are equal to comp function *)
   (* together with the lemma  spfcomp_tospfH2, the complete equality with spfcomp is proven *)
lemma spfcomp_abbrv_tospfH2: "(\<lambda> x. (sbDom\<cdot>x = I f1 f2) 
                                \<leadsto> (\<Squnion>i.(iter_spfcompH2 f1 f2 i) x) \<bar> Oc f1 f2)
                       = (\<lambda> x. (sbDom\<cdot>x = I f1 f2) 
                          \<leadsto> (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2)"      
  by simp
      
      
      
(*
BACKUPS 


      
lemma test35:
  shows "chain Y \<longrightarrow> (\<Squnion>i. iter_spfcompH2 f1 f2 i (\<Squnion>i. Y i)) =  (\<Squnion>i ia.  iter_spfcompH2 f1 f2 i (Y ia))"
proof -
  have f1:" \<And>i. cont (\<lambda>x. iter_spfcompH2 f1 f2 i x)"
    by(simp add: cont2lub_lub_eq) 
  thus ?thesis
    by(rule cont2lub_lub_eq)
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
    by(simp add: cont2lub_lub_eq) 
  hence f2: ""
  thus ?thesis
    by(rule cont2lub_lub_eq)

*)
end