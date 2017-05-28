(*  Title:  SPF_Comp.thy
    Author: Jens Christoph Bürger, Marc Wiartalla
    e-mail: jens.buerger@rwth-aachen.de, marc.wiartalla@rwth-aachen.de

    Description: lemmata for composition of SPFs
*)


theory SPF_Comp
  imports SPF SB SPF_Templates
    
begin
  
chapter \<open>prelude\<close>  
  
(* ----------------------------------------------------------------------- *)
section \<open>definitions\<close>
(* ----------------------------------------------------------------------- *)
  
subsection \<open>general-composition\<close> 
  
(* adds the input to the original sbFix definition *)
  (* makes old sbfix obsolete *)
definition sbFix2 :: "('m SB \<Rightarrow> 'm SB \<rightarrow> 'm SB) \<Rightarrow> 'm SB  \<Rightarrow> channel set \<Rightarrow> 'm SB" where
"sbFix2 F x cs \<equiv>  (\<Squnion>i. iterate i\<cdot>(F x)\<cdot>(cs^\<bottom>))"

abbreviation iter_sbfix:: "('m SB \<Rightarrow> 'm SB \<rightarrow> 'm SB) \<Rightarrow> nat \<Rightarrow> channel set \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
"iter_sbfix F i cs \<equiv> (\<lambda> x. iterate i\<cdot>(F x)\<cdot>(cs^\<bottom>))"

abbreviation sbfun_io_eq :: "('m SB \<rightarrow> 'm SB)  \<Rightarrow> channel set \<Rightarrow> bool" where
"sbfun_io_eq f cs \<equiv> sbDom\<cdot>(f\<cdot>(cs^\<bottom>)) = cs"


subsubsection \<open>obsolete\<close>  

(* abbrv for the part behind  \<leadsto> in spfcomp but without the restriction to Oc *) 
abbreviation iter_spfcompH2 :: "'a SPF \<Rightarrow> 'a SPF \<Rightarrow> nat \<Rightarrow> 'a SB  \<Rightarrow> 'a SB" where
"(iter_spfcompH2 f1 f2 i) \<equiv> (\<lambda> x. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))"  

(* newer spfcopmp definition: input is not iterated *)
definition spfCompH3 :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SB \<Rightarrow> 'm SB  \<rightarrow> 'm SB" where
"spfCompH3 f1 f2 x \<equiv> (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f2)))"

abbreviation iter_spfCompH3 :: "'a SPF \<Rightarrow> 'a SPF \<Rightarrow> nat \<Rightarrow> 'a SB  \<Rightarrow> 'a SB" where
"(iter_spfCompH3 f1 f2 i) \<equiv> (\<lambda> x. iterate i\<cdot>(spfCompH3 f1 f2 x)\<cdot>((spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)^\<bottom>))" 


(* TODO: @Marc add definitions from SPF_MW sercomp, parcomp *)

subsection \<open>feedback\<close> 

subsubsection \<open>obsolete\<close>   
  
(* obsolete feedback operator *)
definition spfFeedbackOperator :: "'a SPF \<Rightarrow> 'a SPF" ("\<mu>_" 50) where
"spfFeedbackOperator f \<equiv>
let I  = spfDom\<cdot>f - spfRan\<cdot>f;
    I1 = spfDom\<cdot>f;
    C  = spfRan\<cdot>f
in Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = I) \<leadsto>
    (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. (f\<rightleftharpoons>((sb \<uplus> z)\<bar> I1)))\<cdot>(C^\<bottom>)))" 
  
definition spfFeedH:: "'m SPF \<Rightarrow> 'm SB \<Rightarrow> 'm SB  \<rightarrow> 'm SB" where
"spfFeedH f x \<equiv> (\<Lambda> z. (f\<rightleftharpoons>((x \<uplus> z)\<bar> (spfDom\<cdot>f))))"

abbreviation iter_spfFeedH:: "'m SPF \<Rightarrow> nat \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
"iter_spfFeedH f i \<equiv> (\<lambda> x. iterate i\<cdot>(spfFeedH f x)\<cdot>((spfRan\<cdot>f)^\<bottom>))"

(* even more obsolete feedback operator *)
definition spfFeedbackOperator2 :: "'a SPF \<Rightarrow> 'a SPF" where
"spfFeedbackOperator2 f \<equiv>
let I  = spfDom\<cdot>f - spfRan\<cdot>f;
    I1 = spfDom\<cdot>f;
    C  = (spfDom\<cdot>f \<union> spfRan\<cdot>f)
in Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = I) \<leadsto>
    (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. sb \<uplus> (f\<rightleftharpoons>(z \<bar> I1)))\<cdot>(C^\<bottom>)) \<bar> (spfRan\<cdot>f))" 

definition spfFeedH2:: "'m SPF \<Rightarrow> 'm SB \<Rightarrow> 'm SB  \<rightarrow> 'm SB" where
"spfFeedH2 f x \<equiv> (\<Lambda> z. x \<uplus> (f\<rightleftharpoons>(z\<bar>(spfDom\<cdot>f))))"

abbreviation iter_spfFeedH2:: "'m SPF \<Rightarrow> nat \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
"iter_spfFeedH2 f i \<equiv> (\<lambda> x. iterate i\<cdot>(spfFeedH2 f x)\<cdot>((spfDom\<cdot>f \<union> spfRan\<cdot>f)^\<bottom>))"
  

 
(* ----------------------------------------------------------------------- *)
section \<open>general-lemmata\<close>
(* ----------------------------------------------------------------------- *)
   (* TODO port general lemmas to corresponding production theories! ! ! *)
 
subsection \<open>cfun\<close>   
  
lemma mycontI2: assumes "monofun (f::'a::cpo \<Rightarrow> 'b::cpo)" 
                and "(\<And>Y. chain Y \<Longrightarrow> f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i)))"
  shows "cont f"
  by (simp add: Cont.contI2 assms(1) assms(2))

(* below lemmata *)   
lemma cont_pref_eq1I: assumes "(a \<sqsubseteq> b)"
  shows "f\<cdot>a \<sqsubseteq> f\<cdot>b"
  by (simp add: assms monofun_cfun_arg)
     
lemma cont_pref_eq2I:  assumes "(a \<sqsubseteq> b)"
  shows "f\<cdot>x\<cdot>a \<sqsubseteq> f\<cdot>x\<cdot>b"
  by (simp add: assms monofun_cfun_arg)
    
(* equality lemmata *)    
lemma cfun_arg_eqI:  assumes "(a = b)"
  shows "f\<cdot>a = f\<cdot>b"
  by (simp add: assms)

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
  
lemma sbdom_lub_eq2I: assumes "chain Y" 
                    and  "(sbDom\<cdot>(\<Squnion>i. Y i) = cs)"
  shows "\<forall>ia. sbDom\<cdot>(Y ia) = cs"
proof -
  have "\<forall>i. ( Y i) \<sqsubseteq> (\<Squnion>i. Y i)" 
    by (simp add: is_ub_thelub assms(1))
  have "\<forall>i. (sbDom\<cdot>(Y i)) = (sbDom\<cdot>(\<Squnion>i. Y i))"
   by (simp add: sbChain_dom_eq2 assms(1))
 thus ?thesis
   by (simp add: assms(2))
qed  
  
lemma sb_one_ch_eqI: assumes "x = y"
  shows "[ch \<mapsto> x]\<Omega> = [ch \<mapsto> y]\<Omega>"
  by (simp add: assms)

   
subsection \<open>sbunion\<close>    
  
lemma sbunion_pref_eq: assumes "(a \<sqsubseteq> b)" and "(c \<sqsubseteq> d)"
  shows "(a \<uplus> c \<sqsubseteq> b \<uplus> d)"
  by (simp add: assms(1) assms(2) monofun_cfun)
  
lemma sbunion_pref_eq2: assumes "(a \<sqsubseteq> b)"
  shows "(x \<uplus> a \<sqsubseteq> x \<uplus> b)"
     by (metis assms monofun_cfun_arg)
  
lemma sbunion_assoc2: "(sb1 \<uplus> sb2) \<uplus> sb3 = sb1 \<uplus> (sb2 \<uplus> sb3)"
  by (simp add: sbunion_associative)
    
lemma sbunion_eqI:  assumes "(a = b)" and "(c = d)"
  shows "(a \<uplus> c = b \<uplus> d)"
  by (simp add: assms(1) assms(2))
  
    
subsection \<open>sbres\<close>    
  
lemma sbres_pref_eq: assumes "(a \<sqsubseteq> b)"
  shows "(a \<bar> cs) \<sqsubseteq> (b \<bar> cs)"
  by (metis assms monofun_cfun_arg)
    
lemma sbres_sbdom_supset: assumes "sbDom\<cdot>sb \<subseteq> cs"
  shows "sb \<bar> cs = sb \<bar> (sbDom\<cdot>sb)"
  by (simp add: assms)
    
lemma sbres_sbdom_supset_inter: 
  shows "sb \<bar> cs = sb \<bar> (cs \<inter> (sbDom\<cdot>sb))"
  by (smt inf.right_idem inf_commute inf_sup_ord(1) sb_eq 
          sbrestrict2sbgetch sbrestrict_sbdom set_mp)
        
lemma sb_rest: "([ch1 \<mapsto> s]\<Omega>)\<bar>{ch1} = [ch1 \<mapsto> (s:: nat stream)]\<Omega>"
  by(simp add: sbrestrict_insert)

    
    
subsection \<open>sbgetch\<close>     
    
lemma sb_onech_getch_insert [simp]:"([ch1 \<mapsto> s]\<Omega>) . ch1 = (s:: nat stream)"
  by(simp add: sbgetch_rep_eq)
  

      
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
 
(* lubs are equal if chain index is multiplied *)
lemma lub_range_mult:  fixes Y:: "nat \<Rightarrow> 'a::cpo" assumes "chain Y" and "m \<ge> 1"
  shows "(\<Squnion>i. Y (i)) = (\<Squnion>i. Y (m * i))"
proof -
  have f1: "\<forall> (i::nat). i \<le> (m * i)"
    using assms(2) by auto
  have f2: "\<forall> i. Y (i) \<sqsubseteq> Y (m * i)"
    by (simp add: assms(1) f1 po_class.chain_mono)
  have f3: "chain (\<lambda>i. Y (m * i))"
    by (metis (no_types, lifting) Suc_n_not_le_n assms mult.commute nat_le_linear 
          nat_mult_le_cancel_disj po_class.chain_def po_class.chain_mono) 
        
  hence "(\<Squnion>i. Y (m * i)) \<sqsubseteq> (\<Squnion>i. Y (i))"
    using assms lub_below_iff by blast    
  thus ?thesis
    by (simp only: assms below_antisym f2 f3 lub_mono)
qed
  
(* lub equality rule for mult lub equality *)
lemma lub_mult_shift_eq: fixes Y:: "nat \<Rightarrow> 'a::cpo" fixes Z:: "nat \<Rightarrow> 'a::cpo" 
  assumes "chain Y" and "chain Z" and "m \<ge> 1"
  and "\<And> i. Y (i) = Z (m * i)"
shows "(\<Squnion>i. (Y i)) = (\<Squnion>i. (Z i))"
  apply (simp only: assms(4))
  using assms(2) assms(3) lub_range_mult by fastforce
  
lemma lub_mult2_shift_eq: fixes Y:: "nat \<Rightarrow> 'a::cpo" fixes Z:: "nat \<Rightarrow> 'a::cpo" 
  assumes "chain Y" and "chain Z"
  and "\<And> i. Y (i) = Z (2 * i)"
shows "(\<Squnion>i. (Y i)) = (\<Squnion>i. (Z i))"
  by (metis One_nat_def Suc_n_not_le_n assms(1) assms(2) assms(3) le_add_same_cancel1 
        lub_mult_shift_eq mult_2 nat_le_linear nat_mult_1_right)  
  
subsection \<open>spf\<close>
   
lemma spf_pref_eq: assumes "(a \<sqsubseteq> b)"
  shows "(f \<rightleftharpoons> a) \<sqsubseteq> (f \<rightleftharpoons> b)"
  by (metis Rep_CSPF_def assms cont2mono monofun_cfun_arg monofun_def op_the_cont)
    
lemma spf_arg_eqI:  assumes "(a = b)"
  shows "f\<rightleftharpoons>a = f\<rightleftharpoons>b"
  by (simp add: assms)
    
subsection \<open>subst\<close>  
  
(* used for substitution *)
lemma two_times_one_insert: "2 * (Suc 0) = Suc(Suc(0))"
  by simp
    
lemma two_times_suci_insert: "2 * (Suc i) = (2 + (2*i))"
  by simp

    
lemma two_suc_suc_eq_insert: "2 = Suc(Suc(0))"
  by simp
    
    
(* show that the version used from proofing is equal to the actual definition of the feedback
    operator *)
lemma spfFeedbackOperator2_iter_spfFeedH: 
shows "(spfFeedbackOperator f) = Abs_CSPF (\<lambda> sb. (sbDom\<cdot>sb = (spfDom\<cdot>f - spfRan\<cdot>f)) \<leadsto>
                                              (\<Squnion>i. (iter_spfFeedH f i) sb))"
  apply (simp add: spfFeedbackOperator_def)
  apply (subst spfFeedH_def)
  by simp
    
lemma spfComp_Oc_sub_C: assumes "c \<in> Oc f1 f2" shows "c \<in> C f1 f2"
  by (meson assms set_mp spfOc_sub_C)
    
    
  
    
    
    
    
  
chapter \<open>comp-helpers\<close>    
  
(* ----------------------------------------------------------------------- *)
section \<open>spfCompH2\<close>
(* ----------------------------------------------------------------------- *)
  (* WARNING this helper is obsolete *)
  
(* Proof comphelper properties by referring to original comphelper *)
lemma spfCompH2_mono[simp]: "monofun (\<lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1)) 
                                             \<uplus> (f2 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f2)))"
  using cont2mono spfCompHelp_cont by blast

lemma spfCompH2_cont[simp]: "cont (\<lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1)) 
                                          \<uplus> (f2 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f2)))"
  using spfCompHelp_cont by blast

lemma helpermonoinX: shows "monofun (\<lambda> x. spfCompHelp2 f1 f2 x)"
by(simp add: spfCompHelp2_def)

lemma helpercontinX: shows "cont (\<lambda> x. spfCompHelp2 f1 f2 x)"
apply(simp add: spfCompHelp2_def)
proof -
   have "\<forall>x. cont (\<lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1))  \<uplus> (f2 \<rightleftharpoons>(z \<bar> spfDom\<cdot>f2)))"
   by simp
   thus "cont (\<lambda>x. \<Lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1))  \<uplus> (f2 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f2)))"
   by (simp add: cont2cont_LAM)
qed

lemma spfcomp_tospfH2: "(spfcomp f1 f2) 
                   = Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = I f1 f2) \<leadsto> 
                      (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2))) \<bar> Oc f1 f2)"
  apply (subst spfcomp_def, subst spfCompHelp2_def, subst C_def, subst I_def, subst Oc_def)
  by (metis (no_types) C_def I_def Oc_def)
    
    
subsection \<open>channel properties\<close>
(* ----------------------------------------------------------------------- *)

lemma spfCompH2_getch_outofrange: assumes "c \<notin> spfRan\<cdot>f1" 
                                and "c \<notin> spfRan\<cdot>f2" 
                                and "sbDom\<cdot>sb = C f1 f2"
  shows "((spfCompHelp2 f1 f2 x)\<cdot>sb) . c = x . c"
  apply (simp add: spfCompHelp2_def)
  apply (subst sbunion_getchL)
  apply (simp add: C_def assms(2) assms(3) subsetI)
  by (simp add: C_def Un_assoc assms(1) assms(3))

lemma spfCompH2_dom [simp]: assumes "sbDom\<cdot>sb = C f1 f2"
  shows "sbDom\<cdot>((spfCompHelp2 f1 f2 x)\<cdot>sb) = (sbDom\<cdot>x \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
  apply (simp add: spfCompHelp2_def)
  proof -
    have f1: "spfDom\<cdot>f1 \<subseteq> sbDom\<cdot>sb"
      by (simp add: C_def Un_commute Un_left_commute assms)
    have "spfDom\<cdot>f2 \<subseteq> sbDom\<cdot>sb"
      using C_def assms by auto
    thus "sbDom\<cdot>x \<union> (sbDom\<cdot>(f1 \<rightleftharpoons> (sb\<bar>spfDom\<cdot>f1))) \<union> (sbDom\<cdot> (f2 \<rightleftharpoons> (sb\<bar>spfDom\<cdot>f2))) 
                = (sbDom\<cdot>x \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
      using f1 by simp
qed
 
  
subsection \<open>iterate spfCompH2\<close>
  
lemma spfCompH2_itDom[simp]: assumes "sbDom\<cdot>x = I f1 f2"
  shows "sbfun_io_eq (iterate i\<cdot>(spfCompHelp2 f1 f2 x)) (C f1 f2)"
  apply (induct_tac i)
   apply auto[1]
  by (simp add: C_def I_def assms inf_sup_aci(6))
  
  
lemma spfCompH2_itgetChI: assumes "sbDom\<cdot>x = I f1 f2" 
                      and "spfComp_well f1 f2"
                      and "c \<in> I f1 f2"
  shows "iter_spfcompH2 f1 f2 (Suc i) x . c = x .c"
  apply (unfold iterate_Suc, subst spfCompHelp2_def)
  apply (simp)
  apply (subst sbunion_getchL)
  apply (metis C_def DiffD2 I_def UnI2 assms(1) assms(3) inf_sup_ord(4) 
               le_supI1 spfCompH2_itDom spfRanRestrict)
  apply (subst sbunion_getchL)
   apply (metis C_def DiffD2 I_def UnI1 Un_upper1 assms(1) assms(3) 
                le_supI1 spfCompH2_itDom spfRanRestrict)
   by (simp)


lemma spfCompH2_itResI: assumes "sbDom\<cdot>x = I f1 f2" 
                    and "spfComp_well f1 f2"
  shows "(iter_spfcompH2 f1 f2 (Suc i) x) \<bar> (I f1 f2) = x"
  apply (rule sb_eq)
   apply (simp add: assms(1) inf_sup_aci(1) inf_sup_aci(6))
   using assms(1) assms(2) spfCompH2_itgetChI by fastforce
  
    
    
    
    
    
chapter \<open>serial-composition\<close>
(* This was the first approach of the evaluation of the composition *)
  (* The situation here is that the domain of one function is exactly the range of another function
     other internal channels do not exist *)
  
(* ----------------------------------------------------------------------- *)
section \<open>sercomp channel domain lemmata\<close>
(* ----------------------------------------------------------------------- *)
    
lemma spfComp_test8: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                       and "sbDom\<cdot>x = I f1 f2" 
                       and "spfComp_well f1 f2"
                       and "no_selfloops f1 f2"
                       and "pL f1 f2 = {}"
  shows "spfDom\<cdot>f1  = (I f1 f2)"
  using assms(1) assms(2) assms(3) assms(4) assms(5) spfComp_I_domf1_eq by blast
    
(* for simp usage when the resut is input for f2 *)
lemma spfComp_domranf1: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                        and "sbDom\<cdot>sb = I f1 f2" 
                        and "spfComp_well f1 f2"
                        and "no_selfloops f1 f2"
                        and "pL f1 f2 = {}"
  shows "(sbDom\<cdot>(f1 \<rightleftharpoons> (sb\<bar>spfDom\<cdot>f1))) = spfRan\<cdot>f1"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) spfRanRestrict subset_refl 
      spfComp_I_domf1_eq)
    

lemma spfComp_I_domf1_eq: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                          and "sbDom\<cdot>sb = I f1 f2" 
                          and "spfComp_well f1 f2"
                          and "no_selfloops f1 f2"
                          and "pL f1 f2 = {}"
  shows "I f1 f2 = spfDom\<cdot>f1"
  apply(simp add: I_def, subst assms(1))
  by (metis I_def  assms(1) assms(2) assms(3) assms(4) assms(5) spfComp_I_domf1_eq)
    

lemma spfComp_getC_Oc[simp]:  assumes "c \<in> spfRan\<cdot>f2" 
  shows "c \<in> Oc f1 f2"
  by (simp add: Oc_def assms(1))
    
lemma helper_cont[simp] : "cont (Rep_cfun (spfCompHelp2 f1 f2 x))"
by simp 


(* ----------------------------------------------------------------------- *)
section \<open>iteration lemmata\<close>
(* ----------------------------------------------------------------------- *)
  
(* proof equality of iterate expressions for f1 and f2 *)
lemma spfComp_serialf1: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                       and "sbDom\<cdot>x = I f1 f2" 
                       and "spfComp_well f1 f2"
                       and "no_selfloops f1 f2"
                       and "c \<in> spfRan\<cdot>f1" 
                       and "pL f1 f2 = {}"                   
shows "(iter_spfcompH2 f1 f2 (Suc (Suc i)) x) . c = (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1)) . c"
  apply (subst iterate_Suc)
  apply(subst spfCompHelp2_def, simp)
  apply (subst sbunion_getchL)
   apply (smt assms(1) assms(2) assms(3) assms(4) assms(5) disjoint_iff_not_equal inf_sup_ord(4) 
              le_supI1 spfCompH2_dom spfCompH2_itDom spfComp_well_def spfRanRestrict)
   apply (subst sbunion_getchR)
    apply (metis C_def Un_upper1 assms(2) assms(5) iterate_Suc le_supI1 spfCompH2_itDom 
                 spfRanRestrict)
  by (metis assms(1) assms(2) assms(3) assms(4) assms(6) iterate_Suc sbrestrict_id 
      spfComp_I_domf1_eq spfCompH2_itResI subsetI)
  
lemma spfComp_serialf2: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                       and "sbDom\<cdot>x = I f1 f2" 
                       and "spfComp_well f1 f2"
                       and "no_selfloops f1 f2"
                       and "c \<in> spfRan\<cdot>f2" 
                       and "pL f1 f2 = {}"
  shows "(iter_spfcompH2 f1 f2 (Suc (Suc (Suc i))) x) . c
                   = (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))) . c"
  apply (subst iterate_Suc)
  apply (subst spfCompHelp2_def)
  apply (simp)
  apply (subst sbunion_getchR)
   apply (metis assms(1) assms(2) assms(5) inf_sup_ord(4) iterate_Suc le_supI1 spfCompH2_dom 
                spfCompH2_itDom spfRanRestrict)
    by (smt Int_absorb1 assms(1) assms(2) assms(3) assms(4) assms(6) inf_sup_ord(4) iterate_Suc 
            le_supI1 sb_eq sbrestrict2sbgetch sbrestrict_sbdom spfCompH2_dom spfComp_domranf1 
            spfCompH2_itDom spfComp_serialf1)

(* this is the core lemma for the equality proofs *)
lemma spfComp_serial : assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                       and "sbDom\<cdot>x = I f1 f2" 
                       and "spfComp_well f1 f2"
                       and "no_selfloops f1 f2"
                       and "pL f1 f2 = {}"
  shows "(iter_spfcompH2 f1 f2 (Suc (Suc (Suc i))) x) = x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                      \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1)))" (is "?L = ?R")
  apply(rule sb_eq)
  apply (smt C_def assms(1) assms(2) assms(3) assms(4) assms(5) inf_sup_ord(4) sbunionDom sbunion_restrict 
             spfComp_I_domf1_eq spfComp_domranf1 spfCompH2_itDom spfRanRestrict sup.right_idem)
  by (smt assms(1) assms(2) assms(3) assms(4) assms(5) inf_sup_ord(4) iterate_Suc sbunionDom 
          sbunion_getchL sbunion_getchR sbunion_restrict spfComp_domranf1 spfCompH2_getch_outofrange 
          spfCompH2_itDom spfComp_serialf1 spfComp_serialf2 spfRanRestrict)
        
        
lemma spfComp_serialnf_chain: assumes "sbDom\<cdot>x = I f1 f2"
  shows "chain (\<lambda>i. iter_spfcompH2 f1 f2 i x)"
  apply(rule sbIterate_chain)
  apply (simp add: assms C_def I_def)
  by blast

  
(* ----------------------------------------------------------------------- *)
section \<open>lub iteration\<close>
(* ----------------------------------------------------------------------- *) 
  
  (* show that the chain has it's maximum at the third chain element *)
lemma spfComp_serial_max: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                          and "sbDom\<cdot>x = I f1 f2" 
                          and "spfComp_well f1 f2"
                          and "no_selfloops f1 f2"
                          and "pL f1 f2 = {}"
  shows "max_in_chain 3 (\<lambda>i. iter_spfcompH2 f1 f2 i x)"
  apply(rule max_in_chainI, subst num3_eq)
  apply(subst spfComp_serial, simp_all add: assms)
  by (metis Suc_le_D Suc_le_lessD assms(1) assms(2) assms(3) assms(4) assms(5) less_Suc_eq_le 
        spfComp_serial)
      
  (* show that lub can be described by constant if no feedback channels exist *)
lemma spfComp_serial_itconst1 [simp]: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                                      and "sbDom\<cdot>x = I f1 f2" 
                                      and "spfComp_well f1 f2"
                                      and "no_selfloops f1 f2"
                                      and "pL f1 f2 = {}"
  shows "(\<Squnion>i. iter_spfcompH2 f1 f2 i x) = iter_spfcompH2 f1 f2 3 x"
  using assms(1) assms(2) assms(3) assms(4) assms(5)
        maxinch_is_thelub spfComp_serial_max spfComp_serialnf_chain by blast
    
lemma spfComp_serial_itconst2 [simp]: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                                      and "sbDom\<cdot>x = I f1 f2" 
                                      and "spfComp_well f1 f2"
                                      and "no_selfloops f1 f2"
                                      and "pL f1 f2 = {}"
  shows "(\<Squnion>i. iter_spfcompH2 f1 f2 i x) = x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                                             \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1)))"
  by (metis One_nat_def Suc_1 assms(1) assms(2) assms(3) assms(4) assms(5)
            spfComp_serial spfComp_serial_itconst1 num3_eq)
         
          
(* ----------------------------------------------------------------------- *)
section \<open>iter const\<close>
(* ----------------------------------------------------------------------- *)
          
(* NOW BRING IT ALL TOGETHER *)

(* Use the lub equality to simplify the inner expression and show that the composition is a 
   well defined spf *)
          
(* show that spfcomp can be simplified to SPF without iterate if the assumtion hold *)
lemma spfComp_iterconst_eq[simp]: assumes "spfComp_well f1 f2"
                                  and "no_selfloops f1 f2" 
                                  and "spfRan\<cdot>f1 = spfDom\<cdot>f2" 
                                  and "pL f1 f2 = {}"  
shows "(\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(\<Squnion>i. iter_spfcompH2 f1 f2 i x)\<bar>Oc f1 f2)
  = (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))))\<bar>Oc f1 f2)"
proof -
  have "\<forall>s. (sbDom\<cdot>s \<noteq> I f1 f2  \<or> 
        (Some ((\<Squnion>n. iterate n\<cdot>(spfCompHelp2 f1 f2 s)\<cdot> (sbLeast (C f1 f2)))\<bar>Oc f1 f2) 
        = Some (s \<uplus> (f1 \<rightleftharpoons> (s\<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (s\<bar>spfDom\<cdot> f1)))\<bar>Oc f1 f2)))"
    by (metis assms(1) assms(2) assms(3) assms(4) spfComp_serial_itconst2)
  then show ?thesis
    by meson
qed
  
lemma serial_iterconst_cont[simp]:       assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                                  and "spfComp_well f1 f2"
                                  and "pL f1 f2 = {}"
shows "cont (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                                    \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))))\<bar>Oc f1 f2)"
proof -
  
   (* show f2 (f1 (x)) is cont *) 
   have f11: "cont (\<lambda>s. (Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))"
     by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
   moreover
     have f12: "cont (\<lambda>s. (Rep_cfun (Rep_SPF f2))\<rightharpoonup>(s))"
       by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
   ultimately
     have f13: "cont (\<lambda>s. (Rep_cfun (Rep_SPF f2))\<rightharpoonup>(((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))))"
       using cont2cont_APP cont_compose op_the_cont by blast
         
   (* show that sbUnion is cont *)      
   have f21: "cont (\<lambda>s. (Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))"
     by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
   hence f22: "cont (\<lambda>s. sbUnion\<cdot> (s  \<uplus>  ((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))))"
     by simp
   hence f23: "cont (\<lambda>s. s  \<uplus>  ((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1)) 
            \<uplus> ((Rep_cfun (Rep_SPF f2))\<rightharpoonup>(((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1)))))"
     using f13 cont2cont_APP cont_compose op_the_cont by blast
       
   (* show thesis *)    
   thus ?thesis
      by(simp add: Rep_CSPF_def)
  qed
    
lemma serial_iterconst_monofun[simp]:    assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                                  and "spfComp_well f1 f2"
                                  and "pL f1 f2 = {}"
shows "monofun (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                                    \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))))\<bar>Oc f1 f2)"
 using cont2mono serial_iterconst_cont assms by blast
   

lemma serial_iterconst_well[simp]:       assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                                  and "spfComp_well f1 f2"
                                  and "no_selfloops f1 f2"
                                  and "pL f1 f2 = {}"
shows "spf_well (Abs_cfun (\<lambda>x. (sbDom\<cdot>x = I f1 f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                            \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))))\<bar>Oc f1 f2))"
 apply (simp add: spf_well_def domIff2 sbdom_rep_eq assms)
 by (smt assms(1) assms(2) assms(3) assms(4) sbunionDom spfCompH2_itDom spfComp_serial_itconst1 
         spfComp_serial_itconst2)
    
       
(* ----------------------------------------------------------------------- *)
section \<open>result\<close>
(* ----------------------------------------------------------------------- *)     
lemma spfCompSeriellGetch: assumes "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                   and "sbDom\<cdot>sb = I f1 f2" 
                   and "spfComp_well f1 f2"
                   and "no_selfloops f1 f2"
                   and "c \<in> spfRan\<cdot>f2" 
                   and "pL f1 f2 = {}"
shows "((spfcomp f1 f2) \<rightleftharpoons> sb) . c = (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (sb\<bar>spfDom\<cdot>f1))) .c"
  apply (simp add: spfcomp_tospfH2)
  apply (subst spfComp_iterconst_eq, simp_all add: assms)
  apply (subst sbunion_getchR, simp_all add: assms)
  by (smt assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) domIff option.exhaust_sel 
        sbleast_sbdom spfLeastIDom spf_sbdom2dom spfran2sbdom spfComp_domranf1)
    
    
chapter \<open>parallel-composition\<close>    
    
 (* TODO: @Marc add theories here *)  
    
    
    
    
    
    
    
    
    
    

  
  
chapter \<open>general comp\<close>
  
(* ----------------------------------------------------------------------- *)
section \<open>sbfix\<close>
(* ----------------------------------------------------------------------- *) 
  
  
  
(* ----------------------------------------------------------------------- *)
section \<open>sbfix\<close>
(* ----------------------------------------------------------------------- *) 
  
end
  