(*  Title:  SPF_Comp.thy
    Author: Jens Christoph Bürger, Marc Wiartalla
    e-mail: jens.buerger@rwth-aachen.de, marc.wiartalla@rwth-aachen.de

    Description: lemmata for composition of SPFs
*)


theory SPF_Comp
  imports SPF SB
    
begin
  
chapter \<open>prelude\<close>  
  
(* ----------------------------------------------------------------------- *)
section \<open>definitions\<close>
(* ----------------------------------------------------------------------- *)
  
subsection \<open>general-composition\<close> 
  



subsubsection \<open>obsolete\<close>  

(* abbrv for the part behind  \<leadsto> in spfcompOld but without the restriction to Oc *) 
abbreviation iter_spfcompOldH2 :: "'a SPF \<Rightarrow> 'a SPF \<Rightarrow> nat \<Rightarrow> 'a SB  \<Rightarrow> 'a SB" where
"(iter_spfcompOldH2 f1 f2 i) \<equiv> (\<lambda> x. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2)))"  

(* newer spfcopmp definition: input is not iterated *)
definition spfCompH :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SB \<Rightarrow> 'm SB  \<rightarrow> 'm SB" where
"spfCompH f1 f2 x \<equiv> (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f2)))"

abbreviation iter_spfCompH :: "'a SPF \<Rightarrow> 'a SPF \<Rightarrow> nat \<Rightarrow> 'a SB  \<Rightarrow> 'a SB" where
"(iter_spfCompH f1 f2 i) \<equiv> (\<lambda> x. iterate i\<cdot>(spfCompH f1 f2 x)\<cdot>((spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)^\<bottom>))" 


subsection \<open>serial and parallel composition\<close>

abbreviation parcomp_well :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> bool" where
"parcomp_well f1 f2 \<equiv> (spfCompL f1 f2 = {}) \<and> (spfRan\<cdot>f1 \<inter> spfRan\<cdot>f2 = {})"
  
abbreviation sercomp_well :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> bool" where
"sercomp_well f1 f2 \<equiv>  (spfRan\<cdot>f1 = spfDom\<cdot>f2) 
                        \<and> (spfCompL f1 f2= {})"

(* operator for parallel composition *)  
definition parcomp :: "'m SPF \<Rightarrow> 'm SPF \<Rightarrow> 'm SPF" ("_\<parallel>_") where
"parcomp f1 f2 \<equiv> Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 ) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f2))))"

(* operator for serial composition *)
definition sercomp :: "'m SPF => 'm SPF => 'm SPF"  ("_\<circ>_") where
"sercomp f1 f2 \<equiv> Abs_CSPF (\<lambda> x. (sbDom\<cdot>x =  spfDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
  
  
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



subsection \<open>sbdom\<close>  

(* The sbDom of the lub of a chain is equals to the sbDom of every chain link *)
  (* Used in cont proof of spfcompOld *)
lemma sbdom_lub_eq: assumes "chain Y" 
                    and  "(sbDom\<cdot>(\<Squnion>i. Y i) = spfCompI f1 f2)"
  shows "\<forall>ia. sbDom\<cdot>(Y ia) = spfCompI f1 f2"
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

    
subsection \<open>sbres\<close>    
   
        (*
lemma sb_rest: "([ch1 \<mapsto> s]\<Omega>)\<bar>{ch1} = [ch1 \<mapsto> (s)]\<Omega>"
  by(simp add: sbrestrict_insert)

lemma sb_onech_getch_insert [simp]:"([ch1 \<mapsto> s]\<Omega>) . ch1 = (s:: nat stream)"
  by(simp add: sbgetch_rep_eq)
  *)
    
subsection \<open>subst\<close>  
  
(* used for substitution *)
lemma two_times_one_insert: "2 * (Suc 0) = Suc(Suc(0))"
  by simp
    
lemma two_times_suci_insert: "2 * (Suc i) = (2 + (2*i))"
  by simp

lemma num3_eq[simp] : " 3 = (Suc(Suc(Suc 0)))"
  using numeral_3_eq_3 by blast
    
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
    
lemma spfComp_Oc_sub_C: assumes "c \<in> spfCompOc f1 f2" shows "c \<in> spfCompC f1 f2"
  by (meson assms set_mp spfOc_sub_C)
    
    
    
    
    
chapter \<open>sbFix2\<close>   

    
    
chapter \<open>sbFix\<close>

   section \<open>sbFix -> sbFix2 compatibility lemmas\<close>

(* cont in X intro rule for SPFs based on sbFix  *)
lemma sbfix_contI2 [simp]: fixes F :: "'m SB \<Rightarrow> 'm SB \<rightarrow> 'm SB"
                            assumes  "cont F" and "\<And> x. (P x) \<Longrightarrow> sbfun_io_eq (F x) cs"
                            and "\<And> x y. sbDom\<cdot>x = sbDom\<cdot>y \<Longrightarrow> P x = P y"
                            shows "cont (\<lambda> x. (P x) \<leadsto> sbFix (F x) cs)"
proof -
  have f1: "(\<lambda> x. (P x) \<leadsto> sbFix (F x) cs) = (\<lambda> x. (P x) \<leadsto> sbFix2 F x cs)"
    apply (subst sbfix_2_sbfix2)
    by simp
  show ?thesis
    apply (subst f1, subst sbFix2_def)
    using sbfix_contI assms by blast
qed

(* the domain is always the same if io_eq holds *)
lemma iter_sbfix_dom: assumes "sbfun_io_eq F cs"
  shows "sbDom\<cdot>(iterate i\<cdot>F\<cdot>(sbLeast cs)) = cs"
    proof (induction i)
      case 0
      thus ?case
        by (simp add: assms(1))
    next
      case (Suc i)
      thus ?case
      proof -
        have "\<And>c. (c\<cdot>(sbLeast cs)::'a SB) \<sqsubseteq> c\<cdot>(F\<cdot>(sbLeast cs))"
          by (simp add: assms monofun_cfun_arg)
        thus ?thesis
          by (metis (no_types) Suc iterate_Suc2 sbdom_eq)
      qed
qed

  (* if input und output of F is equals cs sbFix of f has the same domain *)
lemma sbfix_dom: assumes "sbfun_io_eq (F) cs"
  shows "sbDom\<cdot>(sbFix F cs) =  cs"
proof -
  have "\<And>n. sbfun_io_eq (iterate n\<cdot>(F)) cs"
    by (simp add: assms iter_sbfix_dom)
  thus ?thesis
    by (metis (no_types, lifting) assms sbChain_dom_eq2 sbFix_def sbIterate_chain)
qed


section \<open>fixed point properties\<close>
  (* show that sbFix works similar to the fix operator which works on a pcpo function
     hence "sbfun_io_eq F cs" is a crucial assumptions for the following lemmas, because for
     a fixed domain cs there exists a least sb *)

  (* sbFix calculates the fixed point *)
lemma sbfix_eq: assumes io_eq: "sbfun_io_eq F cs"
  shows "(sbFix F cs) = F\<cdot>(sbFix F cs)"
  apply (simp add: sbFix_def)
   (* perform an chain index shift by 1 *)
  apply (subst lub_range_shift [of _ 1, symmetric])
    apply (simp add: io_eq sbIterate_chain)
    apply (subst contlub_cfun_arg)
      apply (simp add: io_eq sbIterate_chain)
      by simp

  (* the fixed point calculated bs sbFix is smaller than any other fixed point*)
lemma sbfix_least_below: assumes "sbfun_io_eq F cs" and "sbDom\<cdot>x = cs"
  shows "F\<cdot>x \<sqsubseteq> x \<Longrightarrow> (sbFix F cs) \<sqsubseteq> x"
  apply (simp add: sbFix_def)
  apply (rule lub_below)
    apply (simp add: assms sbIterate_chain)
    apply (induct_tac i)
      apply (simp add: assms(2))
      apply (simp add: assms(1))
      apply (erule rev_below_trans)
      by (erule monofun_cfun_arg)


  (* sbFix calculates the least fixed point *)
lemma sbfix_least: assumes "sbfun_io_eq F cs" and "sbDom\<cdot>x = cs"
                    and "F\<cdot>x = x"
  shows "(sbFix F cs) \<sqsubseteq> x"
  by (simp add: assms(1) assms(2) assms(3) sbfix_least_below)

 (* Intro rule for sbfix_eq *)
lemma sbfix_eqI: assumes fp: "F\<cdot>x = x" and lst: "\<And>z. sbDom\<cdot>z = cs \<Longrightarrow> F\<cdot>z = z \<Longrightarrow> x \<sqsubseteq> z"
                 and "sbfun_io_eq F cs" and "sbDom\<cdot>x = cs"
  shows "(sbFix F cs) = x"
proof -
  have f1: "sbFix F cs \<sqsubseteq> x"
    by (simp add: assms(3) assms(4) fp sbfix_least)
  have f2: "sbDom\<cdot>(sbFix F cs) = cs"
    using assms(3) sbfix_dom by blast
  have "sbFix F cs \<sqsubseteq> x"
    using f1 by meson
  thus ?thesis
    using f2 by (metis assms(3) below_antisym lst sbfix_eq)
qed


  (* if sbFix = \<bottom> then F \<bottom> = \<bottom> where \<bottom> = sbLeast cs *)
lemma sbfix_least_iff: assumes "sbfun_io_eq F cs"
  shows "((sbFix F cs) = sbLeast cs) = (F\<cdot>(sbLeast cs) = sbLeast cs)"
proof -
  have "F\<cdot>(sbFix F cs) = sbFix F cs"
    by (metis (full_types) assms sbfix_eq)
  thus ?thesis
    by (metis assms po_eq_conv sbfix_dom sbfix_least sbleast_least)
qed

  (* sbFix is "strict" concerning the least sb with domain cs *)
lemma sbfix_strict: assumes "sbfun_io_eq F cs" and "F\<cdot>(sbLeast cs) = (sbLeast cs)"
  shows "(sbFix F cs) = sbLeast cs"
  by (simp add: assms(2) sbfix_least_iff)

  (* if sbLeast is not a fixed point sbFix does not calculate it *)
lemma sbfix_defined: assumes "sbfun_io_eq F cs" and "F\<cdot>(sbLeast cs) \<noteq> (sbLeast cs)"
  shows "(sbFix F cs) \<noteq> sbLeast cs"
  by (metis assms(1) assms(2) sbfix_eq)

  (* sbFix applied to identity delivers sbLeast *)
lemma sbfix_id [simp]: "(sbFix (\<Lambda> x. x) cs) = (sbLeast cs)"
  by (simp add: sbfix_strict)

  (* sbFix applied to a constant function is the constant *)
lemma sbfix_const [simp]: assumes "sbDom\<cdot>c = cs"
  shows "(sbFix (\<Lambda> x. c) cs) = c"
proof -
  have "sbfun_io_eq (\<Lambda> x. c) cs"
    by (simp add: assms)
  thus ?thesis
    by (metis (no_types) beta_cfun cont_const sbfix_eq)
qed

  (* if P holds for sbLeast and every "F\<cdot>x" it also holds for sbFix F *)
lemma sbfix_ind: assumes "sbfun_io_eq F cs"
                  and "adm P" and "P (sbLeast cs)"
                  and "\<And> x. \<lbrakk>(sbDom\<cdot>x) = cs; P x\<rbrakk> \<Longrightarrow> P (F\<cdot>x)"
  shows "P (sbFix F cs)"
proof -
  have f1: "\<And> n. sbDom\<cdot>(iterate n\<cdot>F\<cdot>(sbLeast cs)) = cs"
    by (simp add: assms(1) iter_sbfix_dom)
  show ?thesis
    unfolding sbFix_def
    apply (subst admD, simp_all add: assms)
      apply (simp add: assms(1) sbIterate_chain)
      apply (rule nat_induct, simp add: assms(3))
      by (simp add: assms(4) f1)
qed

  (* the previous also holds if F is not a cfun but cont *)
lemma cont_sbfix_ind: assumes "cont F" and "sbfun_io_eq (Abs_cfun F) cs"
                       and "adm P" and "P (sbLeast cs)"
                       and "\<And> x. \<lbrakk>(sbDom\<cdot>x) = cs; P x\<rbrakk> \<Longrightarrow> P (F x)"
  shows "P (sbFix (Abs_cfun F) cs)"
  apply (rule sbfix_ind, simp_all add: assms)
  using assms(1) assms(2) by auto

  (* the same holds if the induction starts at F\<cdot>F\<cdot>x*)
lemma sbfix_ind2:  assumes "sbfun_io_eq F cs"
                    and "adm P" and s0: "P ((sbLeast cs))" and s1: "P (F\<cdot>(sbLeast cs))"
                    and s2: "\<And> x. \<lbrakk>(sbDom\<cdot>x) = cs; P x; P (F\<cdot>x)\<rbrakk> \<Longrightarrow> P (F\<cdot>(F\<cdot>x))"
  shows "P (sbFix F cs)"
  unfolding sbFix_def
  apply (subst admD, simp_all add: assms)
    apply (simp add: assms(1) sbIterate_chain)
    apply (rule nat_less_induct)
    apply (case_tac n)
      apply (simp add: s0)
      apply (case_tac nat)
        apply (simp add: s1)
        apply (frule_tac x=nat in spec)
        by (simp add: assms(1) iter_sbfix_dom s2)
  
chapter \<open>comp-helpers\<close>    
  
(* ----------------------------------------------------------------------- *)
section \<open>spfCompH2\<close>
(* ----------------------------------------------------------------------- *)
  (* WARNING this helper is obsolete *)
  
subsection \<open>basic properties\<close>  

  
(* Proof comphelper properties by referring to original comphelper *)
lemma spfCompH2_mono[simp]: "monofun (\<lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1)) 
                                             \<uplus> (f2 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f2)))"
  using cont2mono spfCompHelp_cont by blast

(*Wofür?
lemma spfCompH2_cont[simp]: "cont (\<lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1)) 
                                          \<uplus> (f2 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f2)))"
  using spfCompHelp_cont by blast
*)

lemma helpermonoinX[simp]: shows "monofun (\<lambda> x. spfCompHelp2 f1 f2 x)"
  by(simp add: spfCompHelp2_def)

lemma helpercontinX [simp]: shows "cont (\<lambda> x. spfCompHelp2 f1 f2 x)"
  proof -
     have "\<forall>x. cont (\<lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1))  \<uplus> (f2 \<rightleftharpoons>(z \<bar> spfDom\<cdot>f2)))"
     by simp
     hence "cont (\<lambda>x. \<Lambda> z. x \<uplus> (f1 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f1))  \<uplus> (f2 \<rightleftharpoons> (z \<bar> spfDom\<cdot>f2)))"
       by (simp add: cont2cont_LAM)
     thus ?thesis
       by (simp add: spfCompHelp2_def)
  qed

lemma spfcompOld_tospfH2: "(spfcompOld f1 f2) 
                   = Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfCompI f1 f2) \<leadsto> 
                      (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2))) \<bar> spfCompOc f1 f2)"
  apply (subst spfcompOld_def, subst spfCompHelp2_def, subst spfCompC_def, subst (1 2) spfCompI_def, subst spfCompOc_def)    
  by (metis (no_types) spfCompC_def spfCompI_def spfCompOc_def)
    
    
lemma spfCompH2_getch_outofrange: assumes "c \<notin> spfRan\<cdot>f1" 
                                and "c \<notin> spfRan\<cdot>f2" 
                                and "sbDom\<cdot>sb = spfCompC f1 f2"
  shows "((spfCompHelp2 f1 f2 x)\<cdot>sb) . c = x . c"
  apply (simp add: spfCompHelp2_def)
  apply (subst sbunion_getchL)
  apply (simp add: spfCompC_def assms(2) assms(3) subsetI)
  by (simp add: spfCompC_def Un_assoc assms(1) assms(3))

lemma spfCompH2_dom [simp]: assumes "sbDom\<cdot>sb = spfCompC f1 f2"
  shows "sbDom\<cdot>((spfCompHelp2 f1 f2 x)\<cdot>sb) = (sbDom\<cdot>x \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
  apply (simp add: spfCompHelp2_def)
  proof -
    have f1: "spfDom\<cdot>f1 \<subseteq> sbDom\<cdot>sb"
      by (simp add: spfCompC_def Un_commute Un_left_commute assms)
    have "spfDom\<cdot>f2 \<subseteq> sbDom\<cdot>sb"
      using spfCompC_def assms by auto
    thus "sbDom\<cdot>x \<union> (sbDom\<cdot>(f1 \<rightleftharpoons> (sb\<bar>spfDom\<cdot>f1))) \<union> (sbDom\<cdot> (f2 \<rightleftharpoons> (sb\<bar>spfDom\<cdot>f2))) 
                = (sbDom\<cdot>x \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
      using f1 by simp
qed
 
  
subsection \<open>iterate spfCompH2\<close>
  
  
(* for all i the i'th iteration on spfcompOld is cont as application iterate is cont on cont fun *) 
lemma iter_spfcompOldH2_cont2[simp]: "cont (iter_spfcompOldH2 f1 f2 i)"
  by simp
    
lemma iter_spfcompOldH2_mono[simp]:  "monofun (iter_spfcompOldH2 f1 f2 i)"
  by simp
    
(* replaced spfComp_serialnf_chain *)
lemma iter_spfcompOldH2_chain[simp]: assumes "sbDom\<cdot>x = spfCompI f1 f2"
  shows "chain  (\<lambda>i. iter_spfcompOldH2 f1 f2 i x)"
  apply(rule sbIterate_chain)
  by (simp add: spfCompC_def spfCompI_def assms inf_sup_aci(6))
    
  
lemma spfCompH2_itDom[simp]: assumes "sbDom\<cdot>x = spfCompI f1 f2"
  shows "sbfun_io_eq (iterate i\<cdot>(spfCompHelp2 f1 f2 x)) (spfCompC f1 f2)"
  apply (induct_tac i)
   apply auto[1]
  by (simp add: spfCompC_def spfCompI_def assms inf_sup_aci(6))
  
  
lemma spfCompH2_itgetChI: assumes "sbDom\<cdot>x = spfCompI f1 f2" 
                      and "spfComp_well f1 f2"
                      and "c \<in> spfCompI f1 f2"
  shows "iter_spfcompOldH2 f1 f2 (Suc i) x . c = x .c"
  apply (unfold iterate_Suc, subst spfCompHelp2_def)
  apply (simp)
  apply (subst sbunion_getchL)
  apply (metis spfCompC_def DiffD2 spfCompI_def UnI2 assms(1) assms(3) inf_sup_ord(4) 
               le_supI1 spfCompH2_itDom spfRanRestrict)
  apply (subst sbunion_getchL)
   apply (metis spfCompC_def DiffD2 spfCompI_def UnI1 Un_upper1 assms(1) assms(3) 
                le_supI1 spfCompH2_itDom spfRanRestrict)
   by (simp)


lemma spfCompH2_itResI: assumes "sbDom\<cdot>x = spfCompI f1 f2" 
                    and "spfComp_well f1 f2"
  shows "(iter_spfcompOldH2 f1 f2 (Suc i) x) \<bar> (spfCompI f1 f2) = x"
  apply (rule sb_eq)
   apply (simp add: assms(1) inf_sup_aci(1) inf_sup_aci(6))
   using assms(1) assms(2) spfCompH2_itgetChI by fastforce
  

subsection \<open>lub iterate spfCompH2\<close>
   
(* the lub over the iterations of spfcompOldH2 is monotone if the assumtions hold *)
  (* requires chain property, hence the input must have the right domain *)
lemma lub_iter_spfCompHelp2_mono_req: assumes "x \<sqsubseteq> y" and  "sbDom\<cdot>x = spfCompI f1 f2"
  shows "(\<Squnion>i.(iter_spfcompOldH2 f1 f2 i) x) \<sqsubseteq> (\<Squnion>i.(iter_spfcompOldH2 f1 f2 i) y)"
    apply (rule lub_iter_sbfix2_mono_req)
    by (simp_all add: assms inf_sup_aci(6) spfCompI_def spfCompC_def)

(* the lub over the iteration is always mono, the correct domain is assured via \<leadsto> *)
lemma if_lub_iter_spfCompHelp2_mono_req: assumes "x \<sqsubseteq> y" 
  shows "((\<lambda> x. (sbDom\<cdot>x = spfCompI f1 f2) \<leadsto> (\<Squnion>i.(iter_spfcompOldH2 f1 f2 i) x)) x) 
              \<sqsubseteq> ((\<lambda> x. (sbDom\<cdot>x = spfCompI f1 f2) \<leadsto> (\<Squnion>i.(iter_spfcompOldH2 f1 f2 i) x)) y)"
  apply (rule if_lub_iter_sbfix2_mono_req)
    by (simp_all add: assms inf_sup_aci(6) spfCompI_def spfCompC_def)
    
(* the lub of iter_spfcompOldH2, when applied to a chain, is again a chain *)
  (* this property follows from the monotonicy of lub_iter_spfCompHelp2 *)
lemma chain_lub_iter_spfcompOldH2: assumes  "chain Y" 
                                and  "(sbDom\<cdot>(\<Squnion>i. Y i) = spfCompI f1 f2)"
  shows "chain (\<lambda>i. \<Squnion>ia. iter_spfcompOldH2 f1 f2 ia (Y i))"   
  apply (rule chain_lub_iter_sbfix2)
  by (simp_all add: assms inf_sup_aci(6) spfCompI_def spfCompC_def)




(* ----------------------------------------------------------------------- *)
section \<open>spfCompH\<close>
(* ----------------------------------------------------------------------- *)
  (* similar to spfCompH2 but does not output the input, nevertheless its lub 
     is equal to the one of spfCompH2 as shown later *)

subsection \<open>basic properties\<close>
  
subsubsection \<open>cont\<close>
  
lemma spfCompH_cont[simp]: 
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
    by simp
qed
  
lemma spfCompH_cont2[simp]: 
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
    by simp
qed
  
  
lemma spfCompH_continX[simp]: "cont (\<lambda> x. spfCompH f1 f2 x)"
proof -
  have "cont (\<lambda> x. \<Lambda> z. ((f1\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> spfDom\<cdot>f2))))"
    by (simp add: cont2cont_LAM)
  thus ?thesis
    by (simp add: spfCompH_def)
qed
   
subsubsection \<open>dom\<close>
  
lemma spfCompH_dom [simp]: assumes "sbDom\<cdot>x = spfCompI f1 f2"
                            and "sbDom\<cdot>sb = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
                          shows "sbDom\<cdot>((spfCompH f1 f2 x)\<cdot>sb) = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
proof -
  have f1: "sbDom\<cdot>(f1 \<rightleftharpoons> ((x \<uplus> sb)  \<bar> spfDom\<cdot>f1)) = spfRan\<cdot>f1"
    by (simp add: spfCompI_def assms(1) assms(2) inf_sup_aci(6))
      moreover
  have f2: "sbDom\<cdot>(f2 \<rightleftharpoons> ((x \<uplus> sb)  \<bar> spfDom\<cdot>f2)) = spfRan\<cdot>f2"
    by (simp add: spfCompI_def assms(1) assms(2) sup.coboundedI1)
      ultimately
  show ?thesis
    by (simp add: f1 f2 spfCompH_def assms)
qed

 
  
subsection \<open>iterate spfCompH\<close>  
  
lemma iter_spfCompH_cont[simp]: "cont (\<lambda>x. iter_spfCompH f1 f2 i x)"
  by simp
    
lemma iter_spfCompH_mono[simp]: "monofun (\<lambda>x. iter_spfCompH f1 f2 i x)"
  by (simp add: cont2mono)
    
lemma iter_spfCompH_mono2:  assumes "x \<sqsubseteq> y"
  shows "\<forall>i. ((iter_spfCompH f1 f2 i) x) \<sqsubseteq> ((iter_spfCompH f1 f2 i) y)"
  using assms monofun_def by fastforce
  
lemma iter_spfCompH_chain[simp]: assumes "sbDom\<cdot>x = spfCompI f1 f2"
  shows "chain (\<lambda> i. iter_spfCompH f1 f2 i x)"
  by (simp add: assms sbIterate_chain)
    
lemma iter_spfCompH_dom[simp]: assumes "sbDom\<cdot>x = spfCompI f1 f2" 
  shows "sbDom\<cdot>(iter_spfCompH f1 f2 i x) = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
  by (simp add: assms iter_sbfix2_dom)
  
  
subsection \<open>lub iterate spfCompH\<close> 
  
lemma lub_iter_spfCompH_dom[simp]: assumes "sbDom\<cdot>x = spfCompI f1 f2" 
  shows "sbDom\<cdot>(\<Squnion>i. iter_spfCompH f1 f2 i x) = (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)"
  by (simp add: lub_iter_sbfix2_dom assms) 
  
  
  
  
    
    
chapter \<open>serial-composition\<close>
(* This was the first approach of the evaluation of the composition *)
  (* The situation here is that the domain of one function is exactly the range of another function
     other internal channels do not exist *)
  
(* ----------------------------------------------------------------------- *)
section \<open>sercomp channel domain lemmata\<close>
(* ----------------------------------------------------------------------- *)

lemma spfComp_test8: assumes "sercomp_well f1 f2" 
                       and "sbDom\<cdot>x = spfCompI f1 f2"
  shows "spfDom\<cdot>f1  = (spfCompI f1 f2)"
  proof -
    have "spfDom\<cdot>f1 \<inter> spfRan\<cdot>f1 = {} \<and> spfDom\<cdot>f1 \<inter> spfRan\<cdot>f2 = {}"
      by (metis (no_types) Un_empty assms(1) pL_def)
    thus ?thesis
      by (simp add: Diff_Un Diff_triv spfCompI_def Un_Diff assms(1))
  qed
    
(* for simp usage when the resut is input for f2 *)
lemma spfComp_domranf1: assumes "sercomp_well f1 f2" 
                        and "sbDom\<cdot>sb = spfCompI f1 f2"
  shows "(sbDom\<cdot>(f1 \<rightleftharpoons> (sb\<bar>spfDom\<cdot>f1))) = spfRan\<cdot>f1"
  using assms(1) assms(2)
  by (metis SPF_Comp.spfComp_test8 equalityE spfRanRestrict)
    

lemma spfComp_I_domf1_eq: assumes "sercomp_well f1 f2" 
                          and "sbDom\<cdot>sb = spfCompI f1 f2" 
  shows "spfCompI f1 f2 = spfDom\<cdot>f1"
  apply(simp add: spfCompI_def, subst assms(1))
  using assms(1) assms(2) spfCompI_def spfComp_test8 by blast
    

lemma spfComp_getC_Oc[simp]:  assumes "c \<in> spfRan\<cdot>f2" 
  shows "c \<in> spfCompOc f1 f2"
  by (simp add: spfCompOc_def assms(1))
    
lemma helper_cont[simp] : "cont (Rep_cfun (spfCompHelp2 f1 f2 x))"
by simp 


(* ----------------------------------------------------------------------- *)
section \<open>iteration lemmata\<close>
(* ----------------------------------------------------------------------- *)
  
(* lemma sercomp2spfComp[simp]:"sercomp_well f1 f2 \<Longrightarrow> spfComp_well f1 f2 "
by(simp add: spfComp_well_def pL_def)
*)

(* proof equality of iterate expressions for f1 and f2 *)
lemma spfComp_serialf1: assumes "sercomp_well f1 f2" 
                       and "sbDom\<cdot>x = spfCompI f1 f2"
                       and "c \<in> spfRan\<cdot>f1"                                           
shows "(iter_spfcompOldH2 f1 f2 (Suc (Suc i)) x) . c = (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1)) . c"
  apply (subst iterate_Suc)
  apply(subst spfCompHelp2_def, simp)
  apply (subst sbunion_getchL)
   apply (smt assms(1) assms(2) assms(3) sercomp2spfComp disjoint_iff_not_equal inf_sup_ord(4) 
              le_supI1 spfCompH2_dom spfCompH2_itDom spfComp_well_def spfRanRestrict)
   apply (subst sbunion_getchR)
   apply (metis assms(1) assms(2) assms(3) iterate_Suc spfCompH2_itDom spfComp_test8 
          spfI_sub_C spfRanRestrict)
  by (metis assms(1) assms(2) sercomp2spfComp iterate_Suc sbrestrict_id 
      spfComp_I_domf1_eq spfCompH2_itResI subsetI)
  
lemma spfComp_serialf2: assumes "sercomp_well f1 f2" 
                       and "sbDom\<cdot>x = spfCompI f1 f2"
                       and "c \<in> spfRan\<cdot>f2"
  shows "(iter_spfcompOldH2 f1 f2 (Suc (Suc (Suc i))) x) . c
                   = (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))) . c"
  apply (subst iterate_Suc)
  apply (subst spfCompHelp2_def)
  apply (simp)
  apply (subst sbunion_getchR)
  apply (metis assms(1) assms(2) assms(3) inf_sup_ord(4) iterate_Suc le_supI1 
          spfCompH2_dom spfCompH2_itDom spfRanRestrict)
    by (smt Int_absorb1 assms(1) assms(2) assms(3)  inf_sup_ord(4) iterate_Suc 
            le_supI1 sb_eq sbrestrict2sbgetch sbrestrict_sbdom spfCompH2_dom spfComp_domranf1 
            spfCompH2_itDom spfComp_serialf1)

(* this is the core lemma for the equality proofs *)
lemma spfComp_serial : assumes "sercomp_well f1 f2" 
                       and "sbDom\<cdot>x = spfCompI f1 f2"
  shows "(iter_spfcompOldH2 f1 f2 (Suc (Suc (Suc i))) x) = x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                      \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1)))" (is "?L = ?R")
  apply(rule sb_eq)
  apply (smt spfCompC_def assms(1) assms(2)inf_sup_ord(4) sbunionDom sbunion_restrict 
             spfComp_I_domf1_eq spfComp_domranf1 spfCompH2_itDom spfRanRestrict sup.right_idem)
  by (smt assms(1) assms(2) inf_sup_ord(4) iterate_Suc sbunionDom 
          sbunion_getchL sbunion_getchR sbunion_restrict spfComp_domranf1 spfCompH2_getch_outofrange 
          spfCompH2_itDom spfComp_serialf1 spfComp_serialf2 spfRanRestrict)
        
        
lemma spfComp_serialnf_chain: assumes "sbDom\<cdot>x = spfCompI f1 f2"
  shows "chain (\<lambda>i. iter_spfcompOldH2 f1 f2 i x)"
  apply(rule sbIterate_chain)
  apply (simp add: assms spfCompC_def spfCompI_def)
  by blast

  
(* ----------------------------------------------------------------------- *)
section \<open>lub iteration\<close>
(* ----------------------------------------------------------------------- *) 
  
  (* show that the chain has it's maximum at the third chain element *)
lemma spfComp_serial_max: assumes "sercomp_well f1 f2" 
                          and "sbDom\<cdot>x = spfCompI f1 f2"
  shows "max_in_chain 3 (\<lambda>i. iter_spfcompOldH2 f1 f2 i x)"
  apply(rule max_in_chainI, subst num3_eq)
  apply(subst spfComp_serial, simp_all add: assms)
  by (metis Suc_le_D Suc_le_lessD assms(1) assms(2) less_Suc_eq_le 
        spfComp_serial)
      
  (* show that lub can be described by constant if no feedback channels exist *)
lemma spfComp_serial_itconst1 [simp]: assumes "sercomp_well f1 f2" 
                                      and "sbDom\<cdot>x = spfCompI f1 f2"
  shows "(\<Squnion>i. iter_spfcompOldH2 f1 f2 i x) = iter_spfcompOldH2 f1 f2 3 x"
  using assms(1) assms(2) maxinch_is_thelub spfComp_serial_max 
    spfComp_serialnf_chain by blast
    
lemma spfComp_serial_itconst2 [simp]: assumes "sercomp_well f1 f2" 
                                      and "sbDom\<cdot>x = spfCompI f1 f2"
  shows "(\<Squnion>i. iter_spfcompOldH2 f1 f2 i x) = x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                                             \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1)))"
  by (metis One_nat_def Suc_1 assms(1) assms(2)
            spfComp_serial spfComp_serial_itconst1 num3_eq)
         
          
(* ----------------------------------------------------------------------- *)
section \<open>iter const\<close>
(* ----------------------------------------------------------------------- *)
          
(* NOW BRING IT ALL TOGETHER *)

(* Use the lub equality to simplify the inner expression and show that the composition is a 
   well defined spf *)
          
(* show that spfcompOld can be simplified to SPF without iterate if the assumtion hold *)
lemma spfComp_iterconst_eq[simp]: assumes "sercomp_well f1 f2"  
shows "(\<lambda>x. (sbDom\<cdot>x = spfCompI f1 f2)\<leadsto>(\<Squnion>i. iter_spfcompOldH2 f1 f2 i x)\<bar>spfCompOc f1 f2)
  = (\<lambda>x. (sbDom\<cdot>x = spfCompI f1 f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))))\<bar>spfCompOc f1 f2)"
proof -
  have "\<forall>s. (sbDom\<cdot>s \<noteq> spfCompI f1 f2  \<or> 
        (Some ((\<Squnion>n. iterate n\<cdot>(spfCompHelp2 f1 f2 s)\<cdot> (sbLeast (spfCompC f1 f2)))\<bar>spfCompOc f1 f2) 
        = Some (s \<uplus> (f1 \<rightleftharpoons> (s\<bar>spfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (s\<bar>spfDom\<cdot> f1)))\<bar>spfCompOc f1 f2)))"
    by (metis assms(1)  spfComp_serial_itconst2)
  thus ?thesis
    by meson
qed
  
lemma serial_iterconst_cont[simp]:    
shows "cont (\<lambda>x. (sbDom\<cdot>x = spfCompI f1 f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                                    \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))))\<bar>spfCompOc f1 f2)"
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
      by(simp add:  )
  qed
    
lemma serial_iterconst_monofun[simp]:
shows "monofun (\<lambda>x. (sbDom\<cdot>x = spfCompI f1 f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                                    \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))))\<bar>spfCompOc f1 f2)"
 using cont2mono serial_iterconst_cont by blast
   

lemma serial_iterconst_well[simp]:       assumes "sercomp_well f1 f2"
shows "spf_well (Abs_cfun (\<lambda>x. (sbDom\<cdot>x = spfCompI f1 f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                            \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>spfDom\<cdot>f1))))\<bar>spfCompOc f1 f2))"
 apply (simp add: spf_well_def domIff2 sbdom_rep_eq assms)
 by (smt assms(1) sbunionDom spfCompH2_itDom spfComp_serial_itconst1 
         spfComp_serial_itconst2)
    
       
(* ----------------------------------------------------------------------- *)
section \<open>result\<close>
(* ----------------------------------------------------------------------- *)     
lemma spfCompSeriellGetch: assumes "sercomp_well f1 f2"
                   and "sbDom\<cdot>sb = spfCompI f1 f2"
                   and "c \<in> spfRan\<cdot>f2"
shows "((spfcompOld f1 f2) \<rightleftharpoons> sb) . c = (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (sb\<bar>spfDom\<cdot>f1))) .c"
  apply (simp add: spfcompOld_tospfH2)
  apply (subst spfComp_iterconst_eq, simp_all add: assms)
  apply (subst sbunion_getchR, simp_all add: assms)
  by (smt assms(1) assms(2) assms(3) domIff option.exhaust_sel 
        sbleast_sbdom spfLeastIDom spf_sbdom2dom spfran2sbdom spfComp_domranf1)
    
    
chapter \<open>parallel-composition\<close>    
    
 (* TODO: @Marc add theories here *)  
    
    
section\<open>parcomp channel domain lemmata\<close>     
    
lemma [simp]: assumes "c \<in> spfRan\<cdot>f1"
  shows "c \<notin> spfCompI f1 f2"
by (simp add: spfCompI_def assms(1))

lemma [simp]: assumes "c \<in> spfRan\<cdot>f1"
                  and "parcomp_well f1 f2"
  shows "c \<notin> spfRan\<cdot>f2"
using assms(1) assms(2) by auto

lemma [simp]: assumes "c \<in> spfRan\<cdot>f1"
                  and "spfCompL f1 f2 = {}"
  shows "c \<notin> spfDom\<cdot>f1 \<and> c \<notin> spfDom\<cdot>f2"
using spfCompL_def assms(1) assms(2) by blast

lemma [simp]: assumes "spfCompL f1 f2 = {}"
  shows "spfDom\<cdot>f1 \<subseteq> spfCompI f1 f2"
apply(auto simp add: spfCompI_def)
using spfCompL_def assms apply fastforce
using spfCompL_def assms by fastforce

lemma  spfComp_I_domf1f2_eq[simp]: assumes "spfCompL f1 f2 = {}" 
  shows "spfCompI f1 f2 = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2"
by (metis Diff_triv spfCompI_def spfCompL_def assms)

lemma sbunion_getchM: assumes "c \<notin> sbDom\<cdot>b1"
                          and "c \<notin> sbDom\<cdot>b3"
  shows "b1\<uplus>b2\<uplus>b3 . c = b2 . c"
by (metis assms(1) assms(2) domIff sbdom_insert sbgetch_insert sbunion_getchL sbunion_getchR)

lemma spfComp_cInOc1:  assumes "parcomp_well f1 f2"
                          and "c \<in> spfRan\<cdot>f1" 
  shows "c \<in> spfCompOc f1 f2"
  using spfCompL_def spfCompOc_def assms(2) by blast

lemma spfComp_domranf1_2: assumes "parcomp_well f1 f2"
                        and "sbDom\<cdot>sb = spfCompI f1 f2"
  shows "(sbDom\<cdot>Rep_CSPF f1\<rightharpoonup>(sb\<bar>spfDom\<cdot>f1)) = spfRan\<cdot>f1"
by (simp add: assms(1) assms(2))    
    
section\<open>lub iteration\<close>        

lemma spfComp_parallelf1 : assumes"parcomp_well f1 f2"
                              and "sbDom\<cdot>x = spfCompI f1 f2"
                              and "c \<in> spfRan\<cdot>f1" 
  shows "(iterate (Suc (Suc i))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2))) . c
                  = (x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2))) . c"
  apply(subst iterate_Suc)
  apply(subst spfCompHelp2_def, simp)
   apply(subst sbunion_getchL)
   apply (metis DiffE Un_Diff_Int Un_subset_iff assms(1) assms(2) assms(3) iterate_Suc 
      spfCompH2_itDom spfComp_I_domf1f2_eq spfI_sub_C spfRanRestrict sup_bot.right_neutral)
    by (smt Int_absorb1 spfCompH2_itResI spfI_sub_C assms(1) assms(2) assms(3)  inf_sup_ord(4) 
       iterate_Suc sb_eq sbrestrict2sbgetch sbrestrict_sbdom sbunion_associative sbunion_commutative 
       sbunion_getchR spfComp_I_domf1f2_eq spfCompH2_itDom spfComp_well_def spfRanRestrict 
       subsetCE sup.bounded_iff sup_ge1)
  
lemma spfComp_parallelf2 : assumes"parcomp_well f1 f2"
                              and "sbDom\<cdot>x = spfCompI f1 f2"
                              and "c \<in> spfRan\<cdot>f2" 
  shows "(iterate (Suc (Suc i))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2))) . c
                  = (x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2))) . c"
  apply(subst iterate_Suc)
  apply(subst spfCompHelp2_def, simp)
  apply(subst sbunion_getchR)
  apply (metis assms(1) assms(2) assms(3) iterate_Suc le_sup_iff spfCompH2_itDom 
          spfComp_I_domf1f2_eq spfI_sub_C spfRanRestrict)
    apply(subst sbunion_getchR)
   apply(simp add: assms(1) assms(2) assms(3))
     by (smt Int_absorb1 spfCompH2_itResI spfI_sub_C assms(1) assms(2) assms(3) inf_sup_ord(4) 
       iterate_Suc sb_eq sbrestrict2sbgetch sbrestrict_sbdom sbunion_associative sbunion_commutative 
       sbunion_getchR spfComp_I_domf1f2_eq spfCompH2_itDom spfComp_well_def spfRanRestrict 
       subsetCE sup.bounded_iff sup_ge1)
 
lemma spfComp_parallel : assumes" parcomp_well f1 f2"
                            and "sbDom\<cdot>x = spfCompI f1 f2"
  shows "(iterate (Suc (Suc i))\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2)))
                  = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2))" (is "?L = ?R")
  apply(rule sb_eq)
    apply (metis (mono_tags, lifting) spfCompC_def SPF_Comp.spfCompH2_itDom Un_upper2 assms(1) assms(2) 
            sbunionDom spfComp_I_domf1f2_eq spfComp_domranf1_2 spfRanRestrict)
       by (smt SPF_Comp.spfCompH2_getch_outofrange SPF_Comp.spfCompH2_itDom assms(1) assms(2) 
          inf_sup_ord(4) iterate_Suc sbunion_getchL spfComp_I_domf1f2_eq spfComp_domranf1_2 
          spfComp_parallelf1 spfComp_parallelf2 spfRanRestrict)
    
lemma spfComp_parallel_max: assumes "parcomp_well f1 f2" 
                                and "sbDom\<cdot>x = spfCompI f1 f2"
  shows "max_in_chain 2 (\<lambda>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2)))"
apply(rule max_in_chainI, subst Num.numeral_2_eq_2)
apply(subst spfComp_parallel, simp_all add: assms)
by (metis Suc_le_D Suc_le_lessD assms(1) assms(2) le_simps(2) numerals(2) spfComp_parallel) 
  
lemma spfComp_parallel_itconst1 [simp]: assumes "parcomp_well f1 f2"
                                            and "sbDom\<cdot>x = spfCompI f1 f2"
  shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2)))
               = iterate 2\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2))"
using assms(1) assms(2)
    maxinch_is_thelub spfComp_parallel_max  spfComp_serialnf_chain by blast

lemma spfComp_parallel_itconst2 [simp]: assumes "parcomp_well f1 f2" 
                                     and "sbDom\<cdot>x = spfCompI f1 f2"
  shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2)))
            = x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2))"
by (metis One_nat_def Suc_1 assms(1) assms(2)
    spfComp_parallel spfComp_parallel_itconst1)     
    
section\<open>iter const\<close>

lemma spfComp_parallel_iterconst_eq1 [simp]:  assumes "parcomp_well f1 f2" shows
"(\<lambda>x. (sbDom\<cdot>x = spfCompI f1 f2)\<leadsto>(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2)))\<bar>spfCompOc f1 f2)
              = (\<lambda>x. (sbDom\<cdot>x = spfCompI f1 f2)\<leadsto>(  x \<uplus> ((Rep_CSPF f1) \<rightharpoonup> (x \<bar>spfDom\<cdot>f1)) \<uplus> ((Rep_CSPF f2) \<rightharpoonup> (x\<bar>spfDom\<cdot>f2)) )\<bar>spfCompOc f1 f2)"
proof -
    have "\<forall>s. (sbDom\<cdot>s \<noteq> spfCompI f1 f2  \<or> (Some ((\<Squnion>n. iterate n\<cdot>(spfCompHelp2 f1 f2 s)\<cdot> (sbLeast (spfCompC f1 f2)))\<bar>spfCompOc f1 f2) = Some (s \<uplus> (Rep_CSPF f1\<rightharpoonup>(s\<bar>spfDom\<cdot>f1)) \<uplus>  ((Rep_CSPF f2) \<rightharpoonup> (s\<bar>spfDom\<cdot>f2))\<bar>spfCompOc f1 f2)))"
     by (metis assms(1) spfComp_parallel_itconst2)
  thus ?thesis
    by meson
qed  
  
lemma parallel_iterconst_cont[simp]:
shows "cont (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                                    \<uplus> (f2 \<rightleftharpoons>(x\<bar>spfDom\<cdot>f2)) )\<bar>spfCompOc f1 f2)"
proof -
   have "cont (\<lambda>s. (Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))"
     by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
   hence "cont (\<lambda>s. sbUnion\<cdot> (s  \<uplus>  ((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1)))) \<and> cont (\<lambda>s. Rep_SPF f2\<cdot>(s\<bar>spfDom\<cdot>f2))"
     by simp
   hence "cont (\<lambda>s. s  \<uplus>  ((Rep_cfun (Rep_SPF f1))\<rightharpoonup>(s\<bar>spfDom\<cdot>f1))   \<uplus>  ((Rep_cfun (Rep_SPF f2))\<rightharpoonup>(s\<bar>spfDom\<cdot>f2))  )"
     using cont2cont_APP cont_compose op_the_cont by blast 
   thus ?thesis
     by(simp add:  )
  qed
       
lemma parallel_iterconst_monofun[simp]:  assumes "parcomp_well f1 f2" 
shows "monofun (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                                    \<uplus> (f2 \<rightleftharpoons>(x\<bar>spfDom\<cdot>f2)) )\<bar>spfCompOc f1 f2)"
  using cont2mono parallel_iterconst_cont assms by blast
    
lemma parallel_iterconst_well[simp]: assumes "parcomp_well f1 f2"
shows "spf_well (Abs_cfun (\<lambda>x. (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2)\<leadsto>(x \<uplus> (f1 \<rightleftharpoons> (x \<bar>spfDom\<cdot>f1)) 
                                    \<uplus> (f2 \<rightleftharpoons>(x\<bar>spfDom\<cdot>f2)) )\<bar>spfCompOc f1 f2))"
  apply (simp add: spf_well_def domIff2 sbdom_rep_eq assms)
    by auto
  
section\<open>result\<close>    
  
lemma spfCompParallelGetch1: assumes "parcomp_well f1 f2"
                                and "sbDom\<cdot>sb = spfCompI f1 f2"
                                and "c \<in> spfRan\<cdot>f1" 
  shows "((spfcompOld f1 f2) \<rightleftharpoons> sb) . c = (f1 \<rightleftharpoons> (sb\<bar>spfDom\<cdot>f1)) . c"
  apply(simp only: spfcompOld_tospfH2)
  apply (subst  spfComp_parallel_iterconst_eq1,  simp_all add: assms)
  apply(simp_all add: spfComp_cInOc1 assms)
  apply(subst sbunion_getchM, simp_all)
  apply(simp_all add: assms)
  using assms(1) assms(3) spfCompL_def by blast+
    
lemma spfCompParallelGetch2: assumes "parcomp_well f1 f2"
                                and "sbDom\<cdot>sb = spfCompI f1 f2"
                                and "c \<in> spfRan\<cdot>f2" 
  shows "((spfcompOld f1 f2) \<rightleftharpoons> sb) . c = (f2 \<rightleftharpoons> (sb\<bar>spfDom\<cdot>f2)) . c"
  apply (simp only: spfcompOld_tospfH2)
  apply (subst  spfComp_parallel_iterconst_eq1)
  by (simp_all add: assms)  

    
chapter \<open>general comp\<close>
  
(* ----------------------------------------------------------------------- *)
section \<open>spfcompOld1\<close>
(* ----------------------------------------------------------------------- *) 
  (* WARNING: This composition type is obsolete *)
  (* based on spfCompH2 \<Rightarrow> Iterates the input as well *)
  
subsection \<open>mono\<close>  

(* Show that spfComp is monofun in x independent from the function it's applied to *)
  (* Used in cont proof, hence must be proofed independently *)
lemma spf_comp_mono[simp]: "monofun (\<lambda> x. (sbDom\<cdot>x = spfCompI f1 f2) 
                                          \<leadsto> (\<Squnion>i.(iter_spfcompOldH2 f1 f2 i) x)  \<bar> spfCompOc f1 f2 )" 
  proof -
    have "monofun (\<lambda> x. (sbDom\<cdot>x = spfCompI f1 f2) \<leadsto> (\<Squnion>i.(iter_spfcompOldH2 f1 f2 i) x) )"
      by (metis (no_types, lifting) lub_eq monofun_def if_lub_iter_spfCompHelp2_mono_req)
    thus ?thesis
      by (smt monofun_cfun_arg monofun_def sbdom_eq some_below some_below2)
  qed

    
subsection \<open>cont\<close>   
(* General proof Idea: show that part behind \<leadsto> is cont if input has correct domain and otherwise. 
   This procedure is necessary as the chain properties of iter_spcompH2 only hold if the input 
   domain is correct *)
  
(* Show that 2nd goal from contI holds if input on spfcompOld has the correct domain *)     
lemma chain_if_lub_iter_spfcompOldH2_domI: assumes "(sbDom\<cdot>(\<Squnion>i. Y i) = spfCompI f1 f2)"
  shows "chain Y \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) = spfCompI f1 f2)
                              \<leadsto>(\<Squnion>i. iter_spfcompOldH2 f1 f2 i (\<Squnion>i. Y i))  \<bar> spfCompOc f1 f2 
                      \<sqsubseteq> (\<Squnion>i. (sbDom\<cdot>(Y i) = spfCompI f1 f2)
                              \<leadsto>(\<Squnion>ia. iter_spfcompOldH2 f1 f2 ia (Y i))  \<bar> spfCompOc f1 f2)"
  proof -
      (* Part I: Show that part after \<leadsto> has 2nd property of compI *)
      have f1: "\<And>i. cont (\<lambda>x. iter_spfcompOldH2 f1 f2 i x)"
        by (simp) 
      hence f2: "chain Y \<longrightarrow> (\<Squnion>i. iter_spfcompOldH2 f1 f2 i (\<Squnion>i. Y i)) 
                              = (\<Squnion> ia i.  iter_spfcompOldH2 f1 f2 ia (Y i))"
        by (rule cont2lub_lub_eq)
      moreover
      have f3: "\<forall>ia. chain Y \<longrightarrow>  sbDom\<cdot>(Y ia) = spfCompI f1 f2"
        by (simp add: sbdom_lub_eq assms)
      ultimately
      have f4: "chain Y \<longrightarrow> (\<Squnion>i ia. iter_spfcompOldH2 f1 f2 i (Y ia))  
                              \<sqsubseteq> (\<Squnion>i ia.  iter_spfcompOldH2 f1 f2 ia (Y i))"
        by (simp add: diag_lub ch2ch_cont f1 f2 f3 assms)
          (* now show that property also holds if result is restricted to Oc *)
      hence f5: "chain Y \<longrightarrow> (\<Squnion>i ia. iter_spfcompOldH2 f1 f2 i (Y ia)) \<bar> spfCompOc f1 f2  
                              \<sqsubseteq> (\<Squnion>i ia.  iter_spfcompOldH2 f1 f2 ia (Y i)) \<bar> spfCompOc f1 f2"
        using monofun_cfun_arg by blast
   
      (*  Part II: Show that Some packaging does not change \<sqsubseteq> relation from before*)    
      have f10: "chain Y \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) = spfCompI f1 f2)
                                            \<leadsto>(\<Squnion>i. iter_spfcompOldH2 f1 f2 i (\<Squnion>i. Y i)) \<bar> spfCompOc f1 f2
            = Some ((\<Squnion>i. iter_spfcompOldH2 f1 f2 i (\<Squnion>i. Y i)) \<bar> spfCompOc f1 f2)"
        by (simp add: assms)
      have f11: "chain Y \<longrightarrow> (\<Squnion>i. (sbDom\<cdot>(Y i) = spfCompI f1 f2)
                                            \<leadsto>(\<Squnion>ia. iter_spfcompOldH2 f1 f2 ia (Y i)) \<bar> spfCompOc f1 f2) 
                  = Some((\<Squnion>i ia. iter_spfcompOldH2 f1 f2 ia (Y i)) \<bar> spfCompOc f1 f2)"
        proof -
          have f111: "chain Y \<longrightarrow> (\<Squnion>i. (sbDom\<cdot>(Y i) = spfCompI f1 f2)
                                             \<leadsto>(\<Squnion>ia. iter_spfcompOldH2 f1 f2 ia (Y i)) \<bar> spfCompOc f1 f2)
                       = (\<Squnion>i. Some ((\<Squnion>ia. iter_spfcompOldH2 f1 f2 ia (Y i))\<bar> spfCompOc f1 f2))"
            by (simp add: f3 assms)
          (* with chain_lub_iter_spfcompOldH2 some can now be pulled out *)
          have f212: "chain Y \<longrightarrow> (\<Squnion>i. Some ((\<Squnion>ia. iter_spfcompOldH2 f1 f2 ia (Y i))\<bar> spfCompOc f1 f2))
                        = Some((\<Squnion>i ia. iter_spfcompOldH2 f1 f2 ia (Y i)) \<bar> spfCompOc f1 f2)"
             by (simp add: contlub_cfun_arg some_lub_chain_eq chain_lub_iter_spfcompOldH2 assms)
              thus ?thesis
          using f111 by auto
      qed   
        (* PART III: as Some on both sides can be pulled out (Part II) the thesis follows 
            directly with Part I *)
      thus ?thesis
        by (simp add: f2 f10 f5 some_below)
  qed

    
(* Show that 2nd goal from contI holds independent from the input *)    
lemma chain_if_lub_iter_spfcompOldH2: "chain Y \<longrightarrow>
        (sbDom\<cdot>(\<Squnion>i. Y i) = spfCompI f1 f2)\<leadsto>(\<Squnion>i. iter_spfcompOldH2 f1 f2 i (\<Squnion>i. Y i))  \<bar> spfCompOc f1 f2  \<sqsubseteq>
        (\<Squnion>i. (sbDom\<cdot>(Y i) = spfCompI f1 f2)\<leadsto>(\<Squnion>ia. iter_spfcompOldH2 f1 f2 ia (Y i))  \<bar> spfCompOc f1 f2)"   
  proof -
       have case1: "chain Y \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) \<noteq> spfCompI f1 f2) \<longrightarrow>
          (sbDom\<cdot>(\<Squnion>i. Y i) = spfCompI f1 f2)\<leadsto>(\<Squnion>i. iter_spfcompOldH2 f1 f2 i (\<Squnion>i. Y i))  \<bar> spfCompOc f1 f2 \<sqsubseteq>
          (\<Squnion>i. (sbDom\<cdot>(Y i) = spfCompI f1 f2)\<leadsto>(\<Squnion>ia. iter_spfcompOldH2 f1 f2 ia (Y i))  \<bar> spfCompOc f1 f2)"
         by (smt below_refl is_ub_thelub po_class.chain_def sbChain_dom_eq2)
       moreover
       have case2: "chain Y \<longrightarrow> (sbDom\<cdot>(\<Squnion>i. Y i) = spfCompI f1 f2) \<longrightarrow>
        (sbDom\<cdot>(\<Squnion>i. Y i) = spfCompI f1 f2)\<leadsto>(\<Squnion>i. iter_spfcompOldH2 f1 f2 i (\<Squnion>i. Y i))  \<bar> spfCompOc f1 f2 \<sqsubseteq>
        (\<Squnion>i. (sbDom\<cdot>(Y i) = spfCompI f1 f2)\<leadsto>(\<Squnion>ia. iter_spfcompOldH2 f1 f2 ia (Y i))  \<bar> spfCompOc f1 f2)"
         using chain_if_lub_iter_spfcompOldH2_domI by blast
         thus ?thesis 
           using case1 case2 by blast
  qed

(* Show that spfComp is cont in x independent from the function it's applied to *)
(* I cannot believe I finally proved this :) *)
lemma spf_comp_cont[simp]:
  "cont (\<lambda> x. (sbDom\<cdot>x = spfCompI f1 f2) \<leadsto> (\<Squnion>i.(iter_spfcompOldH2 f1 f2 i) x) \<bar> spfCompOc f1 f2)"
  apply (rule contI2)
  apply (simp)
    using chain_if_lub_iter_spfcompOldH2 by blast

lemma iter_spfcompOldH2_ran[simp]: assumes "sbDom\<cdot>b = spfCompI f1 f2"
  shows  "sbDom\<cdot>(\<Squnion>i. iter_spfcompOldH2 f1 f2 i b) = spfCompC f1 f2"
  by (metis (mono_tags, lifting) assms sbdom_lub_eq2I spfCompH2_itDom spfComp_serialnf_chain)
 
lemma spf_comp_well[simp]: 
  "spf_well (\<Lambda> x. (sbDom\<cdot>x = spfCompI f1 f2) \<leadsto> (\<Squnion>i.(iter_spfcompOldH2 f1 f2 i) x) \<bar> spfCompOc f1 f2)"
  apply (simp add: spf_well_def)
  apply (simp only: domIff2)
  apply (simp add: sbdom_rep_eq)
      by (auto)  

                                
(* used abbreviations are equal to comp function *)
   (* together with the lemma  spfcompOld_tospfH2, the complete equality with spfcompOld is proven *)
lemma spfcompOld_abbrv_tospfH2: "(\<lambda> x. (sbDom\<cdot>x = spfCompI f1 f2) 
                                \<leadsto> (\<Squnion>i.(iter_spfcompOldH2 f1 f2 i) x) \<bar> spfCompOc f1 f2)
                       = (\<lambda> x. (sbDom\<cdot>x = spfCompI f1 f2) 
                          \<leadsto> (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2))) \<bar> spfCompOc f1 f2)"      
  by simp
    
lemma spfcompOld_abbrv_tospfH22: "(spfcompOld f1 f2)
                       = Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfCompI f1 f2) 
                          \<leadsto> (\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2))) \<bar> spfCompOc f1 f2)"      
  by (simp add: spfcompOld_tospfH2)
  
   
(* ----------------------------------------------------------------------- *)
section \<open>spfcompOldOld2\<close>
(* ----------------------------------------------------------------------- *) 
  (* WARNING: This composition type is deprecated an may be replaced by an 
     equal sbfix based definition soon *)
subsection \<open>spfcompOld1 spfcompOldOld2 eq\<close>
 
lemma iter_spfCompH_px_chain[simp]: assumes "sbDom\<cdot>x = spfCompI f1 f2"
  shows "chain (\<lambda> i. x \<uplus> iter_spfCompH f1 f2 i x)"
  by (simp add: assms)
    
lemma lub_iter_spfCompH_eq: assumes "sbDom\<cdot>x = spfCompI f1 f2"
  shows "((\<Squnion>i. ( x \<uplus> iter_spfCompH f1 f2 i x))\<bar> spfCompOc f1 f2) = (\<Squnion>i. (iter_spfCompH f1 f2 i) x)"
proof -
  have f1: "(\<Squnion>i. ( x \<uplus> iter_spfCompH f1 f2 i x)) = x \<uplus> (\<Squnion>i. iter_spfCompH f1 f2 i x)"
    by (simp add: assms contlub_cfun_arg)
  thus ?thesis
    by (simp add: assms lub_iter_spfCompH_dom spfCompOc_def)
qed
   
lemma lub_iter_spfCompH2_spfCompHwX_eq_req_1: assumes "sbDom\<cdot>x = spfCompI f1 f2" 
  shows "(iter_spfcompOldH2 f1 f2 i x) \<sqsubseteq> (x \<uplus> (iter_spfCompH f1 f2 i x))"
proof (induction i)
  case 0
  thus ?case
    by (simp add: spfCompC_def spfCompI_def assms sup.assoc)
next
  case (Suc i)
  thus ?case     
    apply (unfold iterate_Suc)
    apply (subst spfCompHelp2_def, subst spfCompH_def)
    apply (auto)
    apply (subst sbunion_assoc2, rule sbunion_pref_eq2) (* remove x *)
    apply (rule sbunion_pref_eq) (* split up sbunion *)
     apply (rule spf_pref_eq, rule sbres_pref_eq, simp)
     by (rule spf_pref_eq, rule sbres_pref_eq, simp)    
qed

lemma lub_iter_spfCompH2_spfCompHwX_eq_req_2: assumes "sbDom\<cdot>x = spfCompI f1 f2"  
  shows "(x \<uplus> iter_spfCompH f1 f2 i x) \<sqsubseteq> (iter_spfcompOldH2 f1 f2 (Suc i) x)"
proof (induction i)
  case 0
  thus ?case
    apply (simp add: spfCompHelp2_def)
    apply (subst sbunion_assoc2, subst sbunion_pref_eq2)
    apply (simp_all add: assms)
    by (metis (no_types, lifting) spfCompC_def sbleast_least sbleast_sbdom sbunionDom 
               spfRanRestrict sup.bounded_iff sup.cobounded1)   
next
  case (Suc i)
  thus ?case
    apply (unfold iterate_Suc)
    apply (subst spfCompHelp2_def, subst spfCompH_def)
    apply (auto)
    apply (subst sbunion_assoc2, rule sbunion_pref_eq2)
    apply (rule sbunion_pref_eq)
     apply (rule spf_pref_eq, rule sbres_pref_eq, simp)
     by (rule spf_pref_eq, rule sbres_pref_eq, simp)
qed

  
lemma lub_iter_spfCompH2_spfCompHwX_eq: assumes "sbDom\<cdot>x = spfCompI f1 f2" 
  shows "(\<Squnion>i. (iter_spfcompOldH2 f1 f2 i x)) = (\<Squnion>i. ( x \<uplus> iter_spfCompH f1 f2 i x))"
  by (meson assms lub_interl_chain_eq lub_iter_spfCompH2_spfCompHwX_eq_req_1 
      lub_iter_spfCompH2_spfCompHwX_eq_req_2)

lemma lub_iter_spfCompH2_spfCompH_eq: assumes "sbDom\<cdot>x = spfCompI f1 f2" 
  shows "(\<Squnion>i. (iter_spfCompH f1 f2 i) x)  = (\<Squnion>i. (iter_spfcompOldH2 f1 f2 i x))  \<bar> spfCompOc f1 f2"
  using assms lub_iter_spfCompH2_spfCompHwX_eq lub_iter_spfCompH_eq by fastforce
    
    
(* both definitions of spfcompOld are equal independent from the input *)
lemma spfcompOld_and_spfcompOldOld2_eq_req: "(sbDom\<cdot>x = spfCompI f1 f2) \<leadsto> (\<Squnion>i. (iter_spfCompH f1 f2 i) x) 
                            =(sbDom\<cdot>x = spfCompI f1 f2) \<leadsto> ((\<Squnion>i. (iter_spfcompOldH2 f1 f2 i x))  \<bar> spfCompOc f1 f2)"
proof (cases "sbDom\<cdot>x = spfCompI f1 f2")
  case True
  thus ?thesis
    by (simp add: lub_iter_spfCompH2_spfCompH_eq)
next
  case False
  thus ?thesis
    by simp
qed
  
subsection \<open>cont\<close>
(* show that new definition is cont and spf_well based on the proof for the old one *)
lemma spf_compH3_cont[simp]: 
  shows "cont (\<lambda> x. (sbDom\<cdot>x = spfCompI f1 f2) \<leadsto> (\<Squnion>i. (iter_spfCompH f1 f2 i) x))"
  apply (subst spfcompOld_and_spfcompOldOld2_eq_req)
  by simp
    
lemma spf_compH3_well[simp]: 
  shows "spf_well (\<Lambda> x. (sbDom\<cdot>x = spfCompI f1 f2) \<leadsto> (\<Squnion>i. (iter_spfCompH f1 f2 i) x))"
  apply (subst spfcompOld_and_spfcompOldOld2_eq_req)
  by simp

subsection \<open>equalities\<close>
(* used abbreviations are equal to spfcompOldOld2 function *)   
    (* Substitute with this lemma if you need cont properties for spfcompOld *)
lemma spfcompOldH3_abbrv_tospfH32: "(spfcompOldOld2 f1 f2)
                       = Abs_CSPF (\<lambda> x. (sbDom\<cdot>x = spfCompI f1 f2) 
                          \<leadsto>  (\<Squnion>i. iterate i\<cdot>(spfCompH f1 f2 x)\<cdot>((spfRan\<cdot>f1 \<union> spfRan\<cdot>f2)^\<bottom>)))" 
  apply (simp add: spfcompOldOld2_def)
  apply (subst spfCompH_def)
    by simp
    
(* both definitions deliver an equal result *)
lemma spfcompOld_and_spfcompOldOld2_eq: "(spfcompOld f1 f2) = (spfcompOldOld2 f1 f2)"
  apply (subst spfcompOld_abbrv_tospfH22)
  apply (subst spfcompOldH3_abbrv_tospfH32)
  by (simp add: spfcompOld_and_spfcompOldOld2_eq_req)
 
    
    
    
    
chapter \<open>general feed\<close>   
  (* add feedback lemmata here when final definition is decided *)
    
    
chapter \<open>special serial and parallel operators\<close>

lemma spfComp_dom_I: assumes "spfComp_well f1 f2" shows "spfDom\<cdot>(spfcompOld f1 f2) = spfCompI f1 f2"
apply(simp add: spfcompOld_tospfH2, subst spfDomAbs)
by(simp_all add: assms) 

lemma spfDomHelp: assumes "spfDom\<cdot>f1 \<subseteq> sbDom\<cdot>sb" shows "sbDom\<cdot>f1\<rightleftharpoons>sb\<bar>spfDom\<cdot>f1 = spfRan\<cdot>f1"
by (simp add: assms)

lemma sbDomH2: assumes "spfDom\<cdot>f1 \<union> spfDom\<cdot>f2 \<subseteq> sbDom\<cdot>sb2" shows "sbDom\<cdot>((spfCompHelp2 f1 f2 sb1)\<cdot>sb2) = sbDom\<cdot>sb1 \<union> spfRan\<cdot>f1 \<union> spfRan\<cdot>f2"
apply(simp add: spfCompHelp2_def)
apply(subst spfDomHelp)
using assms apply auto[1]
apply(subst spfDomHelp)
using assms apply auto[1]
by simp

lemma spfComp_ran_Oc: assumes "spfComp_well f1 f2" shows "spfRan\<cdot>(spfcompOld f1 f2) = spfCompOc f1 f2"
  apply(simp add: spfcompOld_tospfH2)
  apply(simp add:  spfran_least)
  by(subst spfDomAbs, simp_all add: assms inf.absorb2)  

lemma contSPFRestrict: assumes "cont (Rep_CSPF f)" and "spfDom\<cdot>f = cs" shows "cont (\<lambda> z. (f\<rightleftharpoons>(z\<bar>cs)))"
by (metis  cont_Rep_cfun2 cont_compose op_the_cont)    
    
section \<open>parallel\<close>
  
lemma LtopL: "spfCompL f1 f2 = {} \<Longrightarrow> pspfCompL f1 f2 = {}"
  using spfpl_sub_L by blast

lemma unionRestrictCh: assumes "sbDom\<cdot>sb1 \<inter> cs = {}"
                           and "sbDom\<cdot>sb2 \<union> sbDom\<cdot>sb3 = cs"
                           and "c \<in> cs"
   shows "(sb1 \<uplus> sb2 \<uplus> sb3 \<bar> cs) . c = (sb2 \<uplus> sb3) . c"
by (metis (no_types, lifting) Un_upper2 assms(1) assms(2) inf_sup_distrib1 inf_sup_ord(3) sbrestrict_id sbunion_commutative sbunion_restrict2 sbunion_restrict3 sup_eq_bot_iff)

lemma unionRestrict: assumes "sbDom\<cdot>sb1 \<inter> cs = {}"
                         and "sbDom\<cdot>sb2 \<union> sbDom\<cdot>sb3 = cs"
   shows "sb1 \<uplus> sb2 \<uplus> sb3 \<bar> cs = sb2 \<uplus> sb3"
  by (metis assms(2) sbunionDom sbunion_associative sbunion_restrict)

lemma parCompHelp2Eq: assumes "parcomp_well f1 f2"
                          and "sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2"    
   shows "(\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2)))\<bar>spfCompOc f1 f2 = (f1\<rightleftharpoons>(x\<bar>spfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x\<bar>spfDom\<cdot>f2))" 
apply(subst spfComp_parallel_itconst2, simp_all add: assms spfComp_well_def)
apply(simp add: spfCompOc_def)
apply(subst unionRestrict)
apply(simp_all add: assms)
by (metis spfCompL_def assms(1))

lemma parCompHelp2Eq2: assumes "parcomp_well f1 f2" 
   shows " (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2) \<leadsto> ((\<Squnion>i. iterate i\<cdot>(spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2)))\<bar>spfCompOc f1 f2)
         = (sbDom\<cdot>x = spfDom\<cdot>f1 \<union> spfDom\<cdot>f2) \<leadsto> ((f1\<rightleftharpoons>(x\<bar>spfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x\<bar>spfDom\<cdot>f2)))"
using assms(1) parCompHelp2Eq by fastforce

lemma parallelOperatorEq: assumes "parcomp_well f1 f2"  
   shows "(f1 \<otimes> f2) = (f1 \<parallel> f2)"
apply(simp add: parcomp_def spfcompOld_tospfH2)
apply(subst spfComp_I_domf1f2_eq, simp_all add: assms)
apply(subst parCompHelp2Eq2)
by(simp_all add: assms)

lemma parCompDom: assumes "parcomp_well f1 f2" shows "spfDom\<cdot>(f1 \<parallel> f2) = spfDom\<cdot>(spfcompOld f1 f2)"
  by (simp add: assms(1) parallelOperatorEq)

lemma parCompRan: assumes "parcomp_well f1 f2" shows "spfRan\<cdot>(f1 \<parallel> f2) = spfRan\<cdot>(spfcompOld f1 f2)"
  by (simp add: assms(1) parallelOperatorEq)

section \<open>serial\<close>
  
lemma pLEmptyNoSelfloops: assumes "pspfCompL f1 f2 = {}"
  shows "no_selfloops f1 f2"
  apply(simp add: no_selfloops_def)
  using assms pL_def by auto
    
lemma spfComp_I_domf1_eq2: assumes "sercomp_well f1 f2"
  shows "spfCompI f1 f2 = spfDom\<cdot>f1"
proof -
  have "spfDom\<cdot>f2 - (spfRan\<cdot>f1 \<union> spfRan\<cdot>f2) = spfDom\<cdot>f1 \<inter> (spfDom\<cdot>f2 \<union> spfRan\<cdot>f2)"
    by (metis (no_types) Diff_eq_empty_iff assms bot_eq_sup_iff inf_sup_distrib1 inf_sup_ord(3) pL_def)
  thus ?thesis
    by (simp add: spfCompI_def Un_Diff Un_Diff_Int assms)
qed

lemma serCompHelp2Eq: assumes "pL f1 f2 = {}"
                          and "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                          and "spfComp_well f1 f2"
                          and "sbDom\<cdot>x = spfDom\<cdot>f1" 
   shows "(\<Squnion>i. iterate i\<cdot>(SPF.spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (C f1 f2)))\<bar>Oc f1 f2 = ((f1 \<rightleftharpoons> x)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))" 
   apply(subst spfComp_serial_itconst2)
   apply(simp_all add: assms)
    apply(subst spfComp_I_domf1_eq2, simp_all add: assms)
   apply(simp add: Oc_def)
   apply(subst unionRestrict, simp_all add: assms)
   using pL_def assms(1) assms(2) apply blast
   by (metis (no_types, lifting) assms(2) assms(4) domIff option.collapse sbleast_sbdom spfLeastIDom spf_sbdom2dom spfran2sbdom)

lemma serCompHelp2Eq2: assumes "pspfCompL f1 f2 = {}"
                           and "spfComp_well f1 f2"
                           and "spfRan\<cdot>f1 = spfDom\<cdot>f2"
   shows " (sbDom\<cdot>x = spfDom\<cdot>f1) \<leadsto> ((\<Squnion>i. iterate i\<cdot>(SPF.spfCompHelp2 f1 f2 x)\<cdot>(sbLeast (spfCompC f1 f2)))\<bar>spfCompOc f1 f2)
         = (sbDom\<cdot>x = spfDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> x) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
  by (metis (mono_tags, lifting) assms(1) assms(2) assms(3) lub_eq serCompHelp2Eq)

lemma serialOperatorEq: assumes "pspfCompL f1 f2 = {}"
                            and "spfComp_well f1 f2"
                            and "spfRan\<cdot>f1 = spfDom\<cdot>f2"
                            and "sbDom\<cdot>sb = spfDom\<cdot>f1"
   shows "((f1 \<otimes> f2) \<h> spfRan\<cdot>f1) \<rightleftharpoons> sb = (f1 \<circ> f2) \<rightleftharpoons> sb"
proof - 
  have "sbDom\<cdot>(((f1 \<otimes> f2) \<h> spfRan\<cdot>f1) \<rightleftharpoons> sb) = spfRan\<cdot>f2"
    sorry
  show ?thesis 
    apply(subst sb_eq, simp_all)
    sorry
qed
  (*  
  apply(simp add: sercomp_def spfcomp_tospfH2)
  apply(subst spfComp_I_domf1_eq2, simp_all add: assms)
  apply(subst serCompHelp2Eq2)
  apply(simp_all add: assms)
  apply()
  sorry*)

    
    
end
  