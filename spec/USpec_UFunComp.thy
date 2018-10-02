theory USpec_UFunComp
  imports USpec inc.CPOFix fun.UFun_Comp
begin

(****************************************************)
section\<open>Definitions\<close>
(****************************************************)   
  

(* from here on only lemma on composition *)
default_sort ubcl_comp

(* General Composition  *)
definition uspec_compwell :: "('m,'m) ufun uspec \<Rightarrow> ('m,'m) ufun uspec \<Rightarrow> bool" where
"uspec_compwell S1 S2 \<equiv> \<forall> f1 \<in> (Rep_rev_uspec S1). \<forall> f2 \<in> (Rep_rev_uspec S2). comp_well f1 f2"

abbreviation uspecCompDom:: "('m,'m) ufun uspec \<Rightarrow> ('m,'m) ufun uspec \<Rightarrow> channel set" where
"uspecCompDom S1 S2 \<equiv> (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2) - (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2)"

abbreviation uspecRanUnion:: "('m,'n) ufun uspec \<Rightarrow> ('m,'n) ufun uspec \<Rightarrow> channel set" where
"uspecRanUnion S1 S2 \<equiv> uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2"

abbreviation uspecDomUnion:: "('m,'n) ufun uspec \<Rightarrow> ('m,'n) ufun uspec \<Rightarrow> channel set" where
"uspecDomUnion S1 S2 \<equiv> uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2"

definition uspecComp :: "('m,'m) ufun uspec \<Rightarrow> ('m,'m) ufun uspec \<Rightarrow> ('m,'m) ufun uspec" (infixl "\<Otimes>" 50) where
"uspecComp S1 S2 \<equiv> 
let Comp_set = {ufComp f1 f2 | f1 f2. f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)};
    Cin = (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2) - (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2);
    Cout = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2
in Abs_rev_uspec Comp_set Cin Cout"

(* Parallel Composition *)
definition uspec_parcompwell :: "('m,'n) ufun uspec \<Rightarrow> ('m,'n) ufun uspec \<Rightarrow> bool" where
"uspec_parcompwell S1 S2 \<equiv> \<forall> f1 \<in> (Rep_rev_uspec S1). \<forall> f2 \<in> (Rep_rev_uspec S2). parcomp_well f1 f2"  

definition uspecParComp :: "('m,'n) ufun uspec \<Rightarrow> ('m,'n) ufun uspec \<Rightarrow> ('m,'n) ufun uspec" (infixl "\<parallel>" 50) where
"uspecParComp S1 S2 \<equiv>
let Comp_set = {ufParComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)};
    Cin = (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2);
    Cout = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2
in Abs_rev_uspec Comp_set Cin Cout"

(* Serial Composition *)
definition uspec_sercompwell :: "('in,'m) ufun uspec \<Rightarrow> ('m,'out) ufun uspec \<Rightarrow> bool" where
"uspec_sercompwell S1 S2 \<equiv> \<forall> f1 \<in> (Rep_rev_uspec S1). \<forall> f2 \<in> (Rep_rev_uspec S2). sercomp_well f1 f2"

definition uspecSerComp :: "('in,'m) ufun uspec \<Rightarrow> ('m,'out) ufun uspec \<Rightarrow> ('in,'out) ufun uspec" (infixl "\<circle>" 50) where
"uspecSerComp S1 S2 \<equiv>
let Comp_set = {ufSerComp f1 f2 | f1 f2.  f1\<in>(Rep_rev_uspec S1) \<and> f2\<in>(Rep_rev_uspec S2)};
    Cin = uspecDom\<cdot>S1;
    Cout = uspecRan\<cdot>S2
in Abs_rev_uspec Comp_set Cin Cout"

(* Feedback Composition *)
definition uspecFeedbackComp :: "('m,'m) ufun uspec \<Rightarrow> ('m,'m) ufun uspec" where
"uspecFeedbackComp S1 \<equiv> 
let Comp_set = {ufFeedbackComp f1 | f1.  f1\<in>(Rep_rev_uspec S1)};
    Cin = uspecDom\<cdot>S1 - uspecRan\<cdot>S1;
    Cout = uspecRan\<cdot>S1
in Abs_rev_uspec Comp_set Cin Cout"


subsection \<open>UspecComp\<close>

(*   *)
lemma uspec_compwell_commu: "uspec_compwell S1 S2 =  uspec_compwell S2 S1"
  using  uspec_compwell_def comp_well_def by blast

lemma uspec_compwell2ufunclcompwell: assumes "uspec_compwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. comp_well f1 f2"
  using assms uspec_compwell_def by blast

lemma uspec_comp_well[simp]: assumes "uspec_compwell S1 S2"
  shows "uspecWell (Rev {ufComp f1 f2 |(f1::('m,'m) ufun) (f2::('m,'m) ufun). f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2})
              (Discr (uspecCompDom S1 S2)) (Discr (uspecRanUnion S1 S2))"
  apply (rule uspec_wellI) 
  using assms ufclDom_ufun_def ufclRan_ufun_def ufcomp_dom
   apply (smt CollectD comp_well_def rep_rev_revset ufCompI_def uspec_allDom uspec_allRan uspec_compwell2ufunclcompwell)
  using assms ufclDom_ufun_def ufclRan_ufun_def ufcomp_ran
  by (smt CollectD comp_well_def rep_rev_revset ufCompO_def uspec_allRan uspec_compwell2ufunclcompwell)

(*   *)
lemma uspec_comp_commu: assumes "uspec_compwell S1 S2"
  shows "(S1 \<Otimes> S2) = (S2 \<Otimes> S1)"          
proof - 
  have "{ufComp f1 f2 |(f1::('a,'a) ufun) (f2::('a,'a) ufun). f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} = 
             {ufComp f1 f2 |(f1::('a,'a) ufun) (f2::('a,'a) ufun). f1 \<in> Rep_rev_uspec S2 \<and> f2 \<in> Rep_rev_uspec S1}" (is "?L = ?R")
    apply auto
    apply (meson comp_well_def ufcomp_commu assms uspec_compwell_def)
    by (metis assms comp_well_def ufcomp_commu uspec_compwell2ufunclcompwell)
  then show ?thesis
    unfolding uspecComp_def apply simp
    apply (rule uspec_eqI)
    by (simp add: sup_commute) +
qed


lemma uspec_comp_rep[simp]: assumes "uspec_compwell S1 S2"
shows "{f1 \<otimes> f2 |(f1::('a,'a) ufun) (f2::('a,'a) ufun). f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} 
          = Rep_rev_uspec (S1 \<Otimes> S2)"
  apply (simp add: uspecComp_def)
  using assms(1) rep_abs_rev_simp uspec_comp_well by blast

lemma uspec_comp_ele_ex: assumes "uspec_compwell S1 S2"
and "uspecIsConsistent (S1 \<Otimes> S2)"
shows "\<forall> f \<in> Rep_rev_uspec (S1 \<Otimes> S2). \<exists> f1 \<in> Rep_rev_uspec S1. \<exists> f2 \<in> Rep_rev_uspec S2. f = (f1 \<otimes> f2)"
  using assms uspec_comp_rep by fastforce

lemma uspec_comp_not_empty:  assumes "uspec_compwell S1 S2"
"f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
shows "(f1 \<otimes> f2) \<in> Rep_rev_uspec (S1 \<Otimes> S2)"
  by (metis (mono_tags, lifting) assms(1) assms(2) f2_def mem_Collect_eq rep_abs_rev_simp uspecComp_def uspec_comp_well)

lemma uspec_comp_consistent2: assumes "uspecIsConsistent (S1 \<Otimes> S2)"
  shows "uspecIsConsistent S1 \<and> uspecIsConsistent S2"
  by (metis assms emptyE not_uspec_consisten_empty_eq uspec_comp_ele_ex uspec_compwell_def uspec_consist_f_ex)

lemma uspec_comp_dom: assumes "uspec_compwell S1 S2"
shows "uspecDom\<cdot>(S1 \<Otimes> S2) = (uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2) - (uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2)" (*UFun_Comp \<rightarrow> dom*)
  apply (simp add: uspecComp_def)
  apply (subst uspecdom_insert)
  apply (simp only: uspec_comp_well assms rep_abs_uspec)
  by simp


subsection \<open>UspecParComp\<close>


(*   *)
lemma uspec_parcompwell_commu: "uspec_parcompwell S1 S2 = uspec_parcompwell S2 S1"
  using uspec_parcompwell_def
  by (metis inf_commute ufcomp_L_commu)

(*   *)
lemma uspec_parcompwell2ufunclparcompwell: assumes "uspec_parcompwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. parcomp_well f1 f2"
  using assms uspec_parcompwell_def 
  by blast

(*   *)
lemma uspec_parcomp_well[simp]: assumes "uspec_parcompwell S1 S2"
  shows "uspecWell (Rev {ufParComp f1 f2 |(f1::('a,'b) ufun) (f2::('a,'b) ufun). f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2})
              (Discr (uspecDomUnion S1 S2)) (Discr (uspecRanUnion S1 S2))"
  apply (rule uspec_wellI) 
  using ufclDom_ufun_def
  apply (smt Abs_cfun_inverse2 CollectD assms ufParComp_dom uspecRevSet_def uspec_allDom uspec_parcompwell2ufunclparcompwell uspecrevset_cont)
  using ufclDom_ufun_def
  by (smt Abs_cfun_inverse2 CollectD assms ufParComp_ran ufclRan_ufun_def uspecRevSet_def uspec_allRan uspec_parcompwell2ufunclparcompwell uspecrevset_cont)

(*   *)
lemma uspec_parcomp_rep[simp]: assumes "uspec_parcompwell S1 S2"
shows "{ufParComp f1 f2 |(f1::('a,'b) ufun) (f2::('a,'b) ufun). f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} 
          = Rep_rev_uspec ((S1 :: ('a,'b) ufun uspec) \<parallel> S2)"
  apply (simp add: uspecParComp_def)
  using assms(1) rep_abs_rev_simp uspec_parcomp_well by blast

(*   *)
lemma uspec_parcomp_not_empty:  assumes "uspec_parcompwell S1 S2"
"f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
shows "(ufParComp f1 f2) \<in> Rep_rev_uspec (S1 \<parallel> S2)"
  using assms(1) assms(2) f2_def uspec_parcomp_rep by fastforce  

(*   *)
lemma uspec_parcomp_consistent: assumes "uspec_parcompwell S1 S2"
  and "uspecIsConsistent S1" and "uspecIsConsistent S2"
shows "uspecIsConsistent (S1 \<parallel> S2)"
  by (metis assms(1) assms(2) assms(3) emptyE some_in_eq uspecIsConsistent_def uspec_parcomp_not_empty)

(*   *)
lemma uspec_parcomp_consistent2: assumes "uspec_parcompwell S1 S2" and "uspecIsConsistent (S1 \<parallel> S2)"
  shows "uspecIsConsistent S1 \<and> uspecIsConsistent S2"
proof (rule)
  have f1: "{ufParComp a aa |a aa. a \<in> Rep_rev_uspec S1 \<and> aa \<in> Rep_rev_uspec S2} \<noteq> {}"
    using assms(1) assms(2) uspecIsConsistent_def
    by auto      
  then have "Rep_rev_uspec S1 \<noteq> {}"
    by blast
  then show "uspecIsConsistent S1"
    by (meson uspecIsConsistent_def)
  have "Rep_rev_uspec S2 \<noteq> {}"
    using f1 by blast
  then show "uspecIsConsistent S2"
    by (meson uspecIsConsistent_def)
qed

(*   *)
lemma uspec_parcomp_dom: assumes "uspec_parcompwell S1 S2"
  shows "uspecDom\<cdot>(S1 \<parallel> S2) = uspecDom\<cdot>S1 \<union> uspecDom\<cdot>S2"
  apply (simp add: uspecParComp_def)
  apply (subst uspecdom_insert)
  apply (simp only: uspec_parcomp_well assms rep_abs_uspec)
  by simp

(*   *)
lemma uspec_parcomp_ran: assumes "uspec_parcompwell S1 S2"
  shows "uspecRan\<cdot>(S1 \<parallel> S2) = uspecRan\<cdot>S1 \<union> uspecRan\<cdot>S2"
  apply (simp add: uspecParComp_def)
  apply (subst uspecran_insert)
  apply (simp only: uspec_parcomp_well assms rep_abs_uspec)
  by simp

lemma uspec_parcomp_h1: assumes "uspec_parcompwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. (ufParComp f1 f2) \<in> Rep_rev_uspec (S1 \<parallel> S2)"
  by (simp add: assms uspec_parcomp_not_empty)   

lemma uspec_parcomp_h2: assumes "uspec_parcompwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. parcomp_well f1 f2"
  using assms uspec_parcompwell_def
  by blast

(* if the composition of 2 uspecs is consistent then those uspecs are consistent themselves  *)
lemma uspec_parcomp_ele_ex: assumes "uspec_parcompwell S1 S2"
shows "\<forall> f \<in> Rep_rev_uspec (S1 \<parallel> S2). \<exists> f1 \<in> Rep_rev_uspec S1. \<exists> f2 \<in> Rep_rev_uspec S2. f = (ufParComp f1 f2)"
  using assms(1) uspec_parcomp_rep by fastforce

(* uspec parcomp is commutative  *)
lemma uspec_parcomp_commu: assumes "uspec_parcompwell S1 S2"
  shows "(uspecParComp S1 S2) = (uspecParComp S2 S1)"
proof -
  have f1: "{f1 \<parallel> f2 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} = 
                {f1 \<parallel> f2 |f1 f2. f1 \<in> Rep_rev_uspec S2 \<and> f2 \<in> Rep_rev_uspec S1}" (is "?L = ?R")
    apply auto
     apply (meson assms uspec_parcompwell_def ufParComp_commutativity)
    using assms uspec_parcompwell_def ufParComp_commutativity by metis
  show ?thesis
    apply (rule uspec_eqI)
      apply (simp add: uspecParComp_def)
      apply (simp add: f1 sup_commute) 
     apply (simp add: assms sup_commute uspec_parcomp_dom uspec_parcompwell_commu) 
    by (simp add: assms sup_commute uspec_parcomp_ran uspec_parcompwell_commu)
qed

(* uspec parcomp is associative  *)
lemma uspec_parcomp_asso: assumes "uspec_parcompwell S1 S2"
and "uspec_parcompwell S1 S3"
and "uspec_parcompwell S2 S3"
shows "uspecParComp (uspecParComp S1 S2) S3 = uspecParComp S1 (uspecParComp S2 S3)"
proof -
  have f0: "uspec_parcompwell (S1 \<parallel> S2) S3"
    apply (simp add: uspec_parcompwell_def, auto)
    using assms(1) assms(2) assms(3) uspec_parcomp_ele_ex uspec_parcompwell2ufunclparcompwell uspec_parcompwell_def
     apply (smt empty_iff ufParCompWell_associativity uspec_parcompwell_commu)
    by (smt assms(1) assms(2) assms(3) disjoint_iff_not_equal ufParCompWell_associativity uspec_parcomp_ele_ex uspec_parcompwell2ufunclparcompwell uspec_parcompwell_commu)
  have f1: "uspec_parcompwell S1 (S2 \<parallel> S3)"
    apply (simp add: uspec_parcompwell_def, auto)
    using  assms(1) assms(2) assms(3) uspec_parcomp_ele_ex uspec_parcompwell2ufunclparcompwell
     apply (smt empty_iff ufParCompWell_associativity) 
    by (smt Un_iff assms(1) assms(2) assms(3) disjoint_iff_not_equal ufParComp_ran uspec_parcomp_ele_ex uspec_parcompwell2ufunclparcompwell)
  have f2: "uspecRevSet\<cdot>((S1 \<parallel> S2) \<parallel> S3) = 
      Rev {f1 \<parallel> f2 |f1 f2. f1 \<in> Rep_rev_uspec (S1 \<parallel> S2) \<and> f2 \<in> Rep_rev_uspec S3}"
    apply (simp add: uspecrevset_insert)
    apply (subst uspec_parcomp_rep)
    using assms(1) assms(2) assms(3) uspec_parcomp_ele_ex uspec_parcompwell2ufunclparcompwell uspec_parcompwell_def 
    using f0 apply blast
    by (simp add: rev_inv_rev)
  have f3: "uspecRevSet\<cdot>(S1 \<parallel> (S2 \<parallel> S3)) = 
      Rev {f1 \<parallel> f2 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec (S2 \<parallel> S3)}"
    apply (simp add: uspecrevset_insert)
    by (simp add: f1)
  have f10: "{f1 \<parallel> f2 |f1 f2. f1 \<in> Rep_rev_uspec (S1 \<parallel> S2) \<and> f2 \<in> Rep_rev_uspec S3} =
               {f1 \<parallel> f2 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec (S2 \<parallel> S3)}"
  proof(auto)
    show "\<And>(f1::'a\<Rrightarrow> 'b) f2::'a\<Rrightarrow> 'b.
       f1 \<in> Rep_rev_uspec (S1 \<parallel> S2) \<Longrightarrow>
       f2 \<in> Rep_rev_uspec S3 \<Longrightarrow> \<exists>(f1a::'a\<Rrightarrow> 'b) f2a::'a\<Rrightarrow> 'b. (f1 \<parallel> f2) = (f1a \<parallel> f2a) \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec (S2 \<parallel> S3)"
      sorry
  next
    show "\<And>(f1::'a\<Rrightarrow> 'b) f2::'a\<Rrightarrow> 'b.
       f1 \<in> Rep_rev_uspec S1 \<Longrightarrow>
       f2 \<in> Rep_rev_uspec (S2 \<parallel> S3) \<Longrightarrow>
       \<exists>(f1a::'a\<Rrightarrow> 'b) f2a::'a\<Rrightarrow> 'b. (f1 \<parallel> f2) = (f1a \<parallel> f2a) \<and> f1a \<in> Rep_rev_uspec (S1 \<parallel> S2) \<and> f2a \<in> Rep_rev_uspec S3"
      sorry
  qed
(*proof (auto)
    show "\<And>f1 f2. f1 \<in> Rep_rev_uspec (S1 \<parallel> S2) \<Longrightarrow> f2 \<in> Rep_rev_uspec S3 \<Longrightarrow> \<exists>f1a f2a. f1 \<parallel> f2 = (ufParComp f1a f2a) \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec (S2 \<parallel> S3)"
    proof -
      fix f1::"('a,'b) ufun" and f2::"('a,'b) ufun"
      assume f1_def: "f1 \<in> Rep_rev_uspec (S1 \<parallel> S2)" and f2_def: "f2 \<in> Rep_rev_uspec S3"
      obtain f3 f4 where f3_def: "f3 \<in> Rep_rev_uspec S1" and f4_def: "f4 \<in> Rep_rev_uspec S2" and f1_eq_f3_f4: "f1 = (f3 \<parallel> f4)"
        by (metis assms(1) empty_iff f1_def uspecIsConsistent_def uspec_parcomp_ele_ex)
      then show "\<exists>f1a f2a. (ufParComp f1 f2) = (ufParComp f1a f2a) \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec (S2 \<parallel> S3)"
        using assms(1) assms(2) assms(3) f2_def uspec_parcomp_not_empty uspec_parcompwell_def sorry
    qed
  next
    show "\<And>(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<Longrightarrow> f2 \<in> Rep_rev_uspec (S2 \<parallel> S3) \<Longrightarrow> 
              \<exists>(f1a::'a) f2a::'a. f1 \<parallel> f2 = f1a \<parallel> f2a \<and> f1a \<in> Rep_rev_uspec (S1 \<parallel> S2) \<and> f2a \<in> Rep_rev_uspec S3"
    proof -
      fix f1::'a and f2::'a
      assume f1_def: "f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec (S2 \<parallel> S3)"
      obtain f3 f4 where f3_def: "f3 \<in> Rep_rev_uspec S2" and f4_def: "f4 \<in> Rep_rev_uspec S3" and f2_eq_f3_f4: "f2 = f3 \<parallel> f4"
        by (metis assms(3) empty_iff f2_def uspecIsConsistent_def uspec_parcomp_ele_ex)
      then show "\<exists>(f1a::'a) f2a::'a. f1 \<parallel> f2 = f1a \<parallel> f2a \<and> f1a \<in> Rep_rev_uspec (S1 \<parallel> S2) \<and> f2a \<in> Rep_rev_uspec S3"
        by (meson assms(1) assms(2) assms(3) f1_def parcomp_asso uspec_parcomp_not_empty uspec_parcompwell_def)
    qed
  qed
  have f11: "uspecRevSet\<cdot>(S1 \<parallel> S2 \<parallel> S3) = uspecRevSet\<cdot>(S1 \<parallel> (S2 \<parallel> S3))"
    apply (subst f2)
    apply (subst f3)
    by (simp add: f10)
  show ?thesis
    apply (rule uspec_eqI)
      apply (simp add: f11)
     apply (simp add: assms(1) assms(3) f0 f1 sup_assoc uspec_parcomp_dom)
    by (simp add: assms(1) assms(3) f0 f1 sup_assoc uspec_parcomp_ran)
qed*)
  have f11: "uspecRevSet\<cdot>(S1 \<parallel> S2 \<parallel> S3) = uspecRevSet\<cdot>(S1 \<parallel> (S2 \<parallel> S3))"
    apply (subst f2)
    apply (subst f3)
    by (simp add: f10)
  show ?thesis
    apply (rule uspec_eqI)
    apply (simp add: f11)
    apply (simp add: assms(1) assms(3) f0 f1 sup_assoc uspec_parcomp_dom)
    by (simp add: assms(1) assms(3) f0 f1 sup_assoc uspec_parcomp_ran)
qed

(*   *)
lemma uspec_parcompwell_asso_h: assumes "uspec_parcompwell S1 S2" and "uspec_parcompwell S1 S3"
and "uspec_parcompwell S2 S3" shows "uspec_parcompwell S1 (S2 \<parallel> S3)"
  apply (simp add: uspec_parcompwell_def, auto)
  using assms(1) assms(2) assms(3) uspec_parcomp_ele_ex uspec_parcompwell2ufunclparcompwell 
   apply (smt empty_iff ufParCompWell_associativity)
  by (smt Un_iff assms(1) assms(2) assms(3) disjoint_iff_not_equal ufParComp_ran uspec_parcomp_ele_ex uspec_parcompwell2ufunclparcompwell)

(* the new component is uspecwell  *) 
lemma uspec_parcompwell_asso: assumes "uspec_parcompwell S1 S2" and "uspec_parcompwell S1 S3"
and "uspec_parcompwell S2 S3" 
shows "uspecWell  (Rev {f1 \<parallel> f2 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec (S2 \<parallel> S3)})
      (Discr (uspecDomUnion S1 (S2 \<parallel> S3))) (Discr (uspecRanUnion S1 (S2 \<parallel> S3)))"
  using assms(1) assms(2) assms(3) uspec_parcomp_well uspec_parcompwell_asso_h by blast


subsection \<open>UspecSerComp\<close>


(*   *)
lemma uspec_sercomp_well[simp]: assumes "uspec_sercompwell S1 S2"
  shows "uspecWell (Rev {f1 \<circ> f2 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2})
         (Discr (uspecDom\<cdot>S1)) (Discr (uspecRan\<cdot>S2))"
  apply (rule uspec_wellI)
  using ufclDom_ufun_def
  apply (smt CollectD assms ufSerComp_dom uspec_allDom uspec_sercompwell_def uspecrevset_insert)
  using ufclRan_ufun_def 
  by (smt CollectD assms ufSerComp_ran uspec_allRan uspec_sercompwell_def uspecrevset_insert)

lemma uspec_sercompwell2ufunclsercompwell: assumes "uspec_sercompwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. sercomp_well f1 f2"
  using assms uspec_sercompwell_def by blast

(*   *)
lemma uspec_sercomp_rep[simp]: assumes "uspec_sercompwell S1 S2"
shows "{f1 \<circ> f2 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec S2} 
          = Rep_rev_uspec (S1 \<circle> S2)"
  apply (simp add: uspecSerComp_def)
  using assms mem_Collect_eq rep_abs_rev_simp uspecWell.simps uspec_sercomp_well 
  by smt

(*   *)
lemma uspec_sercomp_not_empty:  assumes "uspec_sercompwell S1 S2"
"f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec S2"
shows "(f1 \<circ> f2) \<in> Rep_rev_uspec (S1 \<circle> S2)"
  using assms(1) assms(2) f2_def uspec_sercomp_rep by fastforce

(*   *)
lemma uspec_sercomp_consistent: assumes "uspec_sercompwell S1 S2"
  and "uspecIsConsistent S1" and "uspecIsConsistent S2"
shows "uspecIsConsistent (S1 \<circle> S2)"
  by (metis assms(1) assms(2) assms(3) ex_in_conv uspecIsConsistent_def uspec_sercomp_not_empty)

(*   *)
lemma uspec_sercomp_consistent2: assumes "uspecIsConsistent (S1 \<circle> S2)"
  shows "uspecIsConsistent S1 \<and> uspecIsConsistent S2"
  by (smt Collect_empty_eq assms emptyE uspecIsConsistent_def uspec_sercomp_rep uspec_sercompwell_def)

(*   *)
lemma uspec_sercomp_dom: assumes "uspec_sercompwell S1 S2"
  shows "uspecDom\<cdot>(S1 \<circle> S2) = uspecDom\<cdot>S1"
  apply (simp add: uspecSerComp_def)
  apply (subst uspecdom_insert)
  apply (simp only: uspec_sercomp_well assms rep_abs_uspec)
  by simp

(*   *)
lemma uspec_sercomp_ran: assumes "uspec_sercompwell S1 S2"
  shows "uspecRan\<cdot>(S1 \<circle> S2) = uspecRan\<cdot>S2"
  apply (simp add: uspecSerComp_def)
  apply (subst uspecran_insert)
  apply (simp only: uspec_sercomp_well assms rep_abs_uspec)
  by simp

(* if the composition of 2 uspecs is consistent then those uspecs are consistent themselves  *)
lemma uspec_sercomp_ele_ex: assumes "uspec_sercompwell S1 S2"
and "f \<in> Rep_rev_uspec (S1 \<circle> S2)"
shows "\<exists> f1 \<in> Rep_rev_uspec S1. \<exists> f2 \<in> Rep_rev_uspec S2. f = (f1 \<circ> f2)"
  using assms(1) assms(2) uspec_sercomp_rep by fastforce

lemma uspec_sercomp_h1: assumes "uspec_sercompwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. (f1 \<circ> f2) \<in> Rep_rev_uspec (S1 \<circle> S2)"
  by (simp add: assms uspec_sercomp_not_empty)

lemma uspec_sercomp_h2: assumes "uspec_sercompwell S1 S2"
  shows "\<forall> f1 \<in> Rep_rev_uspec S1. \<forall> f2 \<in> Rep_rev_uspec S2. sercomp_well f1 f2"
  using assms uspec_sercompwell_def by blast

(* sercomp of uspec is associative  *)
lemma uspec_sercomp_asso: assumes "uspec_sercompwell S1 S2" and "uspec_sercompwell S2 S3"
and "uspecDom\<cdot>S1 \<inter> uspecRan\<cdot>S2 = {}" 
and "uspecDom\<cdot>S2 \<inter> uspecRan\<cdot>S3 = {}" 
shows "((S1 \<circle> S2) \<circle> S3) = (S1 \<circle> (S2 \<circle> S3))"
proof -
  have f0: "uspec_sercompwell (S1 \<circle> S2) S3"
  proof (simp add: uspec_sercompwell_def, rule, rule)
    fix f1::"('a,'c) ufun" and f2::"('c,'d) ufun"
    assume a1: "f1 \<in> Rep_rev_uspec (S1 \<circle> S2)"
    assume a2: "f2 \<in> Rep_rev_uspec S3"
    obtain f3 f4 where f3_def: "(f3 ::('a,'b) ufun) \<in> Rep_rev_uspec S1" and f4_def: "(f4 ::('b,'c) ufun) \<in> Rep_rev_uspec S2" 
        and f1_eq_f3_f4: "f1 = (f3 \<circ> f4)"
      by (metis assms(1) empty_iff a1 uspecIsConsistent_def uspec_sercomp_ele_ex)
    have f1: "sercomp_well f3 f4"
      using assms(1) f3_def f4_def uspec_sercompwell2ufunclsercompwell by blast
    have f2: "sercomp_well f4 f2"
      using a2 assms(2) f4_def uspec_sercompwell_def by blast
    have f3: "ufclDom\<cdot>f3 \<inter> ufclRan\<cdot>f4 = {}"
      by (metis assms(3) f3_def f4_def uspec_allDom uspec_allRan uspecrevset_insert)
    have f4: "ufclDom\<cdot>f4 \<inter> ufclRan\<cdot>f2 = {}"
      by (metis a2 assms(4) f4_def uspec_allDom uspec_allRan uspecrevset_insert)
    show "sercomp_well f1 f2"
      apply(simp add: f1 f1_eq_f3_f4 f2 f3 f4 assms uspec_allDom uspec_allRan)
      apply rule
       apply(subst ufSerComp_ran)
      using f1 apply blast
       apply (simp add: f2)
      apply(subst ufSerComp_ran)
      using f1 apply blast
      apply(subst ufSerComp_dom)
      using f1 apply blast
      by (metis f3 ufclDom_ufun_def ufclRan_ufun_def)
  qed
  have f1: "uspec_sercompwell S1 (S2 \<circle> S3)"
  proof (simp add: uspec_sercompwell_def, rule, rule)
    fix f1::"('a,'b) ufun" and f2::"('b,'d) ufun" 
    assume a1: "f1 \<in> Rep_rev_uspec S1"
    assume a2: "f2 \<in> Rep_rev_uspec (S2 \<circle> S3)"
    obtain f3 f4 where f3_def: "(f3 :: ('b,'c) ufun) \<in> Rep_rev_uspec S2" and f4_def: "(f4 :: ('c,'d) ufun) \<in> Rep_rev_uspec S3" 
        and f1_eq_f3_f4: "f2 = ufSerComp f3 f4"
        using assms(2) a2 uspec_sercomp_rep by blast
    have f1: "sercomp_well f3 f4"
      using assms(2) f3_def f4_def uspec_sercompwell_def
      by blast
    have f2: "sercomp_well f1 f3"
      using a1 assms(1) f3_def uspec_sercompwell2ufunclsercompwell by blast
    have f3: "ufclDom\<cdot>f1 \<inter> ufclRan\<cdot>f3 = {}"
      by (metis a1 assms(3) f3_def uspec_allDom uspec_allRan uspecrevset_insert)
    have f4: "ufclDom\<cdot>f3 \<inter> ufclRan\<cdot>f4 = {}"
      by (metis assms(4) f3_def f4_def uspec_allDom uspec_allRan uspecrevset_insert)
    show "sercomp_well f1 f2"
      apply (simp add: f1 f1_eq_f3_f4 f2 f3 f4)
      apply rule
       apply(subst ufSerComp_dom)
      using f1 apply blast
       apply simp
      apply(subst ufSerComp_ran)
      using f1 apply blast
      apply(subst ufSerComp_dom)
      using f1 apply blast
      by (metis f2 f4 ufclDom_ufun_def ufclRan_ufun_def)
  qed
  have f2: "uspecRevSet\<cdot>(S1 \<circle> S2 \<circle> S3) = 
      Rev {f1 \<circ> f2 |f1 f2. f1 \<in> Rep_rev_uspec (S1 \<circle> S2) \<and> f2 \<in> Rep_rev_uspec S3}"
    apply (simp add: uspecrevset_insert)
    apply (subst uspec_sercomp_rep)
     apply (simp add: f0)
    by (simp add: rev_inv_rev)
  have f3: "uspecRevSet\<cdot>(S1 \<circle> (S2 \<circle> S3)) = 
      Rev {f1 \<circ> f2 |f1 f2. f1 \<in> Rep_rev_uspec S1 \<and> f2 \<in> Rep_rev_uspec (S2 \<circle> S3)}"
    apply (simp add: uspecrevset_insert)
    apply (subst uspec_sercomp_rep)
     apply (simp add: f1)
    by (simp add: rev_inv_rev)
  have f10: "{ ufSerComp f1 f2 |(f1::('a,'c) ufun) (f2::('c,'d) ufun). f1 \<in> (Rep_rev_uspec (S1 \<circle> S2)) \<and> (f2 \<in> Rep_rev_uspec S3)} =
              { ufSerComp f1 f2 |(f1::('a,'b) ufun) (f2::('b,'d) ufun). f1 \<in> (Rep_rev_uspec S1) \<and> f2 \<in> (Rep_rev_uspec (S2 \<circle> S3))}"
    
    sorry
(*  apply (rule subset_antisym)
     apply (rule subsetI)
  proof auto
    show "\<And>(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec (S1 \<circle> S2) \<Longrightarrow> f2 \<in> Rep_rev_uspec S3 \<Longrightarrow> \<exists>(f1a::'a) f2a::'a. f1 \<circ> f2 = f1a \<circ> f2a \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec (S2 \<circle> S3)"
    proof -
      fix f1::'a and f2::'a
      assume f1_def: "f1 \<in> Rep_rev_uspec (S1 \<circle> S2)" and f2_def: "f2 \<in> Rep_rev_uspec S3"
      obtain f3 f4 where f3_def: "f3 \<in> Rep_rev_uspec S1" and f4_def: "f4 \<in> Rep_rev_uspec S2" 
        and f1_eq_f3_f4: "f1 = f3 \<circ> f4"
        by (metis assms(1) empty_iff f1_def uspecIsConsistent_def uspec_sercomp_ele_ex)
      have f1: " f1 \<circ> f2 = f3 \<circ> (f4 \<circ> f2)"
        apply (subst f1_eq_f3_f4)
        by (metis assms(1) assms(2) f2_def f3_def f4_def sercomp_asso uspec_sercompwell2ufunclsercompwell)
      then show "\<exists>(f1a::'a) f2a::'a. f1 \<circ> f2 = f1a \<circ> f2a \<and> f1a \<in> Rep_rev_uspec S1 \<and> f2a \<in> Rep_rev_uspec (S2 \<circle> S3)"
        using assms(2) f2_def f3_def f4_def uspec_sercomp_h1 by blast
    qed
  next
    show "\<And>(f1::'a) f2::'a. f1 \<in> Rep_rev_uspec S1 \<Longrightarrow> f2 \<in> Rep_rev_uspec (S2 \<circle> S3) \<Longrightarrow> \<exists>(f1a::'a) f2a::'a. f1 \<circ> f2 = f1a \<circ> f2a \<and> f1a \<in> Rep_rev_uspec (S1 \<circle> S2) \<and> f2a \<in> Rep_rev_uspec S3"
    proof -
      fix f1::'a and f2::'a
      assume f1_def: "f1 \<in> Rep_rev_uspec S1" and f2_def: "f2 \<in> Rep_rev_uspec (S2 \<circle> S3)"
      obtain f3 f4 where f3_def: "f3 \<in> Rep_rev_uspec S2" and f4_def: "f4 \<in> Rep_rev_uspec S3" 
                    and f2_eq_f3_f4: "f2 = f3 \<circ> f4"
        using assms(2) f2_def uspec_sercomp_rep by blast
      have f1: "f1 \<circ> f2 = (f1 \<circ> f3) \<circ> f4"
        apply (subst f2_eq_f3_f4)
        using assms(1) assms(2) f1_def f3_def f4_def sercomp_asso uspec_sercompwell2ufunclsercompwell by blast
      then show "\<exists>(f1a::'a) f2a::'a. f1 \<circ> f2 = f1a \<circ> f2a \<and> f1a \<in> Rep_rev_uspec (S1 \<circle> S2) \<and> f2a \<in> Rep_rev_uspec S3"
        using assms(1) f1_def f3_def f4_def uspec_sercomp_not_empty by blast
    qed
  qed*)
  have f11: "uspecRevSet\<cdot>(S1 \<circle> S2 \<circle> S3) = uspecRevSet\<cdot>(S1 \<circle> (S2 \<circle> S3))"
    by (simp add: f10 f2 f3)
  show ?thesis
    apply (rule uspec_eqI)
      apply (simp add: f11)
     apply (simp add: assms(1) f0 f1 uspec_sercomp_dom)
    by (simp add: assms(2) f0 f1 uspec_sercomp_ran)
qed


subsection \<open>UspecFeedbackComp\<close>


lemma uspec_feedbackcomp_well: "uspecWell (Rev {ufFeedbackComp f1 | f1.  f1\<in>(Rep_rev_uspec S1)})
  (Discr (uspecDom\<cdot>S1 - uspecRan\<cdot>S1)) (Discr (uspecRan\<cdot>S1))"
  apply (rule uspec_wellI)
  using ufclDom_ufun_def ufFeedbackComp_dom
   apply (smt mem_Collect_eq ufclRan_ufun_def uspecRevSet_condition uspecrevset_insert) 
  using ufclRan_ufun_def ufFeedbackComp_ran
  by (smt mem_Collect_eq uspecRevSet_condition uspecrevset_insert)

lemma uspec_feedbackcomp_insert: "uspecFeedbackComp S1 = 
  Abs_rev_uspec  {ufFeedbackComp f1 | f1.  f1\<in>(Rep_rev_uspec S1)}
  (uspecDom\<cdot>S1 - uspecRan\<cdot>S1) (uspecRan\<cdot>S1)"
  by (simp add: uspecFeedbackComp_def)

lemma uspec_feedbackcomp_consistent_iff: "uspecIsConsistent (uspecFeedbackComp S) = uspecIsConsistent S"
  apply (simp add: uspecIsConsistent_def uspecFeedbackComp_def)
  apply (subst rep_abs_rev_simp)
   apply (simp only: uspec_feedbackcomp_well)
  apply rule
  by simp+

lemma uspec_feecbackcomp_dom: "uspecDom\<cdot>(uspecFeedbackComp S) = uspecDom\<cdot>S - uspecRan\<cdot>S"
  apply (simp add: uspecFeedbackComp_def)
  apply (subst uspecdom_insert)
  apply (simp only: uspec_feedbackcomp_well rep_abs_uspec)
  by simp

lemma uspec_feecbackcomp_ran: "uspecRan\<cdot>(uspecFeedbackComp S) = uspecRan\<cdot>S"
  apply (simp add: uspecFeedbackComp_def)
  apply (subst uspecran_insert)
  apply (simp only: uspec_feedbackcomp_well rep_abs_uspec)
  by simp

lemma uspec_feedbackcomp_f_ex: assumes "f \<in> Rep_rev_uspec (uspecFeedbackComp S)"
  shows "\<exists> f1 \<in> Rep_rev_uspec S. f = ufFeedbackComp f1"
proof -
  have "Rep_uspec (Abs_rev_uspec {ufFeedbackComp a |a. a \<in> Rep_rev_uspec S} (uspecDom\<cdot>S - uspecRan\<cdot>S) (uspecRan\<cdot>S)) = (Rev {ufFeedbackComp a |a. a \<in> Rep_rev_uspec S}, Discr (uspecDom\<cdot>S - uspecRan\<cdot>S), Discr (uspecRan\<cdot>S))"
    using rep_abs_uspec uspec_feedbackcomp_well by blast
  then have "{ufFeedbackComp a |a. a \<in> Rep_rev_uspec S} = Rep_rev_uspec (uspecFeedbackComp S)"
    by (simp add: inv_rev_rev uspec_feedbackcomp_insert)
  then have "\<exists>a. f = (ufFeedbackComp a) \<and> a \<in> Rep_rev_uspec S"
    using assms by blast
  then show ?thesis
    by blast
qed



end