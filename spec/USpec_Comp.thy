theory USpec_Comp
  imports USpec  inc.CPOFix
begin

default_sort ufuncl_comp

(****************************************************)
section\<open>Definitions\<close>
(****************************************************)   
 
(* Smallest possible USpec: Smallest means "least specified", i.e. ALL ufuns with I/O property *)
definition uspecLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> 'm uspec" where
"uspecLeast cin cout = Abs_rev_uspec {f. ufclDom\<cdot>f = cin \<and> ufclRan\<cdot>f = cout} cin cout"

definition uspecFix ::"channel set \<Rightarrow> channel set \<Rightarrow> ('a uspec \<rightarrow> 'a uspec) \<rightarrow> 'a uspec" where
"uspecFix cin cout \<equiv> (\<Lambda> F.  fixg (uspecLeast cin cout)\<cdot>F)"

definition uspecStateLeast :: "channel set \<Rightarrow> channel set \<Rightarrow>'s::type \<Rightarrow> 'm uspec" where
"uspecStateLeast In Out \<equiv> (\<lambda> x. uspecLeast In Out)"

definition uspecStateFix ::"channel set \<Rightarrow> channel set \<Rightarrow> (('s::type \<Rightarrow> 'm uspec) \<rightarrow> ('s \<Rightarrow> 'm uspec)) \<rightarrow> ('s \<Rightarrow> 'm uspec)" where
"uspecStateFix In Out \<equiv> (\<Lambda> F.  fixg (uspecStateLeast In Out)\<cdot>F)"

definition uspecImage::  "('m \<Rightarrow> 'n) \<Rightarrow> 'm uspec \<Rightarrow> 'n uspec" where
"uspecImage f \<equiv>  \<lambda> S.
Abs_uspec ((setrevImage f (uspecRevSet\<cdot>S)), 
  Discr (ufclDom\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))),
  Discr (ufclRan\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))))"

(****************************************************)
section\<open>Lemmas\<close>
(****************************************************)   

subsection \<open>uspecLeast\<close>

lemma uspecLeast_well[simp]: "uspecWell (Rev {f. ufclDom\<cdot>f = cin \<and> ufclRan\<cdot>f = cout}) (Discr cin) (Discr cout)"
  by auto

lemma uspecLeast_contains_ufLeast: "ufunclLeast cin cout \<in> Rep_rev_uspec(uspecLeast cin cout)"
  by (simp add: inv_rev_rev ufuncldom_least_dom ufuncldom_least_ran uspecLeast_def)

lemma uspecLeast_consistent: "uspecIsConsistent (uspecLeast cin cout)"
  using not_uspec_consisten_empty_eq uspecLeast_contains_ufLeast by auto    

lemma uspecLeast_dom: "uspecDom\<cdot>(uspecLeast cin cout) = cin"
  by (simp add: uspecLeast_def uspecdom_insert)

lemma uspecLeast_ran: "uspecRan\<cdot>(uspecLeast cin cout) = cout"
  by (simp add: uspecLeast_def uspecran_insert)

lemma uspecLeast_min: assumes "uspecDom\<cdot>S = In"
                          and "uspecRan\<cdot>S = Out"
                        shows "uspecLeast In Out \<sqsubseteq> S"
  proof -
    have "\<And>f. f \<in> (Rep_rev_uspec S) \<Longrightarrow> ufclDom\<cdot>f = In \<and> ufclRan\<cdot>f = Out"
      by (simp add: assms rep_rev_revset uspec_allDom uspec_allRan)
    moreover have "\<And>f. ufclDom\<cdot>f = In \<and> ufclRan\<cdot>f = Out \<Longrightarrow> f \<in> Rep_rev_uspec (uspecLeast In Out)"
      by (metis (mono_tags, lifting) CollectI rep_abs_rev_simp uspecLeast_def uspecLeast_well)
    ultimately have "\<And>f. f \<in> (Rep_rev_uspec S) \<Longrightarrow> f \<in> Rep_rev_uspec (uspecLeast In Out)"
      by auto
    then have "Rep_rev_uspec S \<subseteq> Rep_rev_uspec (uspecLeast In Out)"
      by(simp add: subsetI)
    then show ?thesis
      by (simp add: assms revBelowNeqSubset uspecLeast_dom uspecLeast_ran uspec_belowI uspecrevset_insert)
  qed

lemma uspecLeast_min2: "(uspecLeast (uspecDom\<cdot>S) (uspecRan\<cdot>S)) \<sqsubseteq> S"
  using uspecLeast_min by auto

lemma uspecLeast_union: "uspecUnion\<cdot>f\<cdot>(uspecLeast (uspecDom\<cdot>f) (uspecRan\<cdot>f)) = (uspecLeast (uspecDom\<cdot>f) (uspecRan\<cdot>f))"
  apply(rule uspec_eqI2)
  apply(rule setrev_eqI)
  apply(rule set_eqI)
  apply auto
  apply(metis (mono_tags, lifting) CollectI rep_abs_rev_simp uspecLeast_def uspecLeast_well uspecUnion_setrev_condition uspec_allDom uspec_allRan uspecrevset_insert)
  apply(simp add: uspecLeast_dom uspecLeast_ran uspecUnion_setrev_condition uspec_allDom uspec_allRan)
  by (simp add: uspecLeast_consistent uspecLeast_dom uspecLeast_ran uspecUnion_consistent2)

lemma uspecLeast_union_consistent: "uspecIsConsistent(uspecUnion\<cdot>f\<cdot>(uspecLeast (uspecDom\<cdot>f) (uspecRan\<cdot>f)))"
  by(simp add: uspecLeast_union uspecLeast_consistent)

subsection \<open>uspecFix\<close>

abbreviation uspec_io_eq :: "('m uspec \<rightarrow> 'm uspec) \<Rightarrow> channel set \<Rightarrow> channel set \<Rightarrow> bool" where
"uspec_io_eq F cin cout \<equiv> uspecDom\<cdot>(F\<cdot>(uspecLeast cin cout)) = cin \<and> 
                          uspecRan\<cdot>(F\<cdot>(uspecLeast cin cout)) = cout"


lemma uspecfix_insert: "uspecFix cin cout\<cdot>F = fixg (uspecLeast cin cout)\<cdot>F"
  by (simp add: uspecFix_def)


lemma uspecfix_insert2: assumes "uspec_io_eq F cin cout" 
  shows "uspecFix cin cout\<cdot>F = (\<Squnion>i::nat. iterate i\<cdot>F\<cdot>(uspecLeast cin cout))"
  apply (simp add: uspecFix_def fixg_def)
  apply (subst Abs_cfun_inverse2)
   apply (rule fixg_cont)
   apply (metis (no_types, lifting) uspecLeast_dom uspecLeast_min uspecLeast_ran uspecdom_eq uspecran_eq)
  by (simp add: assms uspecLeast_min)

lemma uspecfix_mono: "monofun (\<lambda> F.  fixg (uspecLeast cin cout)\<cdot>F)"
  by (simp add: monofun_Rep_cfun2)

lemma uspecfix_cont[simp]: "cont (\<lambda> F.  fixg (uspecLeast cin cout)\<cdot>F)"
  by simp

lemma uspecfix_eq: assumes "uspec_io_eq F cin cout"
  shows "uspecFix cin cout\<cdot>F =  F\<cdot>(uspecFix cin cout\<cdot>F)"
  apply (simp add: uspecfix_insert)
  apply (rule fixg_fix)
   apply (simp add: assms uspecLeast_min)
  by (metis (no_types, hide_lams) uspecLeast_dom uspecLeast_min2 uspecLeast_ran uspecdom_eq uspecran_eq)

lemma uspecfix_least_below: assumes "uspec_io_eq F cin cout" and "uspecDom\<cdot>x = cin" and "uspecRan\<cdot>x = cout"
  shows "F\<cdot>x \<sqsubseteq> x \<Longrightarrow> (uspecFix cin cout\<cdot>F) \<sqsubseteq> x"
  apply (simp add: uspecFix_def)
  apply (rule fixg_least_below)
     apply (simp add: assms(1) uspecLeast_min)
    apply (metis (no_types, hide_lams) uspecLeast_dom uspecLeast_min uspecLeast_ran uspecdom_eq uspecran_eq)
   apply (simp add: assms(2) assms(3) uspecLeast_min)
  by simp

lemma uspecfix_least: assumes "uspec_io_eq F cin cout" and "uspecDom\<cdot>x = cin" and "uspecRan\<cdot>x = cout"
                    and "F\<cdot>x = x"
                  shows "(uspecFix cin cout\<cdot>F) \<sqsubseteq> x"
  by (simp add: assms(1) assms(2) assms(3) assms(4) uspecfix_least_below)

lemma uspecfix_eqI: 
  assumes fp: "F\<cdot>x = x" and
    lst: "\<And>z. uspecDom\<cdot>z = cin \<and> uspecRan\<cdot>z=cout \<Longrightarrow> F\<cdot>z = z \<Longrightarrow> x \<sqsubseteq> z"
    and "uspec_io_eq F cin cout" and "uspecDom\<cdot>x = cin" and "uspecRan\<cdot>x = cout"
  shows "(uspecFix cin cout\<cdot>F) = x"
proof -
  have f1: "\<And>c u. c\<cdot>(u::'a uspec) \<notsqsubseteq> u \<or> 
    uspecRan\<cdot> (c\<cdot>(uspecLeast (uspecDom\<cdot>u) (uspecRan\<cdot>u))) \<noteq> uspecRan\<cdot>u \<or> 
    uspecDom\<cdot> (c\<cdot>(uspecLeast (uspecDom\<cdot>u) (uspecRan\<cdot>u))) \<noteq> uspecDom\<cdot>u \<or> 
    Abs_cfun (Rep_cfun (fixg (uspecLeast (uspecDom\<cdot>u) (uspecRan\<cdot>u))))\<cdot> c \<sqsubseteq> u"
    by (metis uspecFix_def uspecfix_least_below)
  then have f2: "Abs_cfun (Rep_cfun (fixg (uspecLeast cin cout)))\<cdot>F \<sqsubseteq> x"
using assms(3) assms(4) assms(5) fp po_eq_conv by blast
  then have "uspecDom\<cdot>(Abs_cfun (Rep_cfun (fixg (uspecLeast cin cout)))\<cdot>F) = cin"
    using assms(4) by auto
  then have "x \<sqsubseteq> Abs_cfun (Rep_cfun (fixg (uspecLeast cin cout)))\<cdot>F"
using f2 by (metis assms(3) assms(5) lst uspecFix_def uspecfix_eq uspecran_eq)
  then show ?thesis
    using f1 by (metis (no_types) assms(3) assms(4) assms(5) fp po_eq_conv uspecFix_def)
qed

lemma uspecfix_least_iff: assumes "uspec_io_eq F cin cout"
  shows "((uspecFix cin cout\<cdot>F) = uspecLeast cin cout) = 
            (F\<cdot>(uspecLeast cin cout) = uspecLeast cin cout)"
  by (metis assms uspecLeast_min uspecfix_eq uspecfix_eqI)

lemma uspecfix_strict: assumes "uspec_io_eq F cin cout" and "F\<cdot>(uspecLeast cin cout) = (uspecLeast cin cout)"
  shows "(uspecFix cin cout\<cdot>F) = uspecLeast cin cout"
  using assms(1) assms(2) uspecfix_least_iff by blast

lemma uspecfix_defined: assumes "uspec_io_eq F cin cout" 
  and "F\<cdot>(uspecLeast cin cout) \<noteq> (uspecLeast cin cout)"
  shows "(uspecFix cin cout\<cdot>F) \<noteq> uspecLeast cin cout"
  by (simp add: assms(1) assms(2) uspecfix_least_iff)

lemma uspecfix_id: "(uspecFix cin cout\<cdot>(\<Lambda> x. x)) = (uspecLeast cin cout)"
  by (simp add: uspecLeast_dom uspecLeast_ran uspecfix_least_iff)

lemma uspecfix_const: assumes "uspecDom\<cdot>c = cin" and "uspecRan\<cdot>c = cout"
  shows "(uspecFix cin cout\<cdot>(\<Lambda> x. c)) = c"
  apply (rule uspecfix_eqI)
  by (simp add: assms(1) assms(2)) +

lemma uspec_iterate_chain: assumes "uspec_io_eq F cin cout"
  shows "chain (\<lambda>i. iterate i\<cdot>F\<cdot>(uspecLeast cin cout))"
  apply (rule chainI, subst iterate_Suc2)
  apply(rule Cfun.monofun_cfun_arg)
  by (simp add: assms uspecLeast_min)

lemma iter_uspecfix_dom: assumes "uspec_io_eq F cin cout" 
  shows "uspecDom\<cdot>( iterate i\<cdot>F\<cdot>(uspecLeast cin cout)) = cin"
  apply (induction i)
   apply (simp add: uspecLeast_dom)
  by (metis (mono_tags, lifting) assms po_class.chain_def uspec_iterate_chain uspecdom_eq)

lemma iter_upecfix_ran: assumes "uspec_io_eq F cin cout" 
  shows "uspecRan\<cdot>( iterate i\<cdot>F\<cdot>(uspecLeast cin cout)) = cout"
  apply (induction i)
   apply (simp add: uspecLeast_dom)
   apply (simp add: uspecLeast_ran)
  by (metis (mono_tags, lifting) assms po_class.chain_def uspec_iterate_chain uspecran_eq)

lemma uspecfix_ind: assumes "uspec_io_eq F cin cout" 
                  and "adm P" and "P (uspecLeast cin cout)"
                  and "\<And> x. \<lbrakk>uspecDom\<cdot>x = cin; uspecRan\<cdot>x = cout; P x\<rbrakk> \<Longrightarrow> P (F\<cdot>x)"
                shows "P (uspecFix cin cout\<cdot>F)"
  apply (simp add: assms(1) uspecfix_insert2)
  apply (subst admD, simp_all add: assms)
   apply (metis assms(1) iter_fixg_chain uspecLeast_min2)
  apply (rule nat_induct)
   apply (simp add: assms(3)) +
  by (simp add: assms(1) assms(4) iter_upecfix_ran iter_uspecfix_dom)


lemma cont_uspecfix_ind: assumes "cont F" and  "uspec_io_eq (Abs_cfun F) cin cout" 
                  and "adm P" and "P (uspecLeast cin cout)"
                  and "\<And> x. \<lbrakk>uspecDom\<cdot>x = cin; uspecRan\<cdot>x = cout; P x\<rbrakk> \<Longrightarrow> P (F x)"
                shows "P (uspecFix cin cout\<cdot>(Abs_cfun F))"
  by (metis Abs_cfun_inverse2 assms(1) assms(2) assms(3) assms(4) assms(5) uspecfix_ind)

lemma uspecfix_ind2:  assumes "uspec_io_eq F cin cout" 
                  and "adm P" and s0:"P (uspecLeast cin cout)" and s1: "P (F\<cdot>(uspecLeast cin cout))"
                    and s2: "\<And> x. \<lbrakk>uspecDom\<cdot>x = cin; uspecRan\<cdot>x = cout; P x; P (F\<cdot>x)\<rbrakk> \<Longrightarrow> P (F\<cdot>(F\<cdot>x))"
                  shows "P (uspecFix cin cout\<cdot>F)"
  apply (simp add: assms(1) uspecfix_insert2)
  apply (subst admD, simp_all add: assms)
   apply (simp add: assms(1) uspec_iterate_chain)
  apply (rule nat_less_induct)
  apply (case_tac n)
   apply (simp add: s0)
  apply (case_tac nat)
   apply (simp add: s1)
  apply (frule_tac x=nat in spec)
  by (simp add: assms(1) iter_upecfix_ran iter_uspecfix_dom s2)


subsection\<open>uspecImage\<close>


lemma  uspecimage_well:
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  shows "uspecWell (setrevImage f (uspecRevSet\<cdot>S)) 
  (Discr (ufclDom\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))))
  (Discr (ufclRan\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))))"
  by (simp add: assms setrevImage_def ufuncldom_least_dom ufuncldom_least_ran uspec_allDom uspec_allRan)

lemma uspecimage_useful_uspecrevset:
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  shows  "uspecRevSet\<cdot>(uspecImage f S) = setrevImage f (uspecRevSet\<cdot>S)"
  by (smt assms uspecimage_well rep_abs_rev_simp rev_inv_rev setrevImage_def uspecImage_def uspecrevset_insert)

lemma uspecimage_useful_dom:
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  shows  "uspecDom\<cdot>(uspecImage f S) = ufclDom\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))"
 by (smt assms fst_conv uspecimage_well rep_abs_uspec snd_conv undiscr_Discr uspecImage_def uspecdom_insert)

lemma uspecimage_useful_ran:
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  shows "uspecRan\<cdot>(uspecImage f S) = ufclRan\<cdot> (f (ufunclLeast (uspecDom\<cdot> S) (uspecRan\<cdot> S)))"
 by (smt assms fst_conv uspecimage_well rep_abs_uspec snd_conv undiscr_Discr uspecImage_def uspecran_insert)

lemma  uspecimage_mono: 
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>((f::('m::ufuncl_comp \<Rightarrow> 'n::ufuncl_comp)) x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
shows "monofun (uspecImage f)"
proof (rule monofunI)
  have b0:  "\<And>(x::'m uspec) y::'m uspec. x \<sqsubseteq> y 
  \<Longrightarrow> (setrevImage f (uspecRevSet\<cdot>x))  \<sqsubseteq> (setrevImage f (uspecRevSet\<cdot>y))"
    by (metis image_mono inv_rev_rev monofun_cfun_arg revBelowNeqSubset setrevImage_def)
  have b1: "\<And>(x::'m uspec) y::'m uspec. x \<sqsubseteq> y 
  \<Longrightarrow> (uspecRevSet\<cdot>(uspecImage f x)) \<sqsubseteq> (uspecRevSet\<cdot>(uspecImage f y))"
    by (metis (full_types) assms b0 uspecimage_useful_uspecrevset)
  show "\<And>(x::'m uspec) y::'m uspec. x \<sqsubseteq> y \<Longrightarrow> uspecImage f x \<sqsubseteq> uspecImage f y"
    by (smt assms b1 uspecimage_useful_dom uspecimage_useful_ran uspec_belowI uspecdom_eq uspecran_eq)
qed 

lemma  uspecimage_cont_uspecrevset:
 assumes "inj (f::('m::ufuncl_comp \<Rightarrow> 'n::ufuncl_comp))"
  and "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  and "chain Y"
  and "chain (\<lambda>i::nat. uspecImage f (Y i))"
shows "uspecRevSet\<cdot>(uspecImage f (\<Squnion>i::nat. Y i)) \<sqsubseteq> uspecRevSet\<cdot>((\<Squnion>i::nat. uspecImage f (Y i)))"
proof -
  have b0: "\<And>S. uspecRevSet\<cdot>(uspecImage f S) = setrevImage f (uspecRevSet\<cdot>S)"
    by (metis assms(2) uspecimage_useful_uspecrevset)
  have b1: "uspecRevSet\<cdot>(uspecImage f (\<Squnion>i::nat. Y i)) = setrevImage f (uspecRevSet\<cdot>(\<Squnion>i::nat. Y i))"
    by (simp add: b0)
  have b2: "setrevImage f (uspecRevSet\<cdot>(\<Squnion>i::nat. Y i)) = setrevImage f (\<Squnion>i::nat. uspecRevSet\<cdot>(Y i))"
    by (metis assms(3) contlub_cfun_arg)
  have b3: "setrevImage f (\<Squnion>i::nat. uspecRevSet\<cdot>(Y i)) \<sqsubseteq> (\<Squnion>i::nat. setrevImage f (uspecRevSet\<cdot>(Y i)))"
    using image_cont_rev assms(1) assms(3) ch2ch_Rep_cfunR cont2contlubE eq_imp_below by blast
  have b4: "(\<Squnion>i::nat. setrevImage f (uspecRevSet\<cdot>(Y i))) = (\<Squnion>i::nat. uspecRevSet\<cdot>(uspecImage f (Y i)))"
    using b0 by auto
  have b5: "(\<Squnion>i::nat. uspecRevSet\<cdot>(uspecImage f (Y i))) = uspecRevSet\<cdot>((\<Squnion>i::nat. uspecImage f (Y i)))"
    by (simp add: assms(4) cont2contlubE)
  show ?thesis
    using b1 b2 b3 b4 b5 by auto
qed

lemma uspecimage_cont_helper: 
  assumes "inj (f::('m::ufuncl_comp \<Rightarrow> 'n::ufuncl_comp))"
  and "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
shows "cont (uspecImage f)"
  apply (rule Cont.contI2)
  subgoal
    using assms(1) assms(2) uspecimage_mono by blast
  subgoal
  proof -
    have b0: "\<And>Y. chain Y \<Longrightarrow> chain (\<lambda>i::nat. uspecImage f (Y i)) 
      \<Longrightarrow> uspecDom\<cdot>(uspecImage f (\<Squnion>i::nat. Y i)) = uspecDom\<cdot>(\<Squnion>i::nat. uspecImage f (Y i))"
      by (metis (no_types) \<open>monofun (uspecImage (f::'m::ufuncl_comp \<Rightarrow> 'n::ufuncl_comp))\<close> 
        is_ub_thelub monofun_def uspecdom_eq)
    have b1: "\<And>Y. chain Y \<Longrightarrow> chain (\<lambda>i::nat. uspecImage f (Y i)) 
      \<Longrightarrow> uspecRan\<cdot>(uspecImage f (\<Squnion>i::nat. Y i)) = uspecRan\<cdot>(\<Squnion>i::nat. uspecImage f (Y i))"
      by (metis (no_types) \<open>monofun (uspecImage (f::'m::ufuncl_comp \<Rightarrow> 'n::ufuncl_comp))\<close> 
        is_ub_thelub monofun_def uspecran_eq)
    show  "\<And>Y. chain Y \<Longrightarrow> chain (\<lambda>i::nat. uspecImage f (Y i)) 
      \<Longrightarrow> uspecImage f (\<Squnion>i::nat. Y i) \<sqsubseteq> (\<Squnion>i::nat. uspecImage f (Y i))"
proof -
fix Ya :: "nat \<Rightarrow> 'm uspec"
assume a1: "chain Ya"
  assume a2: "chain (\<lambda>i. uspecImage f (Ya i))"
  have "\<forall>f fa. (inj fa \<and> (\<forall>m ma. ufclDom\<cdot>(m::'m) = ufclDom\<cdot>ma \<and> ufclRan\<cdot>m = ufclRan\<cdot>ma \<longrightarrow> ufclDom\<cdot>(fa m::'n) = ufclDom\<cdot>(fa ma) 
    \<and> ufclRan\<cdot>(fa m) = ufclRan\<cdot>(fa ma)) \<and> chain f \<and> chain (\<lambda>n. uspecImage fa (f n)) \<longrightarrow> uspecRevSet\<cdot>(uspecImage fa (Lub f)) 
    \<sqsubseteq> uspecRevSet\<cdot>(\<Squnion>n. uspecImage fa (f n))) = ((\<not> inj fa \<or> (\<exists>m ma. (ufclDom\<cdot>m = ufclDom\<cdot>ma \<and> ufclRan\<cdot>m = ufclRan\<cdot>ma) 
    \<and> (ufclDom\<cdot>(fa m) \<noteq> ufclDom\<cdot>(fa ma) \<or> ufclRan\<cdot>(fa m) \<noteq> ufclRan\<cdot>(fa ma))) \<or> \<not> chain f \<or> \<not> chain (\<lambda>n. uspecImage fa (f n))) 
    \<or> uspecRevSet\<cdot>(uspecImage fa (Lub f)) \<sqsubseteq> uspecRevSet\<cdot>(\<Squnion>n. uspecImage fa (f n)))"
  by meson
  then have f3: "\<forall>f fa. (\<not> inj f \<or> (\<exists>m ma. (ufclDom\<cdot>(m::'m) = ufclDom\<cdot>ma \<and> ufclRan\<cdot>m = ufclRan\<cdot>ma) \<and> (ufclDom\<cdot>(f m::'n) 
    \<noteq> ufclDom\<cdot>(f ma) \<or> ufclRan\<cdot>(f m) \<noteq> ufclRan\<cdot>(f ma))) \<or> \<not> chain fa \<or> \<not> chain (\<lambda>n. uspecImage f (fa n))) \<or> 
    uspecRevSet\<cdot>(uspecImage f (Lub fa)) \<sqsubseteq> uspecRevSet\<cdot>(\<Squnion>n. uspecImage f (fa n))"
    by (metis uspecimage_cont_uspecrevset)
  have f4: "\<forall>f. ((ufclDom\<cdot>(v2_3 f::'m) \<noteq> ufclDom\<cdot>(v3_2 f) \<or> ufclRan\<cdot>(v2_3 f) \<noteq> ufclRan\<cdot>(v3_2 f)) \<or> ufclDom\<cdot>(f (v2_3 f)::'n) 
    = ufclDom\<cdot>(f (v3_2 f)) \<and> ufclRan\<cdot>(f (v2_3 f)) = ufclRan\<cdot>(f (v3_2 f))) = ((ufclDom\<cdot>(v2_3 f) \<noteq> ufclDom\<cdot>(v3_2 f) \<or> ufclRan\<cdot>(v2_3 f) 
    \<noteq> ufclRan\<cdot>(v3_2 f)) \<or> ufclDom\<cdot>(f (v2_3 f)) = ufclDom\<cdot>(f (v3_2 f)) \<and> ufclRan\<cdot>(f (v2_3 f)) = ufclRan\<cdot>(f (v3_2 f)))"
    by metis
  obtain nn :: "(nat \<Rightarrow> 'n uspec) \<Rightarrow> nat" where
    "\<forall>f. (\<not> chain f \<or> (\<forall>n. f n \<sqsubseteq> f (Suc n))) \<and> (chain f \<or> f (nn f) \<notsqsubseteq> f (Suc (nn f)))"
    using po_class.chain_def by moura
  then obtain mm :: "('m \<Rightarrow> 'n) \<Rightarrow> 'm" and mma :: "('m \<Rightarrow> 'n) \<Rightarrow> 'm" where
    f5: "ufclDom\<cdot>(mm f) = ufclDom\<cdot>(mma f) \<and> ufclRan\<cdot>(mm f) = ufclRan\<cdot>(mma f) \<and> (ufclDom\<cdot>(f (mm f)) \<noteq> ufclDom\<cdot>(f (mma f)) 
    \<or> ufclRan\<cdot>(f (mm f)) \<noteq> ufclRan\<cdot>(f (mma f))) \<or> uspecRevSet\<cdot>(uspecImage f (Lub Ya)) \<sqsubseteq> uspecRevSet\<cdot>(\<Squnion>n. uspecImage f (Ya n))"
    using f4 f3 a2 a1 by (meson assms(1))
  have f6: "uspecDom\<cdot>(uspecImage f (Lub Ya)) = uspecDom\<cdot>(\<Squnion>n. uspecImage f (Ya n))"
    using a2 a1 b0 by presburger
  have "uspecRevSet\<cdot>(uspecImage f (Lub Ya)) \<sqsubseteq> uspecRevSet\<cdot>(\<Squnion>n. uspecImage f (Ya n))"
    using f5 by (meson assms(2))
  then show "uspecImage f (\<Squnion>n. Ya n) \<sqsubseteq> (\<Squnion>n. uspecImage f (Ya n))"
    using f6 a2 a1 by (metis (no_types) b1 uspec_belowI)
qed

qed
done


lemma uspecimage_inj_cont: 
  assumes "inj f"
      and "\<And>x y. ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y \<Longrightarrow>
          ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)"
    shows "cont (uspecImage f)"
  using assms uspecimage_cont_helper by blast

lemma uspecimage_helper:
  assumes "\<And>x. ufclDom\<cdot>x =  ufclDom\<cdot> (f x)"
    and "\<And>x. ufclRan\<cdot>x =  ufclRan\<cdot> (f x)"
  shows "ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y \<Longrightarrow>
          ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)"
  by (simp add: assms(1) assms(2))
  
lemma uspecimage_dom1 [simp]:
  assumes "\<And>x. ufclDom\<cdot>x =  ufclDom\<cdot> (f x)"
    and "\<And>x. ufclRan\<cdot>x =  ufclRan\<cdot> (f x)"
  shows "uspecDom\<cdot>(uspecImage f S) = uspecDom\<cdot>S"
  using assms
  by (metis ufuncldom_least_dom uspecimage_useful_dom) 

lemma uspecimage_ran1 [simp]:
  assumes "\<And>x. ufclDom\<cdot>x =  ufclDom\<cdot> (f x)"
    and "\<And>x. ufclRan\<cdot>x =  ufclRan\<cdot> (f x)"
  shows "uspecRan\<cdot>(uspecImage f S) = uspecRan\<cdot>S"
  using assms
  by (metis ufuncldom_least_ran uspecimage_useful_ran)

lemma urs_img_inj:
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
      and "inj f"
      and "uspecRevSet\<cdot>(uspecImage f S1) = uspecRevSet\<cdot>(uspecImage f S2)"
    shows "uspecRevSet\<cdot>S1 = uspecRevSet\<cdot>S2"
proof -
  have f1: "\<forall>a aa. (ufclDom\<cdot>a \<noteq> ufclDom\<cdot>aa \<or> ufclRan\<cdot>a \<noteq> ufclRan\<cdot>aa) \<or> ufclDom\<cdot>(f a) = ufclDom\<cdot>(f aa) 
    \<and> ufclRan\<cdot>(f a) = ufclRan\<cdot>(f aa)"
    by (meson assms(1))
  have "\<forall>f u. (\<exists>a aa. (ufclDom\<cdot>(a::'a) = ufclDom\<cdot>aa \<and> ufclRan\<cdot>a = ufclRan\<cdot>aa) \<and> (ufclDom\<cdot>(f a::'b) 
    \<noteq> ufclDom\<cdot>(f aa) \<or> ufclRan\<cdot>(f a) \<noteq> ufclRan\<cdot>(f aa))) \<or> uspecRevSet\<cdot>(uspecImage f u) = setrevImage
    f (uspecRevSet\<cdot>u)"
    by (meson uspecimage_useful_uspecrevset)
  then obtain aa :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a" and aaa :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a" where
    "\<forall>f u. ufclDom\<cdot>(aa f) = ufclDom\<cdot>(aaa f) \<and> ufclRan\<cdot>(aa f) = ufclRan\<cdot>(aaa f) \<and> (ufclDom\<cdot>(f (aa f)) 
    \<noteq> ufclDom\<cdot>(f (aaa f)) \<or> ufclRan\<cdot>(f (aa f)) \<noteq> ufclRan\<cdot>(f (aaa f))) \<or> uspecRevSet\<cdot>(uspecImage f u) 
    = setrevImage f (uspecRevSet\<cdot>u)"
    by moura
  then have "setrevImage f (uspecRevSet\<cdot>S1) = setrevImage f (uspecRevSet\<cdot>S2)"
    using f1 by (metis assms(3))
  then show ?thesis
    by (meson assms(2) injD setrevimage_inj_inj)
qed

lemma uspecimage_max: assumes "H = uspecMax In Out"
and  "\<And>x. ufclDom\<cdot> (f x) = ufclDom\<cdot>x"
    and "\<And>x. ufclRan\<cdot> (f x) = ufclRan\<cdot>x"
  shows "uspecImage f H = uspecMax In Out"
  apply (simp add: assms)
  apply (simp add: uspecImage_def)
  apply (simp add: uspecrevset_insert)
  apply (simp add: uspecMax_def)
  apply (simp add: setrevimage_empty assms) 
  by (simp add: ufuncldom_least_dom ufuncldom_least_ran)

lemma uspecimage_not_max: assumes "uspec_in h (uspecImage f H)"
and  "\<And>x. ufclDom\<cdot> (f x) = ufclDom\<cdot>x"
    and "\<And>x. ufclRan\<cdot> (f x) = ufclRan\<cdot>x"
  shows "H \<noteq> uspecMax In Out"
  by (metis assms(1) assms(2) assms(3) empty_iff inv_rev_rev prod.sel(1) uspecMax.rep_eq uspecimage_max uspecrevset_insert)

lemma uspecimage_obtain: assumes "uspec_in h (uspecImage f H)"
and  "\<And>x. ufclDom\<cdot> (f x) = ufclDom\<cdot>x"
    and "\<And>x. ufclRan\<cdot> (f x) = ufclRan\<cdot>x"
  shows "\<exists> g. uspec_in g H \<and> h = f g"
proof -
  have "\<forall>f u. (\<exists>b ba. (ufclDom\<cdot>(b::'b) = ufclDom\<cdot>ba \<and> ufclRan\<cdot>b = ufclRan\<cdot>ba) \<and> (ufclDom\<cdot>(f b::'a) \<noteq> ufclDom\<cdot>(f ba) \<or> ufclRan\<cdot>(f b) \<noteq> ufclRan\<cdot>(f ba))) \<or> uspecRevSet\<cdot>(uspecImage f u) = setrevImage f (uspecRevSet\<cdot>u)"
    by (meson uspecimage_useful_uspecrevset)
  then obtain bb :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b" and bba :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b" where
    f1: "\<forall>f u. (ufclDom\<cdot>(bb f) = ufclDom\<cdot>(bba f) \<and> ufclRan\<cdot>(bb f) = ufclRan\<cdot>(bba f)) \<and> (ufclDom\<cdot>(f (bb f)) \<noteq> ufclDom\<cdot>(f (bba f)) \<or> ufclRan\<cdot>(f (bb f)) \<noteq> ufclRan\<cdot>(f (bba f))) \<or> uspecRevSet\<cdot>(uspecImage f u) = setrevImage f (uspecRevSet\<cdot>u)"
    by moura
  obtain bbb :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b" where
    f2: "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x0 \<and> x2 = x1 v3) = (bbb x0 x1 x2 \<in> x0 \<and> x2 = x1 (bbb x0 x1 x2))"
    by moura
  have "uspecRevSet\<cdot>(uspecImage f H) = setrevImage f (uspecRevSet\<cdot>H)"
    using f1 by (metis (no_types) assms(2) assms(3))
    then have "h \<in> f ` inv Rev (uspecRevSet\<cdot>H)"
      by (metis assms(1) inv_rev_rev setrevImage_def)
  then show ?thesis
    using f2 Bex_def_raw image_iff by blast
qed

lemma uspecimage_ele_in: assumes "uspec_in g H"
and  "\<And>x. ufclDom\<cdot> (f x) = ufclDom\<cdot>x"
    and "\<And>x. ufclRan\<cdot> (f x) = ufclRan\<cdot>x"
  shows "uspec_in (f g) (uspecImage f H)"
  by (simp add: assms(1) assms(2) assms(3) inv_rev_rev setrevImage_def uspecimage_useful_uspecrevset)


lemma uspecimage_const[simp]: assumes  "\<And>x. ufclDom\<cdot> (f x) = ufclDom\<cdot>x"
    and "\<And>x. ufclRan\<cdot> (f x) = ufclRan\<cdot>x"
    shows "uspecImage f (uspecConst uf) = uspecConst (f uf)"
  apply(rule uspec_eqI)
  apply (simp add: assms uspecimage_useful_uspecrevset setrevImage_def)
  by (simp_all add: assms)

subsection \<open>uspecStateLeast\<close>

lemma uspecStateLeast_dom [simp]: "\<forall>x. uspecDom\<cdot>(uspecStateLeast In Out x) = In"
  by (simp add: uspecLeast_dom uspecStateLeast_def)

lemma uspecStateLeast_ran[simp]: "\<forall>x. uspecRan\<cdot>(uspecStateLeast In Out x) = Out"
  by (simp add: uspecLeast_ran uspecStateLeast_def)

lemma uspecStateLeast_apply[simp]:
  shows "uspecStateLeast In Out x = uspecLeast In Out"
  by (simp add: uspecStateLeast_def)


lemma uspecStateLeast_bottom [simp]: assumes "\<forall>x. uspecDom\<cdot>(f x) = In" and " \<forall>x. uspecRan\<cdot>(f x) = Out"
  shows "(uspecStateLeast In Out) \<sqsubseteq> f"
  apply (subst fun_below_iff)
  by (simp add: assms(1) assms(2) uspecLeast_min)

lemma uspecStateLeast_least [simp]: "uspecStateLeast In Out \<sqsubseteq> z \<and> y \<sqsubseteq> z \<longrightarrow> uspecStateLeast In Out \<sqsubseteq> y"
proof -
  have "(uspecStateLeast In Out \<sqsubseteq> z \<and> y \<sqsubseteq> z \<longrightarrow> uspecStateLeast In Out \<sqsubseteq> y) \<or> (\<exists>a. uspecDom\<cdot>(y a) \<noteq> In) \<or> (\<exists>a. uspecRan\<cdot>(y a) \<noteq> Out)"
    by (meson uspecStateLeast_bottom)
  moreover
  { assume "\<exists>a. uspecDom\<cdot>(y a) \<noteq> In"
    then have ?thesis
      by (metis (no_types) fun_below_iff uspecLeast_dom uspecStateLeast_def uspecdom_eq) }
  ultimately show ?thesis
    by (metis fun_below_iff uspecLeast_ran uspecStateLeast_def uspecran_eq)
qed


subsection \<open>uspecStateFix\<close>

lemma uspecStateFix_mono[simp]: "monofun (\<lambda> F.  fixg (uspecStateLeast In Out)\<cdot>F)"
  by (simp add: monofun_Rep_cfun2)

lemma uspecStateFix_cont[simp]: "cont (\<lambda> F.  fixg (uspecStateLeast In Out)\<cdot>F)"
  by simp

lemma uspecStateFix_apply: "uspecStateFix In Out\<cdot>F = fixg (uspecStateLeast In Out)\<cdot>F"
  by(simp add: uspecStateFix_def )

(*least Fixpoint*)

lemma uspecStateFix_fix: assumes "uspecStateLeast In Out \<sqsubseteq> F\<cdot>(uspecStateLeast In Out)"
  shows "uspecStateFix In Out\<cdot>F = F\<cdot>(uspecStateFix In Out\<cdot>F)"
  apply (simp add: uspecStateFix_apply)
  apply (rule fixg_fix)
  by (simp add: assms) +

lemma uspecsl_below_uspecsf: "uspecStateLeast In Out \<sqsubseteq> uspecStateFix In Out\<cdot>F"
  apply (simp add: uspecStateFix_apply)
  apply (simp add: fixg_apply) +
proof -
  have "\<forall>x0 x1. ((x1::'a \<Rightarrow> 'b uspec) \<sqsubseteq> (if x1 \<sqsubseteq> x0\<cdot>x1 then \<Squnion>uub. iterate uub\<cdot>x0\<cdot>x1 else x1)) = (if x1 \<sqsubseteq> x0\<cdot>x1 then x1 \<sqsubseteq> (\<Squnion>uub. iterate uub\<cdot>x0\<cdot>x1) else x1 \<sqsubseteq> x1)"
    by auto
  then have f1: "\<forall>f c. if (f::'a \<Rightarrow> 'b uspec) \<sqsubseteq> c\<cdot>f then f \<sqsubseteq> (\<Squnion>n. iterate n\<cdot>c\<cdot>f) else f \<sqsubseteq> f"
    using fixg_pre by blast
  have "(\<Squnion>n. iterate n\<cdot>F\<cdot>(uspecStateLeast In Out)) = (\<Squnion>n. iterate n\<cdot>F\<cdot>(uspecStateLeast In Out))"
    by fastforce
  then show "uspecStateLeast In Out \<sqsubseteq> F\<cdot>(uspecStateLeast In Out) \<longrightarrow> uspecStateLeast In Out \<sqsubseteq> (\<Squnion>n. iterate n\<cdot>F\<cdot>(uspecStateLeast In Out))"
    using f1 by meson
qed


lemma uspecStateFix_least_fix:
assumes "uspecStateLeast In Out \<sqsubseteq> F\<cdot>(uspecStateLeast In Out)"
and "F\<cdot>y = y" and "\<forall>x. uspecDom\<cdot>(y x) = In" and "\<forall>x. uspecRan\<cdot>(y x) = Out"
shows "uspecStateFix In Out\<cdot>F \<sqsubseteq> y"
  apply (simp add: uspecStateFix_apply)
  apply (rule fixg_least_fix)
  by ( simp_all add: assms)

lemma uspecstatefix_dom:"uspecDom\<cdot>((uspecStateFix In Out\<cdot> f) s) = In"
  by (metis fun_below_iff uspecStateLeast_dom uspecdom_eq uspecsl_below_uspecsf)
    
lemma uspecstatefix_ran:"uspecRan\<cdot>((uspecStateFix In Out\<cdot> f) s) = Out"
  by (metis fun_below_iff uspecLeast_ran uspecStateLeast_def uspecran_eq uspecsl_below_uspecsf)



subsection \<open>Forall Exists\<close>

lemma uspecforall_image:
  assumes "\<And>x y. ((ufclDom\<cdot>x = ufclDom\<cdot>y \<and> ufclRan\<cdot>x = ufclRan\<cdot>y) \<Longrightarrow>
    (ufclDom\<cdot>(f x) = ufclDom\<cdot>(f y) \<and> ufclRan\<cdot>(f x) = ufclRan\<cdot>(f y)))"
  shows "\<And>S. uspecForall (\<lambda>x. uspecExists (\<lambda>y. f y = x) S) (uspecImage f S)"
  apply (simp add: uspecImage_def uspecForall_def uspecExists_def)
  proof - 
    have b0:  "\<And>S. uspecRevSet\<cdot>(Abs_uspec
      (setrevImage f (uspecRevSet\<cdot>S), Discr (ufclDom\<cdot>(f (ufunclLeast (uspecDom\<cdot>S) (uspecRan\<cdot>S)))),
      Discr (ufclRan\<cdot>(f (ufunclLeast (uspecDom\<cdot>S) (uspecRan\<cdot>S)))))) 
      = setrevImage f (uspecRevSet\<cdot>S)"
      by (metis assms uspecImage_def uspecimage_useful_uspecrevset)
    show "\<And>S::'a uspec. setrevForall (\<lambda>x::'b. setrevExists (\<lambda>y::'a. f y = x) (uspecRevSet\<cdot>S))
      (uspecRevSet\<cdot>(Abs_uspec
      (setrevImage f (uspecRevSet\<cdot>S), Discr (ufclDom\<cdot>(f (ufunclLeast (uspecDom\<cdot>S) (uspecRan\<cdot>S)))),
      Discr (ufclRan\<cdot>(f (ufunclLeast (uspecDom\<cdot>S) (uspecRan\<cdot>S)))))))"
      apply (subst b0)
      by (simp add: setrevforall_image)
  qed

subsection \<open>Size\<close>

lemma uspec_least_infinite: assumes "Y \<noteq> {}"
  shows "uspecSize (uspecLeast X Y) = \<infinity>"
  apply (simp add: uspecLeast_def)
  apply (simp add: uspecSize_def)
  apply (simp add: uspecRevSet_def)
  apply (simp add: setrevSize_def inv_rev_rev)
  apply (simp add: setSize_def)
  apply (insert assms)
  oops

end