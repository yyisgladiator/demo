(* Title: TSPF_Comp.thy
   Author: Jens Christoph Bürger
   e-mail: jens.buerger@rwth-aachen.de

   Description: lemmata for composition of TSPFs with the general comp operator
*)

theory TSPF_Comp
  imports TSB TSPF
    
begin
  
(* ----------------------------------------------------------------------- *)
section \<open>definitions\<close>
(* ----------------------------------------------------------------------- *)

  (* true if f1 f2 can be composed parallely *)
definition parcomp_well :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> bool" where
"parcomp_well f1 f2 \<equiv> (tspfCompL f1 f2 = {}) \<and> (tspfRan\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {})"
  
definition sercomp_well :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> bool" where
"sercomp_well f1 f2 \<equiv>  (tspfRan\<cdot>f1 = tspfDom\<cdot>f2) 
                        \<and> (tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f1 = {})
                        \<and> (tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f2 = {})
                        \<and> (tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {})"

subsection \<open>special operators\<close>

definition tspfParComp :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> 'm TSPF"  (infix "\<parallel>" 60) where
"tspfParComp f1 f2 \<equiv> Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = (tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2)) \<leadsto> ((f1 \<rightleftharpoons> (x \<bar> tspfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (x \<bar> tspfDom\<cdot>f2))))"

definition tspfSerComp :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> 'm TSPF"  (infix "\<circ>" 60) where
"tspfSerComp f1 f2 \<equiv> Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = tspfDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"

definition tspfHide :: "'m TSPF \<Rightarrow>  channel set \<Rightarrow> 'm TSPF" (infix "\<h>" 60) where
"tspfHide f cs \<equiv> Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = tspfDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(tspfRan\<cdot>f - cs)))"

definition tspfFeedbackH :: "'m TSPF \<Rightarrow> 'm TSB \<Rightarrow> 'm TSB  \<rightarrow> 'm TSB" where
"tspfFeedbackH f x = (\<Lambda> z. (f\<rightleftharpoons>((x \<uplus> z) \<bar> tspfDom\<cdot>f)))" 

abbreviation iter_tspfFeedbackH :: "'a TSPF \<Rightarrow> nat \<Rightarrow> 'a TSB  \<Rightarrow> 'a TSB" where
"iter_tspfFeedbackH f i \<equiv> (\<lambda> x. iterate i\<cdot>(tspfFeedbackH f x)\<cdot>(tsbLeast (tspfRan\<cdot>f)))"

definition tspfFeedback :: "'m TSPF \<Rightarrow> 'm TSPF" where
"tspfFeedback f \<equiv> 
let I  = tspfDom\<cdot>f - tspfRan\<cdot>f;
    Oc = tspfRan\<cdot>f
in Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = I) \<leadsto> tsbFix (tspfFeedbackH f x) Oc)"


section \<open>tspfHide\<close>


(* should be ported to TSB or TSPF *)
lemma if_then_mono_tspf:  assumes "monofun g"
  shows "monofun (\<lambda>b. (tsbDom\<cdot>b = In)\<leadsto>g b)"
proof(rule monofunI)
  fix x y :: "'a TSB"
  assume "x\<sqsubseteq>y"
  hence "tsbDom\<cdot>x = tsbDom\<cdot>y" using tsbdom_below by blast
  thus "(tsbDom\<cdot>x = In)\<leadsto>g x \<sqsubseteq> (tsbDom\<cdot>y = In)\<leadsto>g y"
  proof -
    have "g x \<sqsubseteq> g y"
      by (meson \<open>x \<sqsubseteq> y\<close> assms monofun_def)
    then show ?thesis
      by (simp add: \<open>tsbDom\<cdot>x = tsbDom\<cdot>y\<close> some_below)
  qed
qed  

(* should be ported to TSB or TSPF *)  
lemma if_then_cont_tspf: assumes "cont g"
  shows "cont (\<lambda>b. (tsbDom\<cdot>b = In)\<leadsto>g b)"
proof(rule contI2)
  show "monofun (\<lambda>b. (tsbDom\<cdot>b = In)\<leadsto>g b)"  using assms cont2mono if_then_mono_tspf by blast
  thus " \<forall>Y. chain Y \<longrightarrow> (tsbDom\<cdot>(\<Squnion>i. Y i) = In)\<leadsto>g (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. (tsbDom\<cdot>(Y i) = In)\<leadsto>g (Y i))"
    using assms if_then_lub2 po_class.chain_def by auto
qed

lemma tspfHide_cont[simp]:  
  shows "cont (\<lambda> x. (tsbDom\<cdot>x = tspfDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(tspfRan\<cdot>f - cs)))"
by(simp add: if_then_cont_tspf cont_compose)

lemma tspfHide_well[simp]: 
  shows "tspf_well(\<Lambda> x. (tsbDom\<cdot>x = tspfDom\<cdot>f ) \<leadsto> ((f \<rightleftharpoons> x)\<bar>(tspfRan\<cdot>f - cs)))"
  apply(simp only: tspf_well_def)
  apply rule
   apply (auto simp add: tspf_type_def domIff2 tsbdom_rep_eq)
    by (metis (no_types, lifting) trans_lnle tsbleast_tsdom tsbtick_tsbres tspf_least_in_dom tspf_less_in_than_out_ticks tspf_sbdomeq_to_domeq)

lemma tspfHide_dom:
  shows "tspfDom\<cdot>(tspfHide f cs) = tspfDom\<cdot>f"
proof - 
  have "\<And> tsb. tsbDom\<cdot>tsb \<noteq> tspfDom\<cdot>f \<Longrightarrow> (Rep_CTSPF (tspfHide f cs) tsb) = None"
    by (simp add: tspfHide_def)
  moreover have "\<And> tsb. tsbDom\<cdot>tsb = tspfDom\<cdot>f \<Longrightarrow> (Rep_CTSPF (tspfHide f cs) tsb) \<noteq> None"
    by (simp add: tspfHide_def)
  ultimately show ?thesis
    by (metis domIff tsbleast_tsdom tspf_least_in_dom)
qed

lemma tspfHide_ran:
  shows "tspfRan\<cdot>(tspfHide f cs) = tspfRan\<cdot>f - cs"
  by (smt Un_Diff_Int inf_commute inf_sup_absorb rep_abs_ctspf tspfran_least tsbleast_tsdom tspfHide_cont tspfHide_def tspfHide_dom tspfHide_well tspf_ran_2_tsbdom tsresrict_dom3)

lemma tspfHide_getCh: assumes "tsbDom\<cdot>tsb = tspfDom\<cdot>f" and "c \<notin> cs"
  shows "((tspfHide f cs) \<rightleftharpoons> tsb) . c = (f \<rightleftharpoons> tsb). c"
  by (smt Diff_iff assms(1) assms(2) domIff option.sel rep_abs_ctspf tsbdom_insert tsbgetch_insert tsbgetch_restrict tspfHide_cont tspfHide_def tspfHide_dom tspfHide_ran tspfHide_well tspf_ran_2_tsbdom2)

(* ----------------------------------------------------------------------- *)
section \<open>parallel-comp\<close>
(* ----------------------------------------------------------------------- *)
  
subsection \<open>channel lemmata\<close>
  
  
lemma parcomp_dom_ran_empty: assumes "tspfCompL f1 f2 = {}"
  shows "(tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2) \<inter> (tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2) = {}"
    using assms tspfCompL_def by fastforce
  
lemma parcomp_dom_i_below: assumes "tspfCompL f1 f2 = {}"
  shows "(tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2) = tspfCompI f1 f2"
  using assms tspfCompI_def tspfCompL_def by fastforce
  
lemma parcomp_cInOc: assumes "tspfCompL f1 f2 = {}"
                    and "c \<in> tspfRan\<cdot>f1"
  shows "c \<in> tspfCompOc f1 f2"
  by (simp add: assms(2) tspfCompOc_def)
                    
lemma parcomp_domranf1: assumes "tspfCompL f1 f2 = {}"
                        and "tsbDom\<cdot>tb = tspfCompI f1 f2"
  shows "(tsbDom\<cdot>(f1\<rightleftharpoons>(tb\<bar>tspfDom\<cdot>f1))) = tspfRan\<cdot>f1"
  proof -
    have "tspfDom\<cdot>f1 \<subseteq> tsbDom\<cdot>tb"
      by (metis (no_types) Un_upper1 assms(1) assms(2) parcomp_dom_i_below)
    then show ?thesis
      by (meson tspf_ran_2_tsbdom2 tsresrict_dom2)
  qed
              

  subsection \<open>iterate\<close> 
    
(* (* helper for the composition *)
definition tspfCompH :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> 'm TSB \<Rightarrow> 'm TSB  \<rightarrow> 'm TSB" where
"tspfCompH f1 f2 x = (\<Lambda> z. (f1\<rightleftharpoons>((x \<uplus> z)  \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>((x \<uplus> z)  \<bar> tspfDom\<cdot>f2)))" 

abbreviation iter_tspfCompH :: "'a TSPF \<Rightarrow> 'a TSPF \<Rightarrow> nat \<Rightarrow> 'a TSB  \<Rightarrow> 'a TSB" where
"iter_tspfCompH f1 f2 i \<equiv> (\<lambda> x. iterate i\<cdot>(tspfCompH f1 f2 x)\<cdot>(tsbLeast (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2)))"

(* general composition operator for TSPFs *)
 (* NOTE: Does not always deliver an TSPF *)
definition tspfComp :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> 'm TSPF" (infixl "\<otimes>" 40) where
"tspfComp f1 f2 \<equiv>
let I = tspfCompI f1 f2;
    Oc = (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2)
in Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = I) \<leadsto> tsbFix (tspfCompH f1 f2 x) Oc)"

*)
  
lemma tspfcomp_parallel_f1: assumes "parcomp_well f1 f2"
                           and "tsbDom\<cdot>x = tspfCompI f1 f2"
                           and "c \<in> tspfRan\<cdot>f1"
  shows "(iter_tspfCompH f1 f2 (Suc (Suc i)) x) . c 
    = ((f1\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f2))) . c"
proof -
  have f0: "(tspfCompL f1 f2 = {}) \<and> (tspfRan\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {})"
    using assms(1) parcomp_well_def by blast
  have f1: "tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2 = tspfCompI f1 f2"
    by (meson f0 parcomp_dom_i_below)
  then have f2: "tsbDom\<cdot>x \<inter> tspfDom\<cdot>f1 = tspfDom\<cdot>f1"
    using assms(2) by blast
  have f3: "x \<uplus> 
    tspfCompH f1 f2 x\<cdot> (iter_tsbfix2 (tspfCompH f1 f2) i (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2) x) \<bar> tsbDom\<cdot>x = x"
    using f1 by (metis f0 assms(2) iter_tspfcomph_dom iterate_Suc parcomp_dom_ran_empty 
                 tsbunion_restrict3)
  have "tsbDom\<cdot>x \<inter> tspfDom\<cdot>f2 = tspfDom\<cdot>f2"
    using f1 assms(2) by blast
  hence "(f1\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f2)) = 
        tspfCompH f1 f2 x\<cdot> (iter_tsbfix2 (tspfCompH f1 f2) (Suc i) (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2) x)"
    using f3 f2 by (metis (no_types) iterate_Suc tsbrestrict_test tspfcomph_insert)
  thus ?thesis
    by simp
qed

  
lemma tspfcomp_parallel_f2: assumes "parcomp_well f1 f2"
                           and "tsbDom\<cdot>x = tspfCompI f1 f2"
                           and "c \<in> tspfRan\<cdot>f2"
  shows "(iter_tspfCompH f1 f2 (Suc (Suc i)) x) . c 
    = ((f1\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f2))) . c"
  by (smt Un_upper1 assms(1) assms(2) inf.orderE inf_commute iter_tspfcomph_dom iterate_Suc 
          parcomp_dom_i_below sup.cobounded2 tsbrestrict_test tsbunion_restrict3 tspfCompL_def 
          tspfcomph_insert parcomp_well_def)

lemma tspfcomp_iter_parallel: assumes "parcomp_well f1 f2"
                         and "tsbDom\<cdot>x = tspfCompI f1 f2"
  shows "(iter_tspfCompH f1 f2 (Suc (Suc i)) x) = ((f1\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f2)))"
  (* ISAR Proof generateable by sledgehammer *)
  by (smt assms(1) assms(2) inf.orderE inf_bot_right inf_sup_absorb inf_sup_aci(3) 
          iter_tspfcomph_dom iterate_Suc parcomp_dom_ran_empty sup.cobounded2 tsbunion_restrict 
          tspfcomph_insert parcomp_well_def)
  
lemma tspfcomp_parallel_max_chain: assumes "parcomp_well f1 f2"
                                   and "tsbDom\<cdot>x = tspfCompI f1 f2"
  shows "max_in_chain (Suc (Suc 0)) (\<lambda> i. iter_tspfCompH f1 f2 i x)"           
proof -
  have f1: "\<And>j. Suc (Suc 0) \<le> j \<Longrightarrow> (f1\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f2)) 
                                    = iter_tsbfix2 (tspfCompH f1 f2) j (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2) x"
    proof -
      fix j :: nat
      assume a1: "Suc (Suc 0) \<le> j"
      obtain nn :: "nat \<Rightarrow> nat" where
          f2: "\<And>n na. \<not> Suc n \<le> na \<or> Suc (nn na) = na"
        by (metis (no_types) Suc_le_D)
      hence f3: "Suc (nn j) = j"
        using a1 by metis
      have "\<And>n. j \<le> Suc n \<or> Suc (nn (nn j)) = nn j"
        using f2 by (metis not_less_eq_eq)
      thus "(f1\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f2)) 
                    = iter_tsbfix2 (tspfCompH f1 f2) j (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2) x"
        using f3 a1 by (metis assms(1) assms(2) not_less_eq_eq tspfcomp_iter_parallel)
    qed
  show ?thesis  
    apply (rule max_in_chainI)
    by (subst tspfcomp_iter_parallel, simp_all add: assms f1) 
qed
  
  subsection \<open>lub iterate\<close>
  
lemma tspfcomp_parallel_lub_const1 [simp]: assumes "parcomp_well f1 f2"
                                           and "tsbDom\<cdot>x = tspfCompI f1 f2"
  shows "(\<Squnion> i. iter_tspfCompH f1 f2 i x) = ((f1\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f2)))"
proof -
  have "(\<Squnion> i. iter_tspfCompH f1 f2 i x) = iter_tspfCompH f1 f2 (Suc (Suc 0)) x"
    using assms(1) assms(2) maxinch_is_thelub tspfcomp_parallel_max_chain 
          iter_tspfcomph_chain  by blast
  thus ?thesis
    by (metis assms(1) assms(2) tspfcomp_iter_parallel)
qed
  
  subsection \<open>fun lub iterate\<close>

lemma tspfcomp_parallel_iterconst_eq1:  assumes "parcomp_well f1 f2"
shows "(\<lambda> x. (tsbDom\<cdot>x = tspfCompI f1 f2) \<leadsto> (\<Squnion>i. iter_tspfCompH f1 f2 i x))
            = (\<lambda> x. (tsbDom\<cdot>x = (tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2)) 
                        \<leadsto> ((f1\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f2))))" 
proof -
  have f0: "(tspfCompL f1 f2 = {}) \<and> (tspfRan\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {})"
  using assms(1) parcomp_well_def by blast
  have f1: "(tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2) = tspfCompI f1 f2"
    by (simp add: f0 parcomp_dom_i_below )
  have "\<forall> s.  tsbDom\<cdot>s \<noteq> tspfCompI f1 f2 \<or>
              Some ((\<Squnion>i. iter_tspfCompH f1 f2 i s)) 
                = Some (((f1\<rightleftharpoons>(s \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>(s \<bar> tspfDom\<cdot>f2))))"
    by (metis assms tspfcomp_parallel_lub_const1)
  thus ?thesis
    apply (subst f1)
    by meson
qed
  
lemma parallel_iterconst_cont [simp]: "cont (\<lambda> x. (tsbDom\<cdot>x = (tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2)) 
                        \<leadsto> ((f1\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f2))))"
proof -
  have "cont (\<lambda> s. (Rep_cfun (Rep_TSPF f1))\<rightharpoonup>(s\<bar>tspfDom\<cdot>f1))" 
    using cont_Rep_cfun2 cont_compose by force
  moreover have "cont (\<lambda> s. (Rep_cfun (Rep_TSPF f2))\<rightharpoonup>(s\<bar>tspfDom\<cdot>f2))"
    using cont_Rep_cfun2 cont_compose by force
  ultimately have "cont (\<lambda> s. ((Rep_cfun (Rep_TSPF f1))\<rightharpoonup>(s\<bar>tspfDom\<cdot>f1)) \<uplus> ((Rep_cfun (Rep_TSPF f2))\<rightharpoonup>(s\<bar>tspfDom\<cdot>f2)))"
    using cont2cont_APP cont_Rep_cfun2 cont_compose by blast
  hence "cont (\<lambda> s. (f1\<rightleftharpoons>(s \<bar> tspfDom\<cdot>f1)) \<uplus> (f2\<rightleftharpoons>(s \<bar> tspfDom\<cdot>f2)))"
    by (simp add: )  
  thus ?thesis
    by(simp add: if_then_cont_tspf)
qed
    
(* \<And>b. tsbDom\<cdot>b = tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2 \<Longrightarrow> #\<surd>tsb b  \<le> #\<surd>tsb f1\<rightleftharpoons>b \<bar> tspfDom\<cdot>f1 \<uplus> f2\<rightleftharpoons>b \<bar> tspfDom\<cdot>f2  *)

lemma parallel_tick_well: assumes "parcomp_well f1 f2" and "tsbDom\<cdot>b = tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2"
  shows "(#\<surd>tsb b)  \<le> #\<surd>tsb ((f1\<rightleftharpoons>(b \<bar> (tspfDom\<cdot>f1))) \<uplus> (f2\<rightleftharpoons>(b \<bar> (tspfDom\<cdot>f2))))"
    (* ISAR training proof: requires tsbtick_tsbunion as well as case distinction *)
  by (smt Un_upper1 assms(1) assms(2) inf_commute le_cases3 sup.cobounded2 trans_lnle 
            tsbleast_tsdom tsbrestrict_test tsbtick_tsbres tsbtick_tsbunion2 tsbunion_commutative
             tsbunion_idR tsbunion_restrict3 tspf_least_in_dom tspf_less_in_than_out_ticks 
             tspf_ran_2_tsbdom2 tspf_sbdomeq_to_domeq tsresrict_dom2 parcomp_well_def)
    
    
lemma parallel_iterconst_well [simp]: assumes "parcomp_well f1 f2"
  shows "tspf_well (Abs_cfun (\<lambda> x. (tsbDom\<cdot>x = (tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2)) 
                        \<leadsto> ((f1\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f2)))))"
  apply (subst tspf_well_def)
  apply rule
  apply (auto simp add: tspf_type_def domIff2 tsbdom_rep_eq tspfCompI_def assms)
   apply (metis (no_types, hide_lams) inf_commute inf_sup_absorb sup_commute 
                                      tspf_ran_2_tsbdom2 tsresrict_dom3)
  by (meson assms parallel_tick_well)

 
(* results *)
    
 (* the general composition operator is capable of the parallel composition :) *)
lemma tspfcomp_parallel: assumes "parcomp_well f1 f2"
  shows "(tspfComp f1 f2) \<rightleftharpoons> sb = 
        (Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = (tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2)) 
                        \<leadsto> ((f1\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f2))))) \<rightleftharpoons> sb"
  apply (simp only: tspfcomp2_iterCompH)
    by (simp add: assms(1) tspfcomp_parallel_iterconst_eq1)

      
lemma tspfcomp_parallel_getch1: assumes "parcomp_well f1 f2"
                                and "tsbDom\<cdot>sb = tspfCompI f1 f2"
                                and "c \<in> tspfRan\<cdot>f1"
  shows "((tspfComp f1 f2) \<rightleftharpoons> sb) . c = (f1\<rightleftharpoons>(sb \<bar> tspfDom\<cdot>f1)) . c"
proof -
  have f0: "(tspfCompL f1 f2 = {}) \<and> (tspfRan\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {})"
    using assms(1) parcomp_well_def by blast     
  show ?thesis
    apply (simp only: tspfcomp_parallel assms)
    apply (simp add: assms)
    apply (subst (1 2) parcomp_dom_i_below, simp_all add: assms f0)
    apply (rule tsbunion_getchL)
    by (metis (no_types) IntI f0 assms(2) assms(3) empty_iff parcomp_domranf1 
                  tspfcomp_I_commu tspfcomp_L_commu )
qed
  
    
lemma tspfcomp_parallel_getch2: assumes "parcomp_well f1 f2"
                                and "tsbDom\<cdot>sb = tspfCompI f1 f2"
                                and "c \<in> tspfRan\<cdot>f2"
  shows "((tspfComp f1 f2) \<rightleftharpoons> sb) . c = (f2\<rightleftharpoons>(sb \<bar> tspfDom\<cdot>f2)) . c"
proof -
  have f0: "(tspfCompL f1 f2 = {}) \<and> (tspfRan\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {})"
    using assms(1) parcomp_well_def by blast  
      
  show ?thesis
    apply (simp only: tspfcomp_parallel assms)
    apply (simp add: assms)
    apply (subst (1 2) parcomp_dom_i_below, simp_all add: assms f0)
    apply (rule tsbunion_getchR)
    by (metis f0 assms(2) assms(3) parcomp_domranf1 tspfcomp_I_commu tspfcomp_L_commu)
qed
  

    
  subsection \<open>special parallel operator\<close>

lemma tspfParComp_dom: assumes "parcomp_well f1 f2"
  shows "tspfDom\<cdot>(tspfParComp f1 f2) = tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2"
proof -
  have f1: "Rep_CTSPF (f1\<parallel>f2) (tsbLeast (tspfDom\<cdot>(f1\<parallel>f2))) \<noteq> None"
    by (metis (full_types) domIff tspf_least_in_dom)
  have "(\<lambda>t. (tsbDom\<cdot>t = tspfDom\<cdot>f1 \<union> tspfDom\<cdot> f2)\<leadsto>(f1 \<rightleftharpoons> t \<bar> tspfDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> t \<bar> tspfDom\<cdot>f2)) = Rep_CTSPF (f1\<parallel>f2)"
    by (simp add: assms tspfParComp_def)
  then have "(tsbDom\<cdot>(tsbLeast (tspfDom\<cdot>(f1\<parallel>f2))::'a TSB) = tspfDom\<cdot>f1 \<union> tspfDom\<cdot> f2)\<leadsto>(f1 \<rightleftharpoons> tsbLeast (tspfDom\<cdot>(f1\<parallel>f2)) \<bar> tspfDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> tsbLeast (tspfDom\<cdot>(f1\<parallel>f2)) \<bar> tspfDom\<cdot>f2) \<noteq> None"
    by (smt f1)
  then show ?thesis
    by (metis tsbleast_tsdom)
qed

lemma tspfParComp_ran: assumes "parcomp_well f1 f2"
  shows "tspfRan\<cdot>(tspfParComp f1 f2) = tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2"
  by (smt assms option.sel parcomp_well_def parallel_iterconst_cont parallel_iterconst_well parcomp_dom_i_below parcomp_domranf1 rep_abs_ctspf tspfran_least tsbleast_tsdom tsbunion_dom tspfParComp_def tspfParComp_dom tspfcomp_I_commu tspfcomp_L_commu)
  
lemma tspfParComp_getCh: assumes "parcomp_well f1 f2"  
                             and "tsbDom\<cdot>sb = tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2"
                             and "c \<in> tspfRan\<cdot>f1"
  shows "((tspfParComp f1 f2) \<rightleftharpoons> sb) . c = (f1\<rightleftharpoons>(sb \<bar> tspfDom\<cdot>f1)) . c"                             
  apply(simp add: tspfParComp_def)
  apply(simp add: assms)
  by (metis (no_types, lifting) assms(1) assms(2) assms(3) parcomp_well_def disjoint_iff_not_equal inf_sup_ord(4) tsbunion_getchL tspf_ran_2_tsbdom2 tsresrict_dom2)

lemma tspfParComp_getCh2: assumes "parcomp_well f1 f2"  
                             and "tsbDom\<cdot>sb = tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2"
                             and "c \<in> tspfRan\<cdot>f2"
  shows "((tspfParComp f1 f2) \<rightleftharpoons> sb) . c = (f2\<rightleftharpoons>(sb \<bar> tspfDom\<cdot>f2)) . c"                             
  apply(simp add: tspfParComp_def)
  apply(simp add: assms)
  by (metis (no_types, lifting) assms(2) assms(3) inf_sup_ord(4) tsbunion_getchR tspf_ran_2_tsbdom2 tsresrict_dom2)

lemma tspfParComp_eq: assumes "parcomp_well f1 f2"
  shows "tspfComp f1 f2 = tspfParComp f1 f2"
  by (simp add: assms tspfParComp_def tspfcomp2_lubiter tspfcomp_parallel_iterconst_eq1)
    
    
(* ----------------------------------------------------------------------- *)
section \<open>serial-comp\<close>
(* ----------------------------------------------------------------------- *)
  
subsection \<open>channel lemmata\<close>    
    
  (* for legacy purposes *)
lemma sercomp_well2comp_well: assumes "sercomp_well f1 f2"
  shows "tspfRan\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {}"
    using assms sercomp_well_def by blast
 
  (* for legacy purposes *)
lemma sercomp_well2no_selfloops: assumes "sercomp_well f1 f2"
  shows "tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f1 = {}
                    \<and> tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f2 = {}"
  using assms sercomp_well_def by blast

  (* for legacy purposes *)
lemma sercomp_well2_pL: assumes "sercomp_well f1 f2"
  shows "((tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f1) \<union> (tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2) \<union> (tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f2)) = {}"
  using assms sercomp_well_def by blast

    
lemma sercomp_input_ch: assumes "sercomp_well f1 f2"
  shows "tspfDom\<cdot>f1 = (tspfCompI f1 f2)"
  by (smt Diff_Diff_Int Diff_Un Un_Diff Un_Diff_Int assms sup_bot.right_neutral tspfCompI_def 
          sercomp_well_def)
    
lemma sercomp_dom_f1: assumes "sercomp_well f1 f2"
                      and "tsbDom\<cdot>tb = tspfCompI f1 f2"
  shows "tsbDom\<cdot>(f1\<rightleftharpoons>(tb\<bar>(tspfDom\<cdot>f1))) = tspfRan\<cdot>f1"
proof -
  have "tspfDom\<cdot>f1 = tspfCompI f1 f2"
    by (meson assms(1) sercomp_input_ch)
  then show ?thesis
    by (simp add: assms(2))
qed
 
lemma sercomp_dom_f12: assumes "sercomp_well f1 f2"
  shows "tspfDom\<cdot>f1 \<inter> (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2) = {}"
  using assms sercomp_well_def by blast

lemma sercomp_dom_input: assumes "sercomp_well f1 f2"
  shows "tspfCompI f1 f2 = tspfDom\<cdot>f1"
  using assms sercomp_input_ch by blast
    
  
  subsection \<open>iterate\<close>    
        
lemma sercomp_iter_serial_res_f1: assumes "sercomp_well f1 f2"
                                  and "tsbDom\<cdot>x = tspfCompI f1 f2"
  shows "(iter_tspfCompH f1 f2 (Suc (Suc i)) x) \<bar> (tspfRan\<cdot>f1) = (f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1))"
  by (smt assms(1) assms(2) inf_sup_absorb inf_sup_aci(1) iter_tspfcomph_dom iterate_Suc 
          sercomp_dom_f1 sercomp_dom_f12 tsbrestrict_test tsbunion_restrict tsbunion_restrict2 
          tsbunion_restrict3 tspf_ran_2_tsbdom2 tspfcomph_insert tsresrict_dom3 sercomp_well_def)
                                  

lemma sercomp_iter_serial: assumes "sercomp_well f1 f2"
                              and "tsbDom\<cdot>x = tspfCompI f1 f2"
  shows "(iter_tspfCompH f1 f2 (Suc (Suc (Suc i))) x) = 
    (f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)))"
  by (smt assms(1) assms(2) inf_commute iter_tspfcomph_dom iterate_Suc sercomp_dom_f12 
          sercomp_input_ch sercomp_iter_serial_res_f1 tsbunion_commutative tsbunion_restrict 
          tspfcomph_insert sercomp_well_def)
 
lemma sercomp_iter_max_in_chain: assumes "sercomp_well f1 f2"
                                 and "tsbDom\<cdot>x = tspfCompI f1 f2"
  shows "max_in_chain (Suc (Suc (Suc 0))) (\<lambda>i. iter_tspfCompH f1 f2 i x)"
proof (rule max_in_chainI)
  fix j
  assume a1: "Suc (Suc (Suc 0)) \<le> j"
  have f1: "tspfDom\<cdot>f1 \<inter> tspfDom\<cdot>f2 = {}"
    using assms(1) sercomp_well_def  by blast
  obtain k where o1: "j = Suc (Suc (Suc k))"
    by (metis (no_types) Suc_leD Suc_n_not_le_n a1 not0_implies_Suc)  
  show "iter_tsbfix2 (tspfCompH f1 f2) (Suc (Suc (Suc 0))) (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2) x =
         iter_tsbfix2 (tspfCompH f1 f2) j (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2) x "
    apply (subst o1)
    by (metis assms(1) assms(2) sercomp_iter_serial)
qed
  

  
  subsection \<open>lub iterate\<close> 
      
lemma tspfcomp_sercomp_lub_const1: assumes "sercomp_well f1 f2"
                                   and "tsbDom\<cdot>x = tspfCompI f1 f2"
  shows "(\<Squnion>i. iter_tspfCompH f1 f2 i x) = iter_tspfCompH f1 f2 (Suc (Suc (Suc 0))) x"    
  using assms maxinch_is_thelub sercomp_iter_max_in_chain iter_tspfcomph_chain by blast
      
lemma tspfcomp_sercomp_lub_const2: assumes "sercomp_well f1 f2"
                                   and "tsbDom\<cdot>x = tspfCompI f1 f2"
  shows "(\<Squnion>i. iter_tspfCompH f1 f2 i x) = (f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)))"
  by (metis assms(1) assms(2) sercomp_iter_serial tspfcomp_sercomp_lub_const1)   
      

    

  subsection \<open>fun lub iterate\<close> 
      
lemma tspfcomp_serial_iterconst_eq: assumes "sercomp_well f1 f2"
  shows "(\<lambda> x. (tsbDom\<cdot>x = tspfCompI f1 f2) \<leadsto> (\<Squnion>i. iter_tspfCompH f1 f2 i x) )
        = (\<lambda> x. (tsbDom\<cdot>x = tspfDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)))))"
proof -
  have f1: "(tspfDom\<cdot>f1) = tspfCompI f1 f2"
    using assms sercomp_input_ch by auto
  
  have  "\<forall>x. (tsbDom\<cdot>x \<noteq> tspfCompI f1 f2)  \<or> 
        (Some ((\<Squnion>i. iter_tspfCompH f1 f2 i x))
        = Some ((f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)))))"
      by (metis assms tspfcomp_sercomp_lub_const2)
  thus ?thesis
    apply (subst f1)
    by meson  
qed
  
lemma tspfcomp_serial_iterconst_cont [simp]: 
  "cont (\<lambda> x. (tsbDom\<cdot>x = tspfDom\<cdot>f1) \<leadsto> ((f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)))))"
proof - 
  have "cont (\<lambda> x. (f2 \<rightleftharpoons> x))"
      by (simp add: cont_compose)
  moreover have f1: "cont (\<lambda> x. (f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)))"
    by (metis  cont_Rep_cfun2 cont_compose op_the_cont tspfDom_def tspf_dom_insert)
  ultimately have f2: "cont (\<lambda> x. (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1))))"
    using cont_compose by blast
  with f1 f2 have "cont (\<lambda> x. ((f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)))))"
    using cont2cont_APP cont_Rep_cfun2 cont_compose by blast
  thus ?thesis
    by(simp add: if_then_cont_tspf)
qed    
 
(*  \<And>b. tsbDom\<cdot>b = tspfDom\<cdot>f1 \<Longrightarrow> #\<surd>tsb b  \<le> #\<surd>tsb (f1 \<rightleftharpoons> b \<bar> tspfDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> b \<bar> tspfDom\<cdot>f1))  *)
  
lemma serial_tick_well: assumes "sercomp_well f1 f2" and "tsbDom\<cdot>b = tspfDom\<cdot>f1"
  shows "(#\<surd>tsb b)  \<le> #\<surd>tsb ((f1 \<rightleftharpoons> b \<bar> tspfDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> b \<bar> tspfDom\<cdot>f1)))"
proof -
  have f0: "(tspfRan\<cdot>f1 = tspfDom\<cdot>f2) \<and> (tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f1 = {}) \<and> (tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f2 = {})
        \<and> (tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {})"
    using assms(1) sercomp_well_def by blast
  
  thus ?thesis
    apply (subst tsbtick_tsbunion)
       apply (simp add: assms(1) assms(2))
       apply (simp add: f0 assms(2)) 
       by (smt f0 assms(1) assms(2) inf.idem le_cases3 min.mono min_def tsbleast_tsdom 
                tsbtick_tsbres tspf_least_in_dom tspf_less_in_than_out_ticks 
                tspf_ran_2_tsbdom2 tspf_sbdomeq_to_domeq tsresrict_dom3)
qed
   
  
  
lemma tspfcomp_serial_iterconst_well [simp]: assumes "sercomp_well f1 f2"
  shows "tspf_well (Abs_cfun (\<lambda> x. (tsbDom\<cdot>x = tspfDom\<cdot>f1) \<leadsto> 
                    ((f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1))))) )"
proof -
  have f0: "(tspfRan\<cdot>f1 = tspfDom\<cdot>f2) \<and> (tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f1 = {}) \<and> (tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f2 = {})
        \<and> (tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {})"
    using assms(1) sercomp_well_def by blast
  thus ?thesis
    apply (subst tspf_well_def)
    apply rule
    apply (auto simp add: tspf_type_def domIff2 tsbdom_rep_eq tspfCompI_def assms)
    by (meson assms serial_tick_well )
qed
    
  subsection \<open>result\<close>     
    
lemma tspfcomp_serial: assumes "sercomp_well f1 f2"
  shows "(tspfComp f1 f2) \<rightleftharpoons> sb = 
        Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = tspfDom\<cdot>f1) \<leadsto> 
                    ((f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1)) \<uplus> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (x\<bar>tspfDom\<cdot>f1))))) \<rightleftharpoons> sb"
    apply (simp only: tspfcomp2_iterCompH)
    apply (subst tspfcomp_serial_iterconst_eq)
      using assms apply blast
      by (simp)
   
    
  subsection \<open> special serial operator\<close>

lemma tspfSerComp_cont [simp]: 
  "cont (\<lambda> x. (tsbDom\<cdot>x = tspfDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
proof - 
  have "cont (\<lambda> x. (f1 \<rightleftharpoons> x))"
    by (simp add: cont_compose)
  moreover have "cont (\<lambda> x. (f2 \<rightleftharpoons> x))"
    by (simp add: cont_compose)
  ultimately show ?thesis
    using cont_compose if_then_cont_tspf by blast
qed  

lemma tspfSerComp_tick_well: assumes "sercomp_well f1 f2" and "tsbDom\<cdot>b = tspfDom\<cdot>f1"
  shows "(#\<surd>tsb b)  \<le> #\<surd>tsb (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> b))"
  by (smt assms(1) assms(2) sercomp_well_def inf_sup_ord(1) le_cases3 min.absorb_iff1 serial_tick_well trans_lnle tsbtick_tsbunion tsbtick_tsbunion2 tsbunion_commutative tsbunion_idL tsbunion_restrict2 tspf_ran_2_tsbdom2 tsresrict_dom3)
  
lemma tspfSerComp_well [simp]: assumes "sercomp_well f1 f2"
  shows "tspf_well (Abs_cfun (\<lambda> x. (tsbDom\<cdot>x = tspfDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x))))"
proof -
  have f0: "(tspfRan\<cdot>f1 = tspfDom\<cdot>f2) \<and> (tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f1 = {}) \<and> (tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f2 = {})
        \<and> (tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {})"
    using assms(1) sercomp_well_def by blast
  show ?thesis
    apply (subst tspf_well_def)
    apply rule
     apply (auto simp add: tspf_type_def domIff2 tsbdom_rep_eq tspfCompI_def assms)
     apply (metis assms sercomp_well_def tspf_ran_2_tsbdom2)
      by (simp add: assms tspfSerComp_tick_well)
qed
  
    
lemma tspfSerComp_dom: assumes "sercomp_well f1 f2"
  shows "tspfDom\<cdot>(tspfSerComp f1 f2) = tspfDom\<cdot>f1"
  by (smt assms domIff rep_abs_ctspf tsbleast_tsdom tspfSerComp_cont tspfSerComp_def tspfSerComp_well tspf_least_in_dom)

lemma tspfSerComp_ran: assumes "sercomp_well f1 f2"
  shows "tspfRan\<cdot>(tspfSerComp f1 f2) = tspfRan\<cdot>f2"
  by (smt assms sercomp_well_def option.sel rep_abs_ctspf tspfran_least tsbleast_tsdom tspfSerComp_cont tspfSerComp_def tspfSerComp_dom tspfSerComp_well tspf_ran_2_tsbdom2)

lemma tspfSerComp_repAbs: assumes "sercomp_well f1 f2"
  shows "Rep_CTSPF (tspfSerComp f1 f2) = (\<lambda> x. (tsbDom\<cdot>x = tspfDom\<cdot>f1) \<leadsto> (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> x)))"
  apply(subst tspfSerComp_def)
  apply(subst rep_abs_tspf, subst tspfSerComp_well)
  apply(simp_all)
  using assms by blast
    
lemma tspfSerComp_getCh: assumes "sercomp_well f1 f2"  
                             and "tsbDom\<cdot>sb = tspfDom\<cdot>f1"
                             and "c \<in> tspfRan\<cdot>f2"
  shows "((tspfSerComp f1 f2) \<rightleftharpoons> sb) . c = (f2 \<rightleftharpoons> (f1 \<rightleftharpoons> (sb))) . c"                             
  apply(subst tspfSerComp_repAbs)
  using assms apply blast
  by(simp add: assms)

lemma tspfSerComp_eq: assumes "sercomp_well f1 f2"
  shows "(tspfHide (tspfComp f1 f2) (tspfRan\<cdot>f1)) \<rightleftharpoons> tsb = (tspfSerComp f1 f2) \<rightleftharpoons> tsb"
proof(cases "tsbDom\<cdot>tsb = tspfDom\<cdot>(tspfSerComp f1 f2)")
  case True
  have f0: "(tspfRan\<cdot>f1 = tspfDom\<cdot>f2) \<and> (tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f1 = {}) \<and> (tspfDom\<cdot>f2 \<inter> tspfRan\<cdot>f2 = {})
      \<and> (tspfDom\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {})"
    using assms(1) sercomp_well_def by blast
  have f11: "tspfRan\<cdot>(f1 \<otimes> f2) = tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2"
    (* by (smt Diff_triv True assms domIff f0 inf_bot_right inf_commute inf_sup_ord(1) option.collapse option.sel rep_abs_ctspf sercomp_dom_f1 sercomp_input_ch tsbleast_tsdom tsbunion_commutative tsbunion_dom tsbunion_idL tsbunion_restrict3 tspfSerComp_dom tspfSerComp_ran tspfSerComp_repAbs tspf_least_in_dom tspf_sbdomeq_to_domeq tspfcomp2_lubiter tspfcomp_commu tspfcomp_serial_iterconst_cont tspfcomp_serial_iterconst_eq tspfcomp_serial_iterconst_well tspfran_least tsresrict_dom3)
    prover timeout *)
    sorry
  have f1: "tspfRan\<cdot>(tspfHide (tspfComp f1 f2) (tspfRan\<cdot>f1)) = tspfRan\<cdot>(tspfSerComp f1 f2)"
    apply(simp add: tspfHide_ran)
    apply(subst tspfSerComp_ran)
    using assms apply blast
    by (simp add: Diff_triv Un_Diff f0 f11 inf_commute)
  then show ?thesis 
    apply(subst tsb_eq, simp_all)
    apply (smt True Diff_Un Diff_disjoint Int_Un_distrib2 Un_Diff_Int assms domIff inf_bot_right inf_commute option.sel rep_abs_ctspf sup_bot.right_neutral tsbleast_tsdom tsbunion_dom tspfHide_dom tspfHide_ran tspfSerComp_dom tspfSerComp_ran tspf_least_in_dom tspf_ran_2_tsbdom2 tspfcomp2_lubiter tspfcomp_serial_iterconst_cont tspfcomp_serial_iterconst_eq tspfcomp_serial_iterconst_well tsresrict_dom3)
    by (smt f0 Diff_iff True assms domIff inf.idem inf_commute option.sel rep_abs_ctspf tsbleast_tsdom tsbrestrict_test tsbunion_getchR tsbunion_restrict3 tspfHide_dom tspfHide_getCh tspfHide_ran tspfSerComp_repAbs tspf_least_in_dom tspf_ran_2_tsbdom2 tspfcomp2_lubiter tspfcomp_serial_iterconst_cont tspfcomp_serial_iterconst_eq tspfcomp_serial_iterconst_well)  
next
  case False
  then show ?thesis
    by (smt assms domIff option.collapse rep_abs_ctspf tspfHide_dom tspfSerComp_dom tspf_dom_2tsbdom tspf_least_in_dom tspfcomp2_lubiter tspfcomp_serial_iterconst_cont tspfcomp_serial_iterconst_eq tspfcomp_serial_iterconst_well)    
qed


section \<open>Feedback\<close>  
  
  
lemma tspfFeedbackH_cont[simp]: "cont (\<lambda> z. (f\<rightleftharpoons>((x \<uplus> z) \<bar> tspfDom\<cdot>f)))"
proof - 
  have "cont (\<lambda> z. x \<uplus> z)"
    by simp
  then have "cont (\<lambda> z. ((x \<uplus> z) \<bar> tspfDom\<cdot>f))"
    using cont_Rep_cfun2 cont_compose by blast
  moreover have "cont (\<lambda> z. f\<rightleftharpoons>z)"
    by (simp add: cont_compose)
  ultimately show ?thesis
    using cont_compose by blast
qed

lemma tspfFeedbackH_cont2[simp]: "cont (\<lambda> x. (f\<rightleftharpoons>((x \<uplus> z) \<bar> tspfDom\<cdot>f)))"
proof - 
  have "cont (\<lambda> x. x \<uplus> z)"
    by simp
  then have "cont (\<lambda> x. ((x \<uplus> z) \<bar> tspfDom\<cdot>f))"
    using cont_Rep_cfun2 cont_compose by blast
  moreover then have "cont (\<lambda> x. f\<rightleftharpoons>x)"
    by (simp add: cont_compose)
  ultimately show ?thesis
    using cont_compose by blast
qed  
  
lemma tspfcomph_cont_x[simp]: "cont (\<lambda> x. tspfFeedbackH f x)"
  apply (subst tspfFeedbackH_def)
  by (simp only: cont2cont_LAM tspfFeedbackH_cont tspfFeedbackH_cont2)  
  
lemma tspfFeedbackH_dom: assumes "tsbDom\<cdot>x = tspfDom\<cdot>f - tspfRan\<cdot>f" 
                              and "tsbDom\<cdot>tb = tspfRan\<cdot>f"  
  shows "tsbDom\<cdot>(tspfFeedbackH f x\<cdot>tb) = tspfRan\<cdot>f"
proof - 
  have "tsbDom\<cdot>((x \<uplus> tb) \<bar> tspfDom\<cdot>f) = tspfDom\<cdot>f"
    apply(simp add: assms)
    by auto
  then show ?thesis
    by(simp add: tspfFeedbackH_def)
qed 

lemma iter_tspfFeedbackH_chain [simp]: assumes "tsbDom\<cdot>x = tspfDom\<cdot>f - tspfRan\<cdot>f"
  shows "chain (\<lambda> i. iter_tspfFeedbackH f i x)"
  by (simp add: assms tsbIterate_chain tspfFeedbackH_dom)    
    
lemma iter_tspfFeedbackH_dom [simp]: assumes "tsbDom\<cdot>x = tspfDom\<cdot>f - tspfRan\<cdot>f"
  shows "tsbDom\<cdot>(iter_tspfFeedbackH f i x) = tspfRan\<cdot>f"
  by (simp add: assms iter_tsbfix2_dom tspfFeedbackH_dom)

lemma lub_iter_tspfFeedbackH_dom [simp]: assumes "tsbDom\<cdot>x = tspfDom\<cdot>f - tspfRan\<cdot>f"
  shows "tsbDom\<cdot>(\<Squnion> i. iter_tspfFeedbackH f i x) = tspfRan\<cdot>f"
  by (simp add: assms lub_iter_tsbfix2_dom tspfFeedbackH_dom)
  
lemma tspfFeedback_cont[simp]: "cont (\<lambda> x. (tsbDom\<cdot>x = tspfDom\<cdot>f - tspfRan\<cdot>f) \<leadsto> tsbFix (tspfFeedbackH f x) (tspfRan\<cdot>f))" 
  apply(subst (1) tsbfix_contI2)
   apply(simp_all)
   by (simp add: tspfFeedbackH_dom)
  
lemma tspfFeedback_tspfwell:  
  assumes "\<And>b. tsbDom\<cdot>b = (tspfDom\<cdot>f - tspfRan\<cdot>f) \<Longrightarrow> #\<surd>tsb b  \<le> #\<surd>tsb tsbFix (tspfFeedbackH f b) (tspfRan\<cdot>f)"
  shows "tspf_well (\<Lambda> x. (tsbDom\<cdot>x = tspfDom\<cdot>f - tspfRan\<cdot>f) \<leadsto> tsbFix (tspfFeedbackH f x) (tspfRan\<cdot>f))" 
  apply(simp add: tspf_well_def)
  apply rule
   apply(auto simp add: tspf_type_def domIff2 tsbdom_rep_eq)
   apply(simp add: tsbFix_def)
   apply auto[1]
   by(simp add: assms)
 
end
  