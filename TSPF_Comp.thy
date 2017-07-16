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
abbreviation parcomp_well :: "'m TSPF \<Rightarrow> 'm TSPF \<Rightarrow> bool" where
"parcomp_well f1 f2 \<equiv> (tspfCompL f1 f2 = {}) \<and> (tspfRan\<cdot>f1 \<inter> tspfRan\<cdot>f2 = {})"
  
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
  shows "(tsbDom\<cdot>f1\<rightleftharpoons>(tb\<bar>tspfDom\<cdot>f1)) = tspfRan\<cdot>f1"
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
  have f1: "tspfDom\<cdot>f1 \<union> tspfDom\<cdot>f2 = tspfCompI f1 f2"
    by (meson assms(1) parcomp_dom_i_below)
  then have f2: "tsbDom\<cdot>x \<inter> tspfDom\<cdot>f1 = tspfDom\<cdot>f1"
    using assms(2) by blast
  have f3: "x \<uplus> 
    tspfCompH f1 f2 x\<cdot> (iter_tsbfix2 (tspfCompH f1 f2) i (tspfRan\<cdot>f1 \<union> tspfRan\<cdot>f2) x) \<bar> tsbDom\<cdot>x = x"
    using f1 by (metis assms(1) assms(2) iter_tspfcomph_dom iterate_Suc parcomp_dom_ran_empty 
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
          tspfcomph_insert)

lemma tspfcomp_parallel: assumes "parcomp_well f1 f2"
                         and "tsbDom\<cdot>x = tspfCompI f1 f2"
  shows "(iter_tspfCompH f1 f2 (Suc (Suc i)) x) = ((f1\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f2)))"
  (* ISAR Proof generateable by sledgehammer *)
  by (smt assms(1) assms(2) inf.orderE inf_bot_right inf_sup_absorb inf_sup_aci(3) 
          iter_tspfcomph_dom iterate_Suc parcomp_dom_ran_empty sup.cobounded2 tsbunion_restrict 
          tspfcomph_insert)
  
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
        using f3 a1 by (metis assms(1) assms(2) not_less_eq_eq tspfcomp_parallel)
    qed
  show ?thesis  
    apply (rule max_in_chainI)
    by (subst tspfcomp_parallel, simp_all add: assms f1) 
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
    by (metis assms(1) assms(2) tspfcomp_parallel)
qed
  
  subsection \<open>fun lub iterate\<close>

lemma tspfcomp_parallel_iterconst_eq1:  assumes "parcomp_well f1 f2"
shows "(\<lambda> x. (tsbDom\<cdot>x = tspfCompI f1 f2) \<leadsto> (\<Squnion>i. iter_tspfCompH f1 f2 i x))
            = (\<lambda> x. (tsbDom\<cdot>x = tspfCompI f1 f2) 
                        \<leadsto> ((f1\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f2))))" 
proof -
  have "\<forall> s.  tsbDom\<cdot>s \<noteq> tspfCompI f1 f2 \<or>
              Some ((\<Squnion>i. iter_tspfCompH f1 f2 i s)) 
                = Some (((f1\<rightleftharpoons>(s \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>(s \<bar> tspfDom\<cdot>f2))))"
    by (metis assms tspfcomp_parallel_lub_const1)
  thus ?thesis
    by meson
qed
  
  
lemma parallel_iterconst_cont [simp]: "cont (\<lambda> x. (tsbDom\<cdot>x = tspfCompI f1 f2) 
                        \<leadsto> ((f1\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f1)) \<uplus>  (f2\<rightleftharpoons>(x \<bar> tspfDom\<cdot>f2))))"
proof -
  have "cont (\<lambda>s. (Rep_cfun (Rep_TSPF f1))\<rightharpoonup>(s\<bar>tspfDom\<cdot>f1))"
     by (metis (no_types) cont_Rep_cfun2 cont_compose op_the_cont)
   hence "cont (\<lambda>s. tsbUnion\<cdot> (s  \<uplus>  ((Rep_cfun (Rep_TSPF f1))\<rightharpoonup>(s\<bar>tspfDom\<cdot>f1)))) \<and> cont (\<lambda>s. Rep_TSPF f2\<cdot>(s\<bar>tspfDom\<cdot>f2))"
     by simp
   hence "cont (\<lambda>s. s  \<uplus>  ((Rep_cfun (Rep_TSPF f1))\<rightharpoonup>(s\<bar>tspfDom\<cdot>f1))   \<uplus>  ((Rep_cfun (Rep_TSPF f2))\<rightharpoonup>(s\<bar>tspfDom\<cdot>f2))  )"
     using cont2cont_APP cont_compose op_the_cont by blast 
   thus ?thesis
     apply (subst tspfCompI_def)
     sorry
  qed
    
    (* TODO: TSPF well proof *)
    
    (* TODO: getch proof *)
end
  