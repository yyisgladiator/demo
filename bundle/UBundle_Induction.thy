theory UBundle_Induction
  imports UBundle UBundle_Pcpo UBundle_Conc stream.Streams
begin

  



(****************************************************)
section\<open>Definitions\<close>
(****************************************************) 


default_sort uscl_ind


definition ubMaxLen :: "lnat \<Rightarrow> 'M\<^sup>\<Omega> \<Rightarrow> bool" where
"ubMaxLen n ub  \<equiv> \<forall>c \<in> ubDom\<cdot>ub. usclLen\<cdot>(ub . c) \<le> n"

  (* Retrieves the first n Elements of each Stream. *)
definition ubTake:: "nat \<Rightarrow> 'x ubundle \<rightarrow> 'x ubundle" where
"ubTake n \<equiv> \<Lambda> b . ubMapStream (\<lambda>s. usclTake n\<cdot>s) b"

  (* Retrieves the first Element of each Stream. *)
definition ubHd:: " 'x ubundle \<rightarrow> 'x ubundle" where
"ubHd \<equiv> ubTake 1"

  (* Deletes the first n Elements of each Stream *)
definition ubDrop:: "nat \<Rightarrow> 'x ubundle \<rightarrow> 'x ubundle" where
"ubDrop n \<equiv> \<Lambda> b. ubMapStream (\<lambda>s. usclDrop n\<cdot>s) b"

  (* Deletes the first Elements of each stream *)
definition ubRt:: " 'x ubundle \<rightarrow> 'x ubundle" where
"ubRt \<equiv> ubDrop 1"



(****************************************************)
section\<open>Lemmas\<close>
(****************************************************) 


(* ----------------------------------------------------------------------- *)
subsection\<open>ubTake\<close>
(* ----------------------------------------------------------------------- *)


lemma usclTake_bot[simp] : "\<And> x. usclTake 0 \<cdot> x = \<bottom>"
  by (simp add: usclLen_zero usclTake_len)

lemma ubtake_cont [simp]:"cont (\<lambda>b. ubMapStream (\<lambda>s. usclTake n\<cdot>s) b)"
  by (simp add: ubMapStream_contI2 usclTake_well)

lemma ubtake_insert: "ubTake n\<cdot>b = ubMapStream (\<lambda>s. usclTake n\<cdot>s) b"
  by(simp add: ubTake_def)

lemma ubtake_zero: "ubTake 0\<cdot>In = ubLeast (ubDom\<cdot>In)"
  by (simp add: ubtake_insert ubMapStream_def ubLeast_def)

lemma ubtake_ubdom[simp]: "ubDom\<cdot>(ubTake n\<cdot>b) = ubDom\<cdot>b"
  by (simp add: ubMapStream_ubDom ubtake_insert usclTake_well)

lemma ubtake_ubgetch [simp]: assumes "c\<in>ubDom\<cdot>b"
  shows "ubTake n\<cdot>b . c = usclTake n\<cdot>(b .c)"
  using assms apply (simp add: ubtake_insert)
  by (simp add: ubMapStream_ubGetCh usclTake_well)

lemma ubtake_below [simp]: "ubTake n\<cdot>b \<sqsubseteq> ubTake (Suc n)\<cdot>b"
  using usclTake_below 
  by (metis ub_below ubtake_ubdom ubtake_ubgetch)

lemma ubtake_chain [simp]: "chain (\<lambda>n. ubTake n\<cdot>b)"
by (simp add: po_class.chainI)

lemma ubtake_lub_ubgetch: assumes "c\<in>ubDom\<cdot>b"
  shows "(\<Squnion>n. ubTake n\<cdot>b) . c = (\<Squnion>n. usclTake n\<cdot>(b . c))"
  by (metis (mono_tags, lifting) assms lub_eq po_class.chainI ubdom_chain_eq2 ubgetch_lub ubtake_below ubtake_ubdom ubtake_ubgetch)

lemma ubtake_lub [simp]: "(\<Squnion>n. ubTake n\<cdot>b) = b" (is "?L = b")
proof(rule ub_eq)
  show "ubDom\<cdot>?L = ubDom\<cdot>b"
    by (metis ubdom_chain_eq2 ubtake_chain ubtake_ubdom)
  fix c
  assume "c\<in>ubDom\<cdot>?L"
  hence "c\<in>ubDom\<cdot>b" by (simp add: \<open>ubDom\<cdot>(\<Squnion>n. ubTake n\<cdot>b) = ubDom\<cdot>b\<close>)
  hence "?L . c = (\<Squnion>n. usclTake n\<cdot>(b . c))" using ubtake_lub_ubgetch by auto
  thus "?L .c = b .c" using usclTake_lub by simp
qed

lemma ubTakeLen: assumes "ubDom\<cdot>x \<noteq> {}"
  shows "(ubLen (ubTake a\<cdot>x)) \<le> Fin a"
proof-
  have "\<And>c. c \<in> ubDom\<cdot>x \<Longrightarrow> usclLen\<cdot>((ubTake a\<cdot>x) . c) \<le> Fin a"
    by (metis le_cases ubtake_ubgetch usclTake_eq usclTake_len)
  thus ?thesis
    by (metis (no_types, lifting) assms ubLen_def ublen_min_on_channel ubtake_ubdom)
qed

lemma ubTakeLen_zero: assumes "ubLen x = 0" 
  shows "ubLen (ubTake a\<cdot>x) = 0"
proof-
  have ubdom_x_nempty: "ubDom\<cdot>x \<noteq> {}" 
    by (metis Inf'_neq_0 assms ubLen_def)
  hence "\<exists>c. c \<in> ubDom\<cdot>(ubTake a\<cdot>x) \<and> usclLen\<cdot>((ubTake a\<cdot>x) . c) = 0"
    by (metis (no_types, lifting) Fin_02bot assms le_cases lnle_Fin_0 lnzero_def ubLen_def
        ublen_min_on_channel ubtake_ubdom ubtake_ubgetch usclTake_eq)
  hence "0 \<in> {(usclLen\<cdot>((ubTake a\<cdot>x) . c)) | c. c \<in> ubDom\<cdot>(ubTake a\<cdot>x)}"
    by force
  hence "(LEAST ln. ln\<in>{(usclLen\<cdot>((ubTake a\<cdot>x) . c)) | c. c \<in> ubDom\<cdot>(ubTake a\<cdot>x)}) = 0"
    by (metis (no_types, lifting) Least_le bot_is_0 bottomI lnle_def)
  then show ?thesis
    by (simp add: ubLen_def ubdom_x_nempty)
qed

lemma ubTakeLen_le : "ubLen (ubTake a\<cdot>x) \<le> ubLen x"
proof (cases "ubDom\<cdot>x = {}")
  case True
  then show ?thesis
    by (simp add: ubLen_def)
next
  case False
  have "ubDom\<cdot>(ubTake a\<cdot>x) \<noteq> {}"
    by (simp add: False)
  hence ublen_ubtake_least: "ubLen (ubTake a\<cdot>x) = (LEAST ln. ln\<in>{(usclLen\<cdot>((ubTake a\<cdot>x) . c)) | c. c \<in> ubDom\<cdot>(ubTake a\<cdot>x)})"
    by (simp add: ubLen_def)
  have "\<And>c. c \<in> ubDom\<cdot>x \<Longrightarrow> usclLen\<cdot>((ubTake a\<cdot>x) . c) \<le> usclLen\<cdot>(x . c)"
    by (metis le_cases ubtake_ubgetch usclTake_eq usclTake_len)
  have "\<And>c. c \<in> ubDom\<cdot>x \<Longrightarrow> usclLen\<cdot>((ubTake a\<cdot>x) . c) \<in> {(usclLen\<cdot>((ubTake a\<cdot>x) . c)) | c. c \<in> ubDom\<cdot>(ubTake a\<cdot>x)}"
    by force
  then show ?thesis
    by (metis (no_types, lifting) Least_le dual_order.trans le_cases ubLen_def ubTakeLen
        ublen_min_on_channel ublen_ubtake_least ubtake_ubdom ubtake_ubgetch usclTake_eq)
qed


(* ----------------------------------------------------------------------- *)
  subsection \<open>ubHd\<close>
(* ----------------------------------------------------------------------- *)


lemma ubhd_ubdom[simp]: "ubDom\<cdot>(ubHd\<cdot>b) = ubDom\<cdot>b"
  by(simp add: ubHd_def)

lemma ubHdLen: assumes "ubDom\<cdot>x \<noteq> {}" 
  shows "ubLen (ubHd\<cdot>x) \<le> Fin (Suc(0))"
  by (simp add: assms ubHd_def ubTakeLen)

lemma ubHdLen_zero: assumes "ubLen x = 0"
  shows "ubLen (ubHd\<cdot>x) = 0"
proof-
  have ubhd_ubdom_nempty: "ubDom\<cdot>(ubHd\<cdot>x) \<noteq> {}"
    by (metis Inf'_neq_0 assms ubLen_def ubhd_ubdom)
  have ubhd_ublen_zero_geq: "ubLen (ubHd\<cdot>x) \<ge> Fin 0"
    using Fin_leq_Suc_leq lnat_po_eq_conv by fastforce
  have "\<exists>c. c \<in> ubDom\<cdot>(ubHd\<cdot>x) \<and> usclLen\<cdot>((ubHd\<cdot>x) . c) = Fin 0 \<Longrightarrow> ubLen (ubHd\<cdot>x) = Fin 0"
    by (metis (mono_tags, lifting) Fin_02bot Least_le ubhd_ublen_zero_geq ubhd_ubdom_nempty
        less2eq mem_Collect_eq ubLen_def)
  thus ?thesis
    by (metis Fin_02bot Fin_Suc One_nat_def assms less2eq less_lnsuc lnzero_def neq02Suclnle
        ubHd_def ubLen_geI ubTakeLen ubhd_ubdom ubhd_ubdom_nempty ubtake_ubgetch usclTake_eq)
qed

lemma ubHdLen_one: assumes "ubDom\<cdot>x \<noteq> {}" and "ubLen x > 0"
  shows "ubLen (ubHd\<cdot>x) = Fin 1" 
proof-
  have "\<And>c. c \<in> ubDom\<cdot>x \<Longrightarrow> usclLen\<cdot>(x . c) > 0" 
    by (metis (mono_tags, lifting) assms(1) assms(2) mem_Collect_eq not_le not_less_Least
        ubLen_def usclLen_bot usclLen_zero)
  hence "\<And>c. c \<in> ubDom\<cdot>x \<Longrightarrow> usclLen\<cdot>(usclTake 1\<cdot>(x . c)) = Fin 1"  
    using usclTake_len by force
  thus ?thesis
    by (metis (no_types, lifting) assms(1) ubHd_def ubLen_def ubhd_ubdom
        ublen_min_on_channel ubtake_ubgetch)
qed


(* ----------------------------------------------------------------------- *)
  subsection \<open>ubDrop\<close>
(* ----------------------------------------------------------------------- *)


lemma ubdrop_cont [simp]:"cont (\<lambda>b. ubMapStream (\<lambda>s. usclDrop n\<cdot>s) b)"
  by (simp add: ubMapStream_contI2 usclDrop_well)

lemma ubdrop_insert: "ubDrop n\<cdot>b = ubMapStream (\<lambda>s. usclDrop n\<cdot>s) b"
  by(simp add: ubDrop_def)

lemma ubdrop_zero[simp]: "ubDrop 0\<cdot>b = b"
  by(simp add: ubdrop_insert ubMapStream_def usclDrop_eq)

lemma ubdrop_ubdom[simp]: "ubDom\<cdot>(ubDrop n\<cdot>b) = ubDom\<cdot>b"
  apply (simp add: ubdrop_insert)
  by (simp add: ubMapStream_ubDom usclDrop_well)
  
lemma ubdrop_ubgetch [simp]: assumes "c\<in>ubDom\<cdot>b"
  shows "ubDrop n\<cdot>b . c = usclDrop n\<cdot>(b .c)"
  using assms apply (simp add: ubdrop_insert)
  by (simp add: ubMapStream_ubGetCh usclDrop_well)


(* ----------------------------------------------------------------------- *)
  subsection \<open>ubRt\<close>
(* ----------------------------------------------------------------------- *)


lemma ubrt_ubdom[simp]: "ubDom\<cdot>(ubRt\<cdot>b) = ubDom\<cdot>b"
  by(simp add: ubRt_def)

lemma ubRt2usclrt[simp]: assumes "ubWell [c \<mapsto> x]"
                        shows "ubRt\<cdot>(Abs_ubundle [c \<mapsto> x]) = (Abs_ubundle [c \<mapsto> usclDrop 1 \<cdot>x])"
  by (smt assms dom_empty dom_fun_upd fun_upd_same option.discI option.sel singletonD ubMapStream_ubGetCh ubRt_def ubWell_def ubdom_ubrep_eq ubdrop_insert ubdrop_ubdom ubgetchI ubgetch_insert ubrep_ubabs usclDrop_well)

lemma ubRtLen: assumes "ubLen x > 0"
  shows "lnsuc\<cdot>(ubLen (ubRt\<cdot>x)) = ubLen x"
proof (cases "ubDom\<cdot>x = {}")
  case True
  then show ?thesis
    by (simp add: ubLen_def)
next
  case False
  have ubdrop_ubdom_eq: "ubDom\<cdot>x = ubDom\<cdot>(ubDrop 1\<cdot>x)"
    by simp
  hence ublen_ubdrop_least:
    "ubLen (ubDrop 1\<cdot>x) = (LEAST ln. ln\<in>{(usclLen\<cdot>((ubDrop 1\<cdot>x . c))) | c. c \<in> ubDom\<cdot>(ubDrop 1\<cdot>x)})"
    by (simp add: False ubLen_def)
  have uscldrop_uscllen_suc: "\<And>y k. usclLen\<cdot>y = lnsuc\<cdot>k \<Longrightarrow> usclLen\<cdot>(usclDrop 1\<cdot>y) = k"
    by (metis (no_types, lifting) Fin_Suc One_nat_def inf_ub less2eq lnat_well_h2 lnsuc_lnle_emb
        order_le_less order_refl usclDrop_len)
  hence uscllen_uscldrop_suc:
    "\<And>c. c \<in> ubDom\<cdot>x \<Longrightarrow> usclLen\<cdot>(x . c) = lnsuc\<cdot>(usclLen\<cdot>(usclDrop 1\<cdot>(x . c)))"
    by (metis (mono_tags, lifting) False Least_le assms gr_0 mem_Collect_eq not_le ubLen_def
        usclLen_bot usclLen_zero)
  hence usclLen_lnsuc_in_set:
    "\<And>c. c \<in> ubDom\<cdot>x \<Longrightarrow> lnsuc\<cdot>(usclLen\<cdot>((ubDrop 1\<cdot>x) . c)) \<in> {(usclLen\<cdot>(x . c)) | c. c \<in> ubDom\<cdot>x}"
    by force
  obtain c where c_def: "c \<in> ubDom\<cdot>(ubDrop 1\<cdot>x) \<and> lnsuc\<cdot>(usclLen\<cdot>((ubDrop 1\<cdot>x) . c)) = ubLen x"
    by (metis (no_types, lifting) False ubLen_def ubdrop_ubdom_eq ubdrop_ubgetch
        ublen_min_on_channel uscllen_uscldrop_suc)
  hence "\<And>ch. ch \<in> ubDom\<cdot>(ubDrop 1\<cdot>x) \<Longrightarrow> usclLen\<cdot>((ubDrop 1\<cdot>x) . c) \<le> usclLen\<cdot>((ubDrop 1\<cdot>x) . ch)"
    by (metis (mono_tags, lifting) False Least_le lnsuc_lnle_emb ubLen_def ubdrop_ubdom_eq
        usclLen_lnsuc_in_set)
  hence "usclLen\<cdot>((ubDrop 1\<cdot>x) . c) = ubLen (ubDrop 1\<cdot>x)"
    by (metis (mono_tags, lifting) Least_le c_def less2eq mem_Collect_eq ubLen_geI ubRt_def
        ubdrop_ubdom_eq ublen_ubdrop_least ubrt_ubdom)
  then show ?thesis
    by (metis c_def ubRt_def)
qed

lemma ubRtLen_zero: assumes "ubLen x = Fin 0"
  shows "ubLen (ubRt\<cdot>x) = Fin 0"
proof-
  have ubrt_ubdom_nempty: "ubDom\<cdot>(ubRt\<cdot>x) \<noteq> {}"
    by (metis Fin_0 Inf'_neq_0 assms lnzero_def ubLen_def ubrt_ubdom)
  have "ubLen (ubRt\<cdot>x) \<ge> Fin 0"
    by simp
  hence "\<exists>c. c \<in> ubDom\<cdot>(ubRt\<cdot>x) \<and> usclLen\<cdot>((ubRt\<cdot>x) . c) = Fin 0 \<Longrightarrow> ubLen (ubRt\<cdot>x) = Fin 0"
    using ubrt_ubdom_nempty by (metis (mono_tags, lifting) Least_le less2eq mem_Collect_eq ubLen_def)
  thus ?thesis
    by (metis (mono_tags, lifting) Fin_02bot One_nat_def assms less2nat lnzero_def ubrt_ubdom
        ubLen_def ubRt_def ubdrop_ubgetch ublen_min_on_channel usclDrop_len usclLen_bot usclLen_zero zero_le_one)
qed


(* ----------------------------------------------------------------------- *)
  subsection\<open>MaxLen\<close>
(* ----------------------------------------------------------------------- *)


lemma ubmaxlen_least: "ubMaxLen 0 (ubLeast cs)"
  by(simp add: ubMaxLen_def usclLen_bot)

lemma ubmaxlen_sbtake: "ubMaxLen (Fin n) (ubTake n\<cdot>x)"
  apply (simp add: ubMaxLen_def ubTake_def)
  apply (simp add: ubMapStream_ubDom ubMapStream_ubGetCh usclTake_len usclTake_len_le usclTake_well)
  by (metis (no_types, lifting) leI le_cases lnat_well_h1 usclTake_len usclTake_len_le)

lemma ubmax_len_len: assumes "ubLen ub = n" and "ubMaxLen n ub" 
  shows "\<And>c. c\<in>ubDom\<cdot>ub \<Longrightarrow> usclLen\<cdot>(ub . c) = n"
  by (metis assms(1) assms(2) dual_order.antisym ubMaxLen_def ublen_channel)



lemma ubleast_sbtake: assumes "x \<noteq> ubLeast (ubDom\<cdot>x)" shows "ubHd\<cdot>x \<noteq> ubLeast (ubDom\<cdot>x)"
proof - 
  obtain my_c where my_c_def1: "x . my_c \<noteq> \<bottom>" and my_c_def2: "my_c \<in> ubDom\<cdot>x"
    using assms by (metis ubgetchI ubleast_ubdom ubleast_ubgetch)
  have "(ubHd\<cdot>x) . my_c \<noteq> \<bottom>" 
    apply (simp add: ubHd_def)
    apply (simp add: my_c_def1 my_c_def2)
    using usclLen_zero inject_Fin le_numeral_extra(3) less2nat my_c_def1 n_not_Suc_n neq02Suclnle usclLen_bot usclTake_len by fastforce
  thus ?thesis 
    using my_c_def2 by auto
qed

lemma ubmaxlen_least_only: assumes "ubMaxLen (Fin 0) x"
  shows "x = ubLeast (ubDom\<cdot>x)"
proof-
  have f1: "\<And>c. c \<in> ubDom\<cdot>x \<Longrightarrow> usclLen\<cdot>(x . c) \<le> 0" 
    using assms lnzero_def ubMaxLen_def by auto
  have f3: "(ubDom\<cdot>x) = ubDom\<cdot>(ubLeast (ubDom\<cdot>x))" 
    by simp
  have f4: "\<And>c. c \<in> ubDom\<cdot>x \<Longrightarrow>  (x . c) = ubLeast (ubDom\<cdot>x) . c"
    using f1 
    by (simp add: usclLen_zero)
  show ?thesis using f1 f3 f4 ubmaxlen_least
    by (simp add: ubgetchI)
qed

lemma ubconc_hdrt_dom: "ubDom\<cdot>x = ubDom\<cdot>(ubConc (ubHd\<cdot>x)\<cdot>(ubRt\<cdot>x))"
  by simp 

lemma ubconc_sbhdrt : "x = ubConc (ubHd\<cdot>x)\<cdot>(ubRt\<cdot>x)" (is "x = ?R")
proof(rule ub_eq)
  show f0: "ubDom\<cdot>x = ubDom\<cdot>(?R)" by simp
  fix x :: "'a\<^sup>\<Omega>"
  fix c
  assume a0: "c\<in>ubDom\<cdot>x" 
  show "x  .  c = (ubConc (ubHd\<cdot>x)\<cdot>(ubRt\<cdot>x) ) .  c"
    apply(subst ubConc_usclConc_eq)
        using ubhd_ubdom a0 apply auto[1]
         using ubrt_ubdom a0 apply auto[1]
  proof -
      have f1: "c\<in>ubDom\<cdot>(ubConc (ubHd\<cdot>x)\<cdot>(ubRt\<cdot>x))" 
        using a0 ubconc_hdrt_dom by blast
      have f2: "c\<in>ubDom\<cdot>(ubHd\<cdot>x)" 
        by (simp add: a0)
      have f3: "c\<in>ubDom\<cdot>(ubRt\<cdot>x)"
        by (simp add: a0)
      show "x  .  c = usclConc (ubHd\<cdot>x  .  c)\<cdot>(ubRt\<cdot>x  .  c)" 
        apply (simp add: ubHd_def ubRt_def)
        apply (simp add: ubTake_def ubDrop_def)
        by (metis One_nat_def a0 ubdrop_insert ubdrop_ubgetch ubtake_insert ubtake_ubgetch uscl_Hd_Rt)
    qed
  qed

lemma ubmaxlen_sbrt_sbhd : assumes "ubMaxLen (Fin (Suc n)) x" 
  shows " ubMaxLen (Fin n) (ubRt\<cdot>x)"
proof - 
  have f1: "\<And>c. c \<in> ubDom\<cdot>x \<Longrightarrow>  usclLen\<cdot>(x . c) \<le> Fin (Suc n)" using assms 
    by (simp add: ubMaxLen_def)
  have f2: "\<And>c. c \<in> ubDom\<cdot>(ubRt\<cdot>x) \<Longrightarrow>  usclLen\<cdot>((ubRt\<cdot>x) . c) \<le> Fin n" 
    apply(simp add: ubRt_def)
    using f1 le_imp_less_or_eq
    by (simp add: usclDrop_len)
  show ?thesis 
    using f2 ubMaxLen_def by blast
qed


(* ----------------------------------------------------------------------- *)
section\<open>Induction\<close>
(* ----------------------------------------------------------------------- *)


lemma ubcases: "\<And>x. x = (ubLeast (ubDom\<cdot>x)) \<or> (\<exists>a s. ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a  \<and> a \<noteq> (ubLeast (ubDom\<cdot>x)) \<and> x = ubConc a\<cdot>s)"
  apply(case_tac "x = (ubLeast (ubDom\<cdot>x))")
   apply(simp_all)
proof - 
  fix x :: "'a\<^sup>\<Omega>"
  assume a1: "x \<noteq> ubLeast (ubDom\<cdot>x)"
  show "\<exists>a. ubDom\<cdot>a = ubDom\<cdot>x \<and> (\<exists>s. ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (Suc (0::nat))) a \<and> a \<noteq> (ubLeast (ubDom\<cdot>x))  \<and> x = ubConc a\<cdot>s)"
    apply(rule_tac x = "ubHd\<cdot>x" in exI)
    apply(simp)
    apply(rule_tac x = "ubRt\<cdot>x" in exI)
    apply(simp)
    apply rule
     apply(simp add: ubMaxLen_def ubHd_def)
     apply rule
    apply (metis ubMaxLen_def ubmaxlen_sbtake ubtake_ubdom ubtake_ubgetch)
    apply(simp add: ubleast_sbtake a1)
    by (metis ubconc_sbhdrt)
qed

lemma ubcases2: "\<And>x P. \<lbrakk>x = (ubLeast (ubDom\<cdot>x)) \<Longrightarrow> P; 
                        \<And>a s. ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a \<and> a \<noteq> (ubLeast (ubDom\<cdot>x)) \<and> x = ubConc a\<cdot>s \<Longrightarrow> P\<rbrakk> 
                        \<Longrightarrow> P"
  using ubcases by blast

lemma ubtake_ind2: 
  "\<forall>x. P (ubLeast (ubDom\<cdot>x)) \<and> 
       (\<forall>a s. P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a  \<and> a \<noteq> (ubLeast (ubDom\<cdot>x)) \<longrightarrow> P (ubConc a\<cdot>s)) 
        \<and> ubMaxLen (Fin n) x
       \<longrightarrow> P x"
  apply rule+
proof(induct n)
  case 0
  have "\<And>x.
       P (ubLeast (ubDom\<cdot>x)) \<Longrightarrow>
        (\<forall>a s.
            P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (1::nat)) a \<and> a \<noteq> ubLeast (ubDom\<cdot>x) \<longrightarrow> P (ubConc a\<cdot>s)) \<Longrightarrow>
       ubMaxLen (Fin (0::nat)) x \<Longrightarrow>
       P x"
  proof -
    fix x :: "'a\<^sup>\<Omega>"
    assume a0: "P (ubLeast (ubDom\<cdot>x))"
    assume a1: "(\<forall>a s.
            P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (1::nat)) a \<and> a \<noteq> ubLeast (ubDom\<cdot>x) \<longrightarrow> P (ubConc a\<cdot>s))"
    assume a2: "ubMaxLen (Fin (0::nat)) x"
    show "P x" 
    proof-
      have f0: "x = ubLeast (ubDom\<cdot>x)" using a2 
        by (simp add: ubmaxlen_least_only)
      show ?thesis using a0 f0 by auto
    qed
  qed
  then show ?case
    using "0.prems" by blast
next
  case (Suc n)
  have "\<And>(n::nat) x.
       (\<And>x.
           P (ubLeast (ubDom\<cdot>x)) \<and>
           (\<forall>a s.
               P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (1::nat)) a \<and> a \<noteq> ubLeast (ubDom\<cdot>x) \<longrightarrow> P (ubConc a\<cdot>s)) \<and>
           ubMaxLen (Fin n) x \<Longrightarrow>
           P x) \<Longrightarrow>
       P (ubLeast (ubDom\<cdot>x)) \<Longrightarrow>
       (\<forall>a s.
           P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (1::nat)) a \<and> a \<noteq> ubLeast (ubDom\<cdot>x) \<longrightarrow> P (ubConc a\<cdot>s)) \<Longrightarrow>
       ubMaxLen (Fin (Suc n)) x \<Longrightarrow>
       P x"
  proof -
    fix n :: "nat"
    fix x :: "'a \<^sup>\<Omega>"
    assume a3: "(\<And>x.
              P (ubLeast (ubDom\<cdot>x)) \<and>
              (\<forall>a s.
                  P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (1::nat)) a \<and> a \<noteq> ubLeast (ubDom\<cdot>x) \<longrightarrow> P (ubConc a\<cdot>s)) \<and>
              ubMaxLen (Fin n) x \<Longrightarrow>
              P x)"
    assume a4: "P (ubLeast (ubDom\<cdot>x))"
    assume a5: "(\<forall>a s.
            P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (1::nat)) a \<and> a \<noteq> ubLeast (ubDom\<cdot>x) \<longrightarrow> P (ubConc a\<cdot>s))"
    assume a6: "ubMaxLen (Fin (Suc n)) x"
    show "P x" 
    proof -
      have f1: "x = ubConc (ubHd\<cdot>x)\<cdot>(ubRt\<cdot>x)" 
        by (simp add: ubconc_sbhdrt)
      have f2: "ubMaxLen (Fin 1) (ubHd\<cdot>x)" 
        by (simp add: ubHd_def ubmaxlen_sbtake)
      have f3: "ubDom\<cdot>(ubHd\<cdot>x) = ubDom\<cdot>x" 
        by simp 
      have f4: "ubDom\<cdot>(ubRt\<cdot>x) = ubDom\<cdot>x" 
        by simp
      have f5: "P (ubRt\<cdot>x)" 
      proof - 
        have f51: "ubMaxLen (Fin n) (ubRt\<cdot>x)" 
          by (simp add: a6 ubmaxlen_sbrt_sbhd)
        show ?thesis using f51 
          by (metis a3 a4 a5 f4)
      qed
      have f6: "P (ubConc (ubHd\<cdot>x)\<cdot>(ubRt\<cdot>x))" 
        by (metis a4 a5 f1 f2 f3 f4 f5 ubleast_sbtake)
      show ?thesis using f5 f6 a3 a4 a5 a6 
        by (metis f1)
    qed
  qed
  then show ?case
    using Suc.hyps Suc.prems by blast
qed

lemma ubtake_ind: 
  "\<forall>x. (P (ubLeast (ubDom\<cdot>x)) \<and> 
       (\<forall>a s. P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a \<and> a \<noteq> (ubLeast (ubDom\<cdot>x)) \<longrightarrow> P (ubConc a\<cdot>s))) 
       \<longrightarrow> P (ubTake n\<cdot>x)" 
  apply rule+
  apply(subst ubtake_ind2, simp_all)
  using ubmaxlen_sbtake ubtake_ind2
  by auto

lemma finind_ub: 
  "\<lbrakk> \<exists>n. ubMaxLen (Fin n) x; 
     P (ubLeast (ubDom\<cdot>x)); 
     \<And>u ub. P ub \<and> ubDom\<cdot>u = (ubDom\<cdot>x) \<and> ubDom\<cdot>ub = (ubDom\<cdot>x) \<and> ubMaxLen (Fin 1) u \<and> u \<noteq> (ubLeast (ubDom\<cdot>x)) \<Longrightarrow> P (ubConc u\<cdot>ub) \<rbrakk>
     \<Longrightarrow> P x"
proof - 
fix x :: "'a ubundle"
  assume a0: "\<exists>n. ubMaxLen (Fin n) x"
  assume a1: "P (ubLeast (ubDom\<cdot>x))"
  assume a2: "\<And>u ub. P ub \<and> ubDom\<cdot>u = (ubDom\<cdot>x) \<and> ubDom\<cdot>ub = (ubDom\<cdot>x) \<and> ubMaxLen (Fin 1) u \<and> u \<noteq> (ubLeast (ubDom\<cdot>x)) \<Longrightarrow> P (ubConc u\<cdot>ub)"
  obtain n where n_def:  "ubMaxLen (Fin n) x"
    using a0 by blast
  have f1: "ubDom\<cdot>x = ubDom\<cdot>(ubTake n\<cdot>x)" by simp
  have f2:  "x =  (ubTake n\<cdot>x) "
    proof-  
      have f21: "\<And>c. c\<in>(ubDom\<cdot>x) \<Longrightarrow> usclLen\<cdot> (x . c) \<le>  Fin n"
        using n_def ubMaxLen_def by blast
      have f22: "\<And>c. c\<in>(ubDom\<cdot>x) \<Longrightarrow> usclLen\<cdot>((ubTake n\<cdot>x).c) \<le>  Fin n"
        using ubMaxLen_def ubmaxlen_sbtake ubtake_ubdom by blast
      have f23: "\<And>c. c\<in>(ubDom\<cdot>x) \<Longrightarrow> (ubTake n\<cdot>x).c = usclTake n\<cdot>(x . c)"
        by simp
      have f25: "\<And>c. c\<in>(ubDom\<cdot>x) \<Longrightarrow> usclTake n\<cdot>(x . c) = x . c"
      proof -
        fix c
        assume a0: "c \<in> ubDom\<cdot>x"
        show "usclTake n\<cdot>(x  .  c) = x  .  c"
          by (simp add: usclTake_eq a0 f21)
      qed
      show ?thesis
         by (simp add: ubgetchI a0 n_def f21 f22 f23 f25)
    qed
  show "P x" apply (subst f2) 
    apply (subst ubtake_ind)
     apply rule
      apply (simp add: a1)
     apply (simp add: a2)
    by simp
qed

lemma ind_ub: 
  "\<lbrakk> adm P; 
     P (ubLeast (ubDom\<cdot>x)); 
     \<And>u ub. P ub \<and> ubDom\<cdot>u = (ubDom\<cdot>x) \<and> ubDom\<cdot>ub = (ubDom\<cdot>x) \<and> ubMaxLen (Fin 1) u \<and> u \<noteq> (ubLeast (ubDom\<cdot>x)) \<Longrightarrow> P (ubConc u\<cdot>ub) \<rbrakk>
     \<Longrightarrow> P x"
  apply (unfold adm_def)
  apply (erule_tac x="\<lambda>i. ubTake i\<cdot>x" in allE, auto)
  by(simp add: ubtake_ind)


(* ----------------------------------------------------------------------- *)
section\<open>Instantiation Stream\<close>
(* ----------------------------------------------------------------------- *)


instantiation stream :: (message) uscl_ind
begin
  definition usclTake_stream_def: "usclTake \<equiv> stake"
  definition usclDrop_stream_def: "usclDrop \<equiv> sdrop"
instance
  apply intro_classes      
  apply simp_all
  apply (simp add: usclOkay_stream_def usclConc_stream_def usclTake_stream_def usclDrop_stream_def)
  apply (simp add: usclTake_stream_def usclLen_stream_def slen_stake)
  apply (simp add: usclLen_stream_def usclDrop_stream_def)
  apply (simp add: slen_stake usclLen_stream_def usclTake_stream_def)
  apply (metis (mono_tags, lifting) dual_order.strict_implies_order fin2stake_lemma  usclLen_stream_def usclTake_stream_def)
  apply (metis (mono_tags, lifting) fin2stake fin2stake_lemma le_neq_trans lnat_well_h1 order.strict_implies_order usclLen_stream_def usclTake_stream_def)   
  apply (metis (mono_tags, lifting) dual_order.trans sdom_prefix stream.take_below usclOkay_stream_def usclTake_stream_def) 
  apply (simp add: stake_mono usclTake_stream_def)
  apply (simp add: reach_stream usclTake_stream_def)
  apply (simp add: sdrop_forw_rt slen_rt_ile_eq usclDrop_stream_def usclLen_stream_def)
  apply (simp add: usclDrop_stream_def)
  by(metis (mono_tags, lifting) dual_order.trans sdrop_sdom usclDrop_stream_def usclOkay_stream_def)

end


end