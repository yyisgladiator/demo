theory bundle_induction
imports  bundle.SBElem
begin

section{* more general lemmata *}

lemma ubhd_getch_noteps: assumes "\<forall>c\<in>ubDom\<cdot>x. x . c \<noteq> \<bottom>"
  shows "\<forall>c\<in>ubDom\<cdot>x.  ubHd\<cdot>x . c \<noteq> \<bottom>"
  by (metis (no_types, lifting) Fin_0 assms empty_iff le_imp_less_or_eq ubHdLen_one ubHd_def ubLen_def ubLen_smallereq_all ubTakeLen_le ubhd_ubdom ubleast_sbtake ublen_min_on_channel ubtake_zero usclLen_bot usclLen_zero) 

lemma ubcases_alt: "\<And>x. (\<exists>c\<in>ubDom\<cdot>x. x . c = \<bottom>) \<or> (\<exists>a s. ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a  \<and> (\<forall>c\<in>ubDom\<cdot>x. a . c \<noteq> \<bottom>) \<and> x = ubConc a\<cdot>s)"
  apply(case_tac "(\<exists>c\<in>ubDom\<cdot>x. x . c = \<bottom>)", simp)
  by (metis (no_types, hide_lams) ubhd_getch_noteps ubHd_def ubconc_sbhdrt ubhd_ubdom ubmaxlen_sbtake ubrt_ubdom)

lemma ubcases_alt2: "\<And>x P. \<lbrakk>\<exists>c\<in>ubDom\<cdot>x. x . c = \<bottom> \<Longrightarrow> P; 
                        \<And>a s. ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a  \<and> (\<forall>c\<in>ubDom\<cdot>x. a . c \<noteq> \<bottom>) \<and> x = ubConc a\<cdot>s \<Longrightarrow> P\<rbrakk> 
                        \<Longrightarrow> P"
  using ubcases_alt by blast

lemma ublen_sbrt_sbhd : 
  assumes "ubLen x \<le> Fin (Suc n)" 
  shows " ubLen (ubRt\<cdot>x) \<le> Fin n"
  by (metis Fin_Suc assms bottomI leD leI less2lnleD lnle_Fin_0 lnle_def lnsuc_lnle_emb lnzero_def nat.distinct(1) ubRtLen ubRtLen_zero)


section{* new bundle induction *}

subsection{* auxiliary lemmata*}

lemma ubtake_ind_alt2: 
  "\<forall>x. (\<forall>ub.  ubDom\<cdot>ub = ubDom\<cdot>x \<and> (\<exists>c\<in>ubDom\<cdot>x. ub . c = \<bottom>)\<longrightarrow> P ub) \<and> 
       (\<forall>a s. P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (Suc 0)) a  \<and> (\<forall>c\<in>ubDom\<cdot>a. a . c \<noteq> \<bottom>) \<longrightarrow> P (ubConc a\<cdot>s)) 
        \<and> ubLen x \<le> Fin n
       \<longrightarrow> P x"
proof(induct n)
  case 0
  have "\<And>x.
       (\<forall>ub.  ubDom\<cdot>ub = ubDom\<cdot>x \<and> (\<exists>c\<in>ubDom\<cdot>x. ub . c = \<bottom>)\<longrightarrow> P ub) \<Longrightarrow>
        (\<forall>a s. P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (Suc 0)) a \<and> (\<forall>c\<in>ubDom\<cdot>a. a . c \<noteq> \<bottom>) \<longrightarrow> P (ubConc a\<cdot>s)) \<Longrightarrow>
       ubLen x \<le> Fin 0 \<Longrightarrow> P x"
    by (metis (mono_tags, lifting) Fin_02bot Inf'_neq_0 bottomI lnle_def lnzero_def ubLen_def ublen_min_on_channel usclLen_zero)
  then show ?case
    using "0.prems" by blast
next
  case (Suc n)
  have "\<And>(n::nat) x.
       (\<And>x.
          (\<forall>ub.  ubDom\<cdot>ub = ubDom\<cdot>x \<and> (\<exists>c\<in>ubDom\<cdot>x. ub . c = \<bottom>)\<longrightarrow> P ub) \<and>
           (\<forall>a s. P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (Suc 0)) a \<and>  (\<forall>c\<in>ubDom\<cdot>a. a . c \<noteq> \<bottom>) \<longrightarrow> P (ubConc a\<cdot>s)) \<and>
           ubLen x \<le> Fin n \<Longrightarrow> P x) \<Longrightarrow>
      (\<forall>ub.  ubDom\<cdot>ub = ubDom\<cdot>x \<and> (\<exists>c\<in>ubDom\<cdot>x. ub . c = \<bottom>)\<longrightarrow> P ub) \<Longrightarrow>
       (\<forall>a s. P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (Suc 0)) a \<and>  (\<forall>c\<in>ubDom\<cdot>a. a . c \<noteq> \<bottom>) \<longrightarrow> P (ubConc a\<cdot>s)) \<Longrightarrow>
       ubLen x \<le> Fin (Suc n) \<Longrightarrow> P x"
  proof -
    fix n :: "nat"
    fix x ::" 'a\<^sup>\<Omega>"
    assume a3: "(\<And>x.
             (\<forall>ub.  ubDom\<cdot>ub = ubDom\<cdot>x \<and> (\<exists>c\<in>ubDom\<cdot>x. ub . c = \<bottom>)\<longrightarrow> P ub) \<and>
              (\<forall>a s. P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (Suc 0)) a \<and> (\<forall>c\<in>ubDom\<cdot>a. a . c \<noteq> \<bottom>) \<longrightarrow> P (ubConc a\<cdot>s)) \<and>
              ubLen x \<le> Fin n \<Longrightarrow> P x)"
    assume a4: "(\<forall>ub.  ubDom\<cdot>ub = ubDom\<cdot>x \<and> (\<exists>c\<in>ubDom\<cdot>x. ub . c = \<bottom>)\<longrightarrow> P ub)"
    assume a5: "(\<forall>a s. P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin (Suc 0)) a \<and> (\<forall>c\<in>ubDom\<cdot>a. a . c \<noteq> \<bottom>) \<longrightarrow> P (ubConc a\<cdot>s))"
    assume a6: "ubLen x \<le> Fin (Suc n)"
    show "P x" 
    proof -
      have f1: "x = ubConc (ubHd\<cdot>x)\<cdot>(ubRt\<cdot>x)" 
        by (simp add: ubconc_sbhdrt)
      have f2: "ubMaxLen (Fin (Suc 0)) (ubHd\<cdot>x)" 
        by (simp add: ubHd_def ubmaxlen_sbtake)
      have f3: "ubDom\<cdot>(ubHd\<cdot>x) = ubDom\<cdot>x" 
        by simp 
      have f4: "ubDom\<cdot>(ubRt\<cdot>x) = ubDom\<cdot>x" 
        by simp
      have f5: "P (ubRt\<cdot>x)" 
      proof - 
        have f51: "ubLen (ubRt\<cdot>x) \<le> Fin n" 
          by (simp add: a6 ublen_sbrt_sbhd)
        show ?thesis using f51
          by(subst a3, simp_all add: f51 a4 a5)
      qed
      have f6: "P (ubConc (ubHd\<cdot>x)\<cdot>(ubRt\<cdot>x))"
        by (metis One_nat_def a4 a5 f1 f2 f3 f4 f5 ubhd_getch_noteps)
      show ?thesis using f5 f6 a3 a4 a5 a6 
        by (metis f1)
    qed
  qed
  then show ?case
    using Suc.hyps by blast 
qed

lemma ubtake_ind_alt: 
  "\<forall>x. (\<forall>ub.  ubDom\<cdot>ub = ubDom\<cdot>x \<and> (\<exists>c\<in>ubDom\<cdot>x. ub . c = \<bottom>)\<longrightarrow> P ub) \<and> ubDom\<cdot>x \<noteq> {} \<and>
       (\<forall>a s. P s \<and> ubDom\<cdot>a = ubDom\<cdot>x \<and> ubDom\<cdot>s = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) a \<and> (\<forall>c\<in>ubDom\<cdot>a. a . c \<noteq> \<bottom>) \<longrightarrow> P (ubConc a\<cdot>s)) 
       \<longrightarrow> P (ubTake n\<cdot>x)" 
  apply rule+
  apply(subst ubtake_ind_alt2, simp_all)
  using ubTakeLen ubtake_ind_alt2
  by auto

subsection{* final bundle inductions *}

lemma finind_ub_alt:
  "\<lbrakk>ubLen x = Fin n; 
    \<And>ub. (ubDom\<cdot>ub = ubDom\<cdot>x \<and> (\<exists>c\<in>ubDom\<cdot>x. ub . c = \<bottom>)) \<Longrightarrow> P ub;
    \<And>u ub. (P ub \<and> ubDom\<cdot>u = ubDom\<cdot>x \<and> ubDom\<cdot>ub = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) u \<and> (\<forall>c\<in>ubDom\<cdot>u. u . c \<noteq> \<bottom>)) \<Longrightarrow> P (ubConc u\<cdot>ub)\<rbrakk>
    \<Longrightarrow> P x"
  by(subst ubtake_ind_alt2, auto)

lemma finind_sbe:
 "\<lbrakk>ubLen x = Fin n;
  \<And>ub. (ubDom\<cdot>ub = ubDom\<cdot>x \<Longrightarrow> (\<exists>c\<in>ubDom\<cdot>x. ub . c = \<bottom>)) \<Longrightarrow> P ub;
  \<And>sbe ub. P ub \<Longrightarrow> sbeDom sbe = ubDom\<cdot>x \<Longrightarrow> ubDom\<cdot>ub = ubDom\<cdot>x \<Longrightarrow> P (ubConcEq (sbe2SB sbe)\<cdot>ub)\<rbrakk>
  \<Longrightarrow> P x"
  apply(subst ubtake_ind_alt2, auto)
  by (smt Fin_neq_inf One_nat_def conceq_conc_1 leI one_lnat_def order_refl sbe_obtain ubHdLen_one 
          ubLen_def ubclDom_ubundle_def ubconc_sbhdrt ubconc_ubleast ubhd_ubdom ublen_min_on_channel 
          ubmaxlen_least_only ubmaxlen_sbrt_sbhd ubrt_ubdom usclLen_zero)

lemma ind_ub_alt:
  "\<lbrakk>ubDom\<cdot>x \<noteq> {};
    adm P;
    \<And>ub. (ubDom\<cdot>ub = ubDom\<cdot>x \<and> (\<exists>c\<in>ubDom\<cdot>x. ub . c = \<bottom>)) \<Longrightarrow> P ub;
    \<And>u ub. P ub \<and> ubDom\<cdot>ub = ubDom\<cdot>x \<and> ubDom\<cdot>u = ubDom\<cdot>x \<and> ubMaxLen (Fin 1) u \<and> (\<forall>c\<in>ubDom\<cdot>x. u . c \<noteq> \<bottom>) \<Longrightarrow> P (ubConcEq u\<cdot>ub)\<rbrakk>
  \<Longrightarrow> P x"
 apply (unfold adm_def)
 apply (erule_tac x="\<lambda>i. ubTake i\<cdot>x" in allE)
 by(simp add: ubtake_ind_alt ubConcEq_def)

lemma ind_sbe:
  assumes "adm P" 
  and     "ubDom\<cdot>x \<noteq> {}"
  and     "\<And>ub. (ubDom\<cdot>ub = ubDom\<cdot>x \<Longrightarrow> (\<exists>c\<in>ubDom\<cdot>x. ub . c = \<bottom>)) \<Longrightarrow> P ub"
  and     "\<And>sbe ub. P ub \<Longrightarrow> sbeDom sbe = ubDom\<cdot>x \<Longrightarrow> ubDom\<cdot>ub = ubDom\<cdot>x \<Longrightarrow> P (ubConcEq (sbe2SB sbe)\<cdot>ub)"
shows     "P x"
  apply(rule ind_ub_alt)
  apply (simp add: assms)
  apply (simp add: assms)
  apply (simp add: assms)
  by (metis (no_types, lifting) assms  ublen_not_0 usclLen_bot one_lnat_def sbe_obtain ubLen_def 
      ublen_min_on_channel ubundle_ubgetch_uscllen_one)                       



end