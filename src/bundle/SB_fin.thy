theory SB_fin

imports SB
begin
declare[[show_types]]

section\<open>default sort finite and chan\<close>
default_sort "{finite,chan}"

section\<open> SB functions with finite type \<close>

subsection \<open>Cont version of sbHdElem\_h\<close>

lift_definition sbHdElem_h_cont::"'c\<^sup>\<Omega> \<rightarrow> ('c\<^sup>\<surd>) u"is 
"sbHdElem_h"
  apply(simp add: sbHdElem_h_def cfun_def)
  apply(intro cont2cont)
  apply(rule Cont.contI2)
   apply(rule monofunI)
  apply auto[1]
  apply (metis minimal monofun_cfun_arg po_eq_conv)
   apply (meson below_shd monofun_cfun_arg)
proof-
  fix Y::"nat \<Rightarrow> 'c\<^sup>\<Omega>"
  assume ch1:"chain Y"
  assume ch2:"chain (\<lambda>i::nat. if \<exists>c::'c. Y i  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y i  \<^enum>  c)))))"
  have "\<exists>c::'c. (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon> \<Longrightarrow> \<exists>c::'c. \<forall>i. (Y i)  \<^enum>  c = \<epsilon>"
    by (metis ch1 is_ub_thelub minimal monofun_cfun_arg po_eq_conv)
  have "adm (\<lambda>sb::'c\<^sup>\<Omega>. \<exists>c::'c. sb \<^enum> c= \<epsilon>)" (*Similar proof in spfstep.thy (automaton project)*)
  proof(rule admI)
    fix Y::"nat \<Rightarrow> 'c\<^sup>\<Omega>"
    assume chain:"chain Y"
    assume epsholds:"\<forall>i::nat. \<exists>c::'c. Y i  \<^enum>  c = \<epsilon>"
    then have h0:"\<forall>c i. ((Y i) \<^enum> c \<noteq> \<epsilon>) \<longrightarrow> ((\<Squnion>i::nat. Y i)  \<^enum>  c \<noteq> \<epsilon>)"
      by (metis (full_types) chain is_ub_thelub minimal monofun_cfun_arg po_eq_conv)
    then obtain set_not_eps where set_not_eps_def:"set_not_eps = {c::'c. \<exists>i. Y i \<^enum> c \<noteq> \<epsilon>}" 
      by simp
    then have "finite set_not_eps"
      by simp
    then have "finite (UNIV - set_not_eps)"
      by simp
    have h1:"\<forall>c\<in>(UNIV - set_not_eps). (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon>"
      by (simp add: chain contlub_cfun_arg set_not_eps_def)
    have h2:"\<forall>c\<in>(set_not_eps). (\<Squnion>i::nat. Y i)  \<^enum>  c \<noteq> \<epsilon>"
      using h0 set_not_eps_def by auto
    have "set_not_eps \<noteq> UNIV"
      apply(simp add: set_not_eps_def) 
      sorry
    then show "\<exists>c::'c. (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon>"
      using h1 by blast
  qed
  then have "\<forall>i::nat. \<exists>c::'c. Y i  \<^enum>  c = \<epsilon> \<Longrightarrow> \<exists>c::'c. (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon>"
    apply(rule admD)
    by(simp_all add: ch1)
  then have finiteIn:"\<forall>c::'c. (\<Squnion>i::nat. Y i)  \<^enum>  c \<noteq> \<epsilon> \<Longrightarrow> \<exists>i. \<forall>c::'c. (Y i) \<^enum> c \<noteq> \<epsilon>"
    by blast
  then show "(if \<exists>c::'c. (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd ((\<Squnion>i::nat. Y i)  \<^enum>  c))))) \<sqsubseteq>
       (\<Squnion>i::nat. if \<exists>c::'c. Y i  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y i  \<^enum>  c)))))"
  proof(cases "\<exists>c::'c. (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon>")
    case True
    then show ?thesis
      by simp
  next
    case False
    have ch3:"\<And>c. chain (\<lambda>i. Y i  \<^enum>  c)"
      by (simp add: ch1)
    obtain n where n_def:"\<forall>c::'c. (Y n) \<^enum> c \<noteq> \<epsilon>"
      using False finiteIn by auto
    then have shd_eq:"\<And>i. i\<ge>n \<Longrightarrow> (\<lambda>c::'c. shd (Y i  \<^enum>  c)) = (\<lambda>c::'c. shd (Y n  \<^enum>  c))"
      apply(subst fun_eq_iff)
      apply auto
      apply(rule below_shd_alt,auto)
      by (simp add: ch1 monofun_cfun_arg po_class.chain_mono)
    have h1:"\<forall>i\<ge>n. (if \<exists>c::'c. Y i  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y i  \<^enum>  c))))) 
                = Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y n  \<^enum>  c))))"
      apply(auto)
      apply (metis ch1 minimal monofun_cfun_arg n_def po_class.chain_mono po_eq_conv)
      using shd_eq by presburger
    have h2:"(if \<exists>c::'c. (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd ((\<Squnion>i::nat. Y i)  \<^enum>  c))))) \<sqsubseteq> Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y n  \<^enum>  c))))"
      apply(simp add: False)
      by (metis below_shd ch1 is_ub_thelub monofun_cfun_arg n_def)
    have h3:"(if \<exists>c::'c. Y n  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y n  \<^enum>  c))))) \<sqsubseteq> (\<Squnion>i::nat. if \<exists>c::'c. Y i  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y i  \<^enum>  c)))))"
      using below_lub ch2 by blast
    have h3_h:"(if \<exists>c::'c. Y n  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y n  \<^enum>  c))))) = Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y n  \<^enum>  c))))"
      by(simp add: n_def)
    then show ?thesis
      using h2 h3 by auto
  qed
qed

subsection\<open>sb\_cases definition\<close>

definition sb_case::"'cs\<^sup>\<Omega> \<rightarrow> ('cs\<^sup>\<surd> \<rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'a::pcpo) \<rightarrow> 'a" where
"sb_case = (\<Lambda> sb k. fup\<cdot>(\<Lambda> sbe. k\<cdot>sbe\<cdot>(sbRt\<cdot>sb))\<cdot>(sbHdElem_h_cont\<cdot>sb))"

lemma sb_case_cont:"cont (\<lambda>sb. \<Lambda> k. fup\<cdot>(\<Lambda> sbe. k\<cdot>sbe\<cdot>(sbRt\<cdot>sb))\<cdot>(sbHdElem_h_cont\<cdot>sb))"
  by simp


lemma sb_cases_bot:"\<not>(range(Rep::'c\<Rightarrow> channel)\<subseteq>cEmpty) \<Longrightarrow> sb_case\<cdot>\<bottom>\<cdot>f = \<bottom>"
  oops

lemma sb_cases_sbe:"sb_case\<cdot>(sbECons\<cdot>sbe\<cdot>sb)\<cdot>f = f\<cdot>sbe\<cdot>sb"
  oops
(*
lemma sb_case_inj1:"inj (Rep_cfun (sb_case\<cdot>sb))"
proof(rule injI)
  fix x y::"'a\<^sup>\<surd> \<rightarrow> 'a\<^sup>\<Omega> \<rightarrow> 'b"
  assume sb_case_eq:"sb_case\<cdot>sb\<cdot>x = sb_case\<cdot>sb\<cdot>y"
  have "\<And>xa. x\<cdot>xa = y\<cdot>xa"
    sorry
  then show "x = y"
    by(simp add: cfun_eqI)
  oops

lemma sb_case_inj2:"inj (Rep_cfun sb_case)"
  oops
*)
(*
subsection\<open>cont version of sbLen\<close>

definition sbLen_alt:: "'cs\<^sup>\<Omega> \<rightarrow> lnat" where
"sbLen_alt = (fix\<cdot>(\<Lambda> h sb. sb_case\<cdot>sb\<cdot>(\<Lambda> sbe sb2 . lnsuc\<cdot>(h\<cdot>sb2))))"

subsubsection\<open>sbLen\_alt lemmas\<close>

lemma sblen_alt_empty:"(range(Rep::'c\<Rightarrow> channel)\<subseteq>cEmpty) \<Longrightarrow> sbLen_alt\<cdot>(\<bottom>::'c\<^sup>\<Omega>) = \<infinity>"
  oops

lemma sblen_alt_bot:"sbLen_alt\<cdot>(\<bottom>::'cs\<^sup>\<Omega>) = \<infinity> \<or> sbLen_alt\<cdot>(\<bottom>::'cs\<^sup>\<Omega>) = 0"
  oops

lemma sblen_alt_step:"sbLen_alt\<cdot>(sbECons\<cdot>sbe\<cdot>sb) = lnsuc\<cdot>(sbLen_alt\<cdot>sb)"
  oops

lemma sblen_alt_insert2:" sbLen_alt\<cdot>sb = sbLen sb"
  oops

lemma sblen_alt_sbeqI:"x \<sqsubseteq> y \<Longrightarrow> sbLen_alt\<cdot>x = \<infinity> \<Longrightarrow> x = y"
  oops
*)
end