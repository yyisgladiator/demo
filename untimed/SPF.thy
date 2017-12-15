theory SPF
  imports SB "../UFun_applyIn" UB_ToDo
begin
default_sort message

type_synonym 'm SPF = "'m SB \<Rrightarrow> 'm SB"

instance ubundle :: (uscl) ubcl_comp
  sorry

section \<open>Definitions with spfApplyIn\<close>

(* ToDo: make signature more general, output does not have to be an SB *)
definition spfRt :: "('m SB \<Rrightarrow> 'm SB) \<rightarrow> ('m SB \<Rrightarrow> 'm SB)" where
"spfRt \<equiv> ufApplyIn sbRt"

section \<open>Definitions with spfApplyOut\<close>

(* ToDo: make signature more general, input does not have to be an SB *)
definition spfConc :: "'m SB \<Rightarrow> 'm SPF \<rightarrow> 'm SPF" where
"spfConc sb = ufApplyOut (ubConcEq sb)"


subsection \<open>more general lemma\<close>

lemma spf_eq: assumes "ufDom\<cdot>uf1 = ufDom\<cdot>uf2"
  and "\<And>ub. ubDom\<cdot>ub = ufDom\<cdot>uf1 \<Longrightarrow> uf1 \<rightleftharpoons> ub = uf2 \<rightleftharpoons> ub"
shows "uf1 = uf2"
  by (metis assms(1) assms(2) ubDom_ubundle_def ufun_eqI)

lemma ufapply_in_out:
  assumes "\<And>sb. ubDom\<cdot>(f\<cdot>sb) =  ubDom\<cdot>sb"
      and "\<And>sb. ubDom\<cdot>(g\<cdot>sb) =  ubDom\<cdot>sb"
    shows  "ufApplyIn f\<cdot>(ufApplyOut g\<cdot>spf) = ufApplyOut g\<cdot>(ufApplyIn f\<cdot>spf)"
  apply(rule ufun_eqI)
  using assms by auto
  

subsection \<open>spfRt lemma\<close>
lemma spfrt_step[simp]: "(spfRt\<cdot>spf)\<rightleftharpoons>sb = spf\<rightleftharpoons>(sbRt\<cdot>sb)"
  by(simp add: spfRt_def)

subsection \<open>spfConc lemma\<close>
lemma spconc_step[simp]: 
  assumes "ubDom\<cdot>sb = ufDom\<cdot>spf"
  shows "(spfConc sb1\<cdot>spf)\<rightleftharpoons>sb = ubConcEq sb1\<cdot>(spf\<rightleftharpoons>sb)"
  by(simp add: spfConc_def assms)





end