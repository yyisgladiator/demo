theory HOLMF_instance

imports  Division inc.SetPcpo spec.SetRev spec.USpec

begin


default_sort po


(* ToDo: make cont/move the SetPcpo *)
definition setify::"('m::type \<Rightarrow> ('n::type set)) \<Rightarrow> ('m \<Rightarrow> 'n) set" where
"setify \<equiv> \<lambda> f. {g. \<forall>m. g m \<in> (f m)}"

instantiation "fun" :: (type, div_cpo) div_cpo
begin
  definition DIV_fun_def: "DIV_fun \<equiv> (setify ` (setify (\<lambda>a. DIV)))::('a \<Rightarrow> 'b) set set"    (* TODO ! for nda_h *)


lemma fixes S::"('s::type \<Rightarrow> 'p::div_cpo) set"
  assumes "D\<in>DIV" and "S\<subseteq>D" and "S\<noteq>{}"
  shows "S <<| (\<lambda>a. lub {s a | s. s\<in>S})"
proof(rule is_lubI)
  have "\<And>a. \<exists>d\<in>DIV. {s a | s. s\<in>S} \<subseteq> d" sorry
  hence "\<And>a s. s\<in>S \<Longrightarrow> s a \<sqsubseteq> lub {ss a | ss. ss\<in>S}" oops

instance 
  apply(intro_classes)
  sorry
end







text {* The least upper bound on sets corresponds to the @{text "Intersection"} operator. *}
lemma setrev_inter_lub: "A <<| Rev (\<Inter> ((inv Rev) ` A))"
apply (simp add: is_lub_def)
apply (simp add: is_ub_def)
  by (simp add: INF_greatest INF_lower inv_rev_rev revBelowNeqSubset)


text {* Another needed variant of the fact that lub on sets corresponds to intersection. *}
lemma setrev_lub_eq_inter: "lub = (\<lambda>A. Rev (\<Inter> ((inv Rev) ` A)))"
apply (rule ext)
apply (rule lub_eqI [OF setrev_inter_lub])
done


lemma uspec_dom[simp]: "s\<in>USPEC In Out \<Longrightarrow> uspecDom\<cdot>s = In"
  using uspecdom_eq uspecleast_least by fastforce


lemma uspec_ran[simp]: "s\<in>USPEC In Out \<Longrightarrow> uspecRan\<cdot>s= Out"
  using uspecleast_least uspecran_eq by fastforce

lemma uspec_ub: "S\<noteq>{} \<Longrightarrow>S \<subseteq> USPEC In Out \<Longrightarrow> S <| x \<Longrightarrow> x\<in>USPEC In Out"
  unfolding USPEC_def
  unfolding is_ub_def
  by (metis (mono_tags, lifting) bot.extremum_uniqueI contra_subsetD mem_Collect_eq subset_emptyI uspecdom_eq uspecran_eq)

lemma uspec_cpo: assumes  "S \<subseteq> USPEC In Out" and "S\<noteq>{}"
  shows "\<exists>x\<in>USPEC In Out. S <<| x"
proof -
  let ?A = "(Rep_rev_uspec ` S)"
  let ?lub = "(Rev (\<Inter>?A), Discr In, Discr Out)"
  have "\<And>a. a\<in>(\<Inter>?A) \<Longrightarrow> ufclDom\<cdot>a = In"
    by (metis (mono_tags) INT_E assms(1) assms(2) contra_subsetD ex_in_conv uspec_allDom uspec_dom uspecrevset_insert)
  moreover have "\<And>a. a\<in>(\<Inter>?A) \<Longrightarrow> ufclRan\<cdot>a = Out"
    using assms(1) assms(2) rep_rev_revset uspec_allRan by fastforce
  ultimately have "uspecWell (Rev (\<Inter>?A)) (Discr In) (Discr Out)" by(simp)
  hence lub_rep_abs: "Rep_uspec (Abs_uspec ?lub) = ?lub"
    using rep_abs_uspec by blast
  have "\<And>s. s\<in>S \<Longrightarrow> s\<sqsubseteq>(Abs_uspec ?lub)"
    apply(rule uspec_belowI)
    apply(simp_all add: uspecdom_insert uspecran_insert lub_rep_abs uspecrevset_insert)
    using assms uspec_dom uspecdom_insert apply fastforce
    using assms uspec_ran uspecran_insert apply fastforce
    by (metis INF_lower inv_rev_rev revBelowNeqSubset)
  hence "S <| Abs_uspec ?lub"
    using is_ubI by blast
  moreover have "\<And>u. S <| u \<Longrightarrow> (Abs_uspec ?lub) \<sqsubseteq> u"
    apply(rule uspec_belowI)
    apply(simp_all add: uspecdom_insert uspecran_insert lub_rep_abs uspecrevset_insert)
    apply (metis assms(1) assms(2) uspec_dom uspec_ub uspecdom_insert)
    apply (metis (full_types) assms(1) assms(2) uspec_ran uspec_ub uspecran_insert)
    by (metis (no_types, lifting) INF_greatest fst_monofun inv_rev_rev is_ubD rep_uspec_belowI revBelowNeqSubset)
  ultimately show ?thesis
    using assms is_lubI uspec_ub by blast
qed


lemma uspec_chain_field: assumes "longChain S"
  and "a\<in>S" and "b\<in>S"
shows "uspecDom\<cdot>a = uspecDom\<cdot>b" and "uspecRan\<cdot>a = uspecRan\<cdot>b"
  using assms(1) assms(2) assms(3) longChain_def uspecdom_eq apply blast
  by (metis (no_types) assms(1) assms(2) assms(3) longChain_def uspecran_eq)

lemma uspec_chain_field2: assumes "longChain S" 
  shows "\<exists>In Out. S \<subseteq> USPEC In Out"
  apply(cases "S={}")
  apply simp
proof (rule ccontr)
  assume "S\<noteq>{}" and "\<nexists>(In::channel set) Out::channel set. S \<subseteq> USPEC In Out"
  from this obtain a b where "a\<in>S" and "b\<in>S" and "uspecDom\<cdot>a\<noteq>uspecDom\<cdot>b \<or> uspecRan\<cdot>a\<noteq>uspecRan\<cdot>b"
    by (smt USPEC_def assms mem_Collect_eq order_refl subsetI subset_emptyI uspec_chain_field(1) uspec_chain_field(2))
  thus False
    by (meson assms(1) uspec_chain_field(1) uspec_chain_field(2)) 
qed

lemma uspec_cpo2: fixes S :: "'m::ufuncl uspec set"
  assumes "longChain S" and  "S\<noteq>{}"
  shows "\<exists>x. S <<| x"
  using assms(1) assms(2) uspec_chain_field2 uspec_cpo by blast


instantiation uspec:: (ufuncl) div_pcpo
begin
definition DIV_uspec_def: "DIV_uspec \<equiv> { USPEC In Out | In Out . True  }"
instance
  apply(intro_classes)
  apply(auto simp add: DIV_uspec_def)
  using uspec_cpo apply blast
  by (metis (mono_tags, lifting) USPEC_def mem_Collect_eq uspecleast_dom uspecleast_least uspecleast_ran)
end


end