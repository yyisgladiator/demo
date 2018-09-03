theory HOLMF_instance

imports  KnasterTarski spec.USpec HOLMF

begin


default_sort ufuncl


definition USPEC :: "channel set \<Rightarrow> channel set \<Rightarrow> 'm uspec set" where
"USPEC In Out = {spec. uspecDom\<cdot>spec = In \<and> uspecRan\<cdot>spec = Out}"




lift_definition uspecLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> 'm uspec" is
"\<lambda>In Out. (Rev (Set.filter (\<lambda>x. ufclDom\<cdot>x = In \<and> ufclRan\<cdot>x=Out) UNIV), Discr In, Discr Out)"
  by simp

lemma uspecleast_dom[simp]: "uspecDom\<cdot>(uspecLeast In Out) = In"
  by (simp add: uspecdom_insert uspecLeast.rep_eq)

lemma uspecleast_ran[simp]: "uspecRan\<cdot>(uspecLeast In Out) = Out"
  by (simp add: uspecran_insert uspecLeast.rep_eq)

lemma uspecleast_least: assumes "spec \<in> USPEC In Out"
  shows "uspecLeast In Out \<sqsubseteq> spec"
  apply(rule uspec_belowI)
  apply (simp_all add: USPEC_def)
  using USPEC_def assms apply blast
  using USPEC_def assms apply force
  apply(simp add: uspecRevSet_def uspecLeast.rep_eq)
  by (metis (no_types, lifting) UNIV_I USPEC_def assms inv_rev_rev mem_Collect_eq member_filter revBelowNeqSubset subsetI uspec_allDom uspec_allRan uspecrevset_insert)





lift_definition uspecMax :: "channel set \<Rightarrow> channel set \<Rightarrow> 'm uspec" is
"\<lambda>In Out. (Rev {}, Discr In, Discr Out)"
  by simp


lemma uspecmax_dom[simp]: "uspecDom\<cdot>(uspecMax In Out) = In"
  by (simp add: uspecdom_insert uspecMax.rep_eq)

lemma uspecmax_ran[simp]: "uspecRan\<cdot>(uspecMax In Out) = Out"
  by (simp add: uspecran_insert uspecMax.rep_eq)

lemma uspecmax_max: assumes "spec \<in> USPEC In Out"
  shows "spec \<sqsubseteq> uspecMax In Out"
  apply(rule uspec_belowI)
  apply (metis (no_types) assms uspecdom_eq uspecleast_dom uspecleast_least uspecmax_dom)
  apply (metis (no_types) assms uspecleast_least uspecleast_ran uspecmax_ran uspecran_eq)
  by (simp add: inv_rev_rev revBelowNeqSubset uspecMax.rep_eq uspecrevset_insert)




lemma uspec_cpo: assumes "longChain S" and "S \<subseteq> USPEC In Out"
  shows "\<exists>x\<in>USPEC In Out. S <<| x"
  apply(simp add: is_lub_def)
  sorry


lemma uspec_chain_field: assumes "longChain S"
  and "a\<in>S" and "b\<in>S"
shows "uspecDom\<cdot>a = uspecDom\<cdot>b" and "uspecRan\<cdot>a = uspecRan\<cdot>b"
  using assms(1) assms(2) assms(3) longChain_def uspecdom_eq apply blast
  by (metis (no_types) assms(1) assms(2) assms(3) longChain_def uspecran_eq)

lemma uspec_chain_field2: assumes "longChain S"
  shows "\<exists>In Out. S \<subseteq> USPEC In Out"
  apply(rule ccontr)
  apply auto
  sorry

lemma uspec_cpo2: fixes S :: "'m uspec set"
  assumes "longChain S"
  shows "\<exists>x. S <<| x"
  by (metis (mono_tags) USPEC_def assms longChain_def lub_eqI mem_Collect_eq subsetI uspec_cpo)


definition setify::"('m::type \<Rightarrow> ('n::type set)) \<Rightarrow> ('m \<Rightarrow> 'n) set" where
"setify = undefined"


definition test::"'b::type set set \<Rightarrow> (('a::type \<Rightarrow> ('b set)) set)" where
"test Ab = setify (\<lambda>a. Ab)"

instantiation "fun" :: (type, ppcpo) ppcpo
begin
  definition A_fun_def: "A_fun \<equiv> (setify ` (test A))::('a \<Rightarrow> 'b) set set"    (* TODO ! for nda_h *)

instance 
  apply(intro_classes)
  sorry
end

instantiation uspec:: (ufuncl) ppcpo
begin
definition A_uspec_def: "A_uspec \<equiv> { USPEC In Out | In Out . True  }"
instance
  sorry

end


end