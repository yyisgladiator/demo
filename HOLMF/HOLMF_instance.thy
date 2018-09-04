theory HOLMF_instance

imports  Division

begin


default_sort po


definition setify::"('m::type \<Rightarrow> ('n::type set)) \<Rightarrow> ('m \<Rightarrow> 'n) set" where
"setify = undefined"


definition test::"'b::type set set \<Rightarrow> (('a::type \<Rightarrow> ('b set)) set)" where
"test Ab = setify (\<lambda>a. Ab)"

instantiation "fun" :: (type, div_cpo) div_cpo
begin
  definition DIV_fun_def: "DIV_fun \<equiv> (setify ` (test DIV))::('a \<Rightarrow> 'b) set set"    (* TODO ! for nda_h *)

instance 
  apply(intro_classes)
  sorry
end












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


instantiation uspec:: (ufuncl) ppcpo
begin
definition A_uspec_def: "A_uspec \<equiv> { USPEC In Out | In Out . True  }"
instance
  sorry

end


end