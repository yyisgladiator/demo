theory Division

imports LongChain

begin
default_sort po



class division =
  fixes DIV :: "'a set set"
begin
end

class div_cpo = division + po + 
 (*  assumes p0: "DIV \<noteq> {} "  (* A is not empty *)  *)

    (* Elements from different divisions are never in a below-relation *)
 (* assumes p2: "\<And>a b. a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> \<exists>aa bb. aa\<in>a \<and> bb\<in>b \<Longrightarrow> a = b" (* ToDo: Name + schöner aufschreiben *) *)

    (* every set is a cpo *)
  assumes div_cpo: "\<And>S a. a\<in>DIV \<Longrightarrow> \<not>finite S \<Longrightarrow> longChain S \<Longrightarrow> S\<subseteq>a \<Longrightarrow> \<exists>x\<in>a. S <<| x" (* ToDo: Name + schöner aufschreiben *)
begin

lemma div_cpo_g: "a\<in>DIV \<Longrightarrow> longChain S \<Longrightarrow> S\<subseteq>a \<Longrightarrow> \<exists>x\<in>a. S <<| x"
  apply(cases "finite S")
  apply (metis is_lub_maximal is_ubI lc_finite longChain_def subset_eq)
  by (simp add: local.div_cpo)

end

class div_pcpo = div_cpo +  
    (* every division has its own bottom element *)
  assumes div_pcpo: "\<And>a. a\<in>DIV \<Longrightarrow> \<exists>bot\<in>a. \<forall>b\<in>a. bot \<sqsubseteq>b"  (* ToDo: Name + schöner aufschreiben *)
begin
lemma div_pcpo_full: "\<And>a. a\<in>DIV \<Longrightarrow>  a\<noteq>{}"
  using local.div_pcpo by auto

end


end
