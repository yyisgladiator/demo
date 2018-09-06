theory Division

imports LongChain inc.SetPcpo

begin
default_sort po



class division =
  fixes DIV :: "'a set set"
begin
end

class div_cpo = division + po + 

  assumes div_non_empty: "DIV \<noteq> {}"

  assumes div_inner_non_empty: "\<And>a. a\<in>DIV  \<Longrightarrow> a \<noteq> {}"


    (* every set is a cpo *)
  assumes div_cpo: "\<And>S a. a\<in>DIV \<Longrightarrow> \<not>finite S \<Longrightarrow> longChain S \<Longrightarrow> S\<subseteq>a \<Longrightarrow> \<exists>x\<in>a. S <<| x"
begin

lemma div_cpo_g: "a\<in>DIV \<Longrightarrow> longChain S \<Longrightarrow> S\<subseteq>a \<Longrightarrow> \<exists>x\<in>a. S <<| x"
  apply(cases "finite S")
  apply (metis is_lub_maximal is_ubI lc_finite longChain_def subset_eq)
  by (simp add: local.div_cpo)

lemma div_cpo_lub_in: "a\<in>DIV \<Longrightarrow> longChain S \<Longrightarrow> S\<subseteq>a \<Longrightarrow> lub S \<in> a"
  using div_cpo_g lub_eqI by blast

end

class div_pcpo = div_cpo +  
    (* every division has its own bottom element *)
  assumes div_pcpo: "\<And>a. a\<in>DIV \<Longrightarrow> \<exists>bot\<in>a. \<forall>b\<in>a. bot \<sqsubseteq>b"  (* ToDo: Name + schöner aufschreiben *)
begin

definition div_bot::"'b::div_pcpo set \<Rightarrow> 'b" where
"div_bot C = (THE bott.  bott\<in>C \<and> (\<forall>x\<in>C. bott\<sqsubseteq>x))"

lemma div_pcpo_bott: assumes "C\<in>DIV" shows "\<exists>!bott. bott\<in>C \<and> (\<forall>x\<in>C. bott\<sqsubseteq>x)"
  by (meson assms local.div_pcpo po_eq_conv)

lemma div_bot: 
  fixes C ::"'b::div_pcpo set"
  assumes "C\<in>DIV" shows "(div_bot C)\<in>C \<and> (\<forall>x\<in>C. (div_bot C)\<sqsubseteq>x)"
  apply(simp add: div_bot_def)
  apply(rule theI' [of _ ])
  by (simp add: assms div_pcpo_class.div_pcpo_bott)

end







section \<open>fun div_cpo\<close>


instantiation "fun" :: (type, div_cpo) div_cpo
begin
definition DIV_fun:: "('s::type \<Rightarrow> 'm::div_cpo) set set" where
"DIV_fun = (setify ` (setify (\<lambda>a. DIV)))"   

lemma div_fun_s: fixes f g::"'s::type \<Rightarrow> 'm::div_cpo"
  assumes "D\<in>(DIV::('s \<Rightarrow> 'm) set set)" and "f\<in>D"
  shows "(\<exists>d2\<in>DIV::'m set set. f a\<in>d2)"
    using assms apply(simp add:  DIV_fun_def)
  unfolding DIV_fun_def
  by (smt setify_def bex_imageD mem_Collect_eq)

lemma div_fun_non_empty: "(DIV::('s::type \<Rightarrow> 'm::div_cpo) set set) \<noteq> {}"
  apply(simp add:  DIV_fun_def)
  apply(rule setify_notempty)
  by (simp add: div_non_empty)

lemma div_fun_non_empty2: "a\<in>(DIV::('s::type \<Rightarrow> 'm::div_cpo) set set) \<Longrightarrow> a \<noteq> {}"
  apply(simp add:  DIV_fun_def)
  by (smt setify_def setify_notempty div_inner_non_empty image_iff mem_Collect_eq)

lemma div_fun_s2: fixes f g::"'s::type \<Rightarrow> 'm::div_cpo"
  assumes "D\<in>(DIV::('s \<Rightarrow> 'm) set set)" and "f\<in>D" and "g\<in>D"
  shows "(\<exists>d2\<in>DIV::'m set set. f a\<in>d2 \<and> g a\<in>d2)"
  using assms apply(simp add: DIV_fun_def)
  by (smt setify_def image_iff mem_Collect_eq) 

lemma div_cpo_fun_chains: "longChain S \<Longrightarrow> longChain {s a | s. s\<in>S}"
apply(auto simp add: longChain_def)
  by (meson fun_belowD)

lemma div_cpo_fun_lub: fixes S::"('s::type \<Rightarrow> 'p::div_cpo) set"
  assumes "D\<in>DIV" and "S\<subseteq>D"  and "longChain S"
  shows "S <<| (\<lambda>a. lub {s a | s. s\<in>S})" and "(\<lambda>a. lub {s a | s. s\<in>S}) \<in> D"
proof -
  obtain DD where dd_def: "D = setify DD" and dd_in: "DD\<in>setify (\<lambda>a. DIV)"
    by (metis DIV_fun_def assms(1) imageE)
  hence "\<And>s a. s\<in>S \<Longrightarrow> s a \<in> DD a"
    by (metis (no_types, lifting) CollectD setify_def assms(2) set_mp)
  hence f1: "\<And>a. {s a | s. s\<in>S} \<subseteq> DD a"
    by (smt CollectD setify_def dd_in subsetI)

  moreover have dd_in_div: "\<And>a. DD a\<in>DIV"
    by (metis (mono_tags, lifting) setify_def dd_in mem_Collect_eq)
  moreover have chain: "\<And>a. longChain {s a | s. s\<in>S}"
    by (simp add: assms(3) div_cpo_fun_chains)
  ultimately have lub_in: "\<And>a. lub {s a | s. s\<in>S} \<in> DD a"
    by (simp add: div_cpo_lub_in)

 show "(\<lambda>a. lub {s a | s. s\<in>S}) \<in> D"
   by (simp add: setify_def dd_def lub_in)

  have s_lub: "\<And>a. {s a | s. s\<in>S} <<| lub {s a | s. s\<in>S}"
      using chain dd_in_div div_cpo_g f1 is_lub_lub by blast
    hence "S <| (\<lambda>a::'s. lub {s a |s::'s \<Rightarrow> 'p. s \<in> S})"
      by (smt below_fun_def is_lub_def is_ub_def mem_Collect_eq)
    moreover have "\<And>u::'s \<Rightarrow> 'p. S <| u \<Longrightarrow> (\<lambda>a::'s. lub {s a |s::'s \<Rightarrow> 'p. s \<in> S}) \<sqsubseteq> u"
    by (smt s_lub fun_belowD fun_belowI is_lub_below_iff is_ubD is_ubI mem_Collect_eq)
  ultimately show "S <<| (\<lambda>a. lub {s a | s. s\<in>S})"
    using is_lubI by blast
qed

instance 
  apply(intro_classes)
  apply (simp add: div_fun_non_empty)
  apply (simp add: div_fun_non_empty2)
  using div_cpo_fun_lub(1) div_cpo_fun_lub(2) by blast
end







section \<open>fun div_pcpo\<close>

instance "fun" :: (type, div_pcpo) div_pcpo
proof(intro_classes)
  fix a ::"('a::type \<Rightarrow> 'b::div_pcpo) set"
  assume "a\<in>DIV"
 from this obtain DD where dd_def: "a = setify DD" and dd_in: "DD\<in>setify (\<lambda>a. DIV)"
   by (metis DIV_fun_def imageE)  
  hence bot_exist: "\<And>s. \<exists>bot\<in>DD s. \<forall>b\<in>DD s. bot\<sqsubseteq>b"
    by (simp add: SetPcpo.setify_def div_pcpo)
  let ?bot = "\<lambda>s. SOME bot. (bot\<in>DD s \<and> (\<forall>b\<in>DD s. bot\<sqsubseteq>b))"
  have "?bot \<in> a"
    by (smt SetPcpo.setify_def bot_exist dd_def mem_Collect_eq someI_ex)
  moreover have "\<forall>b\<in>a. ?bot \<sqsubseteq> b" apply(simp add: below_fun_def, auto)
    by (smt SetPcpo.setify_def bot_exist dd_def mem_Collect_eq someI_ex)
  ultimately show "\<exists>bot\<in>a. \<forall>b\<in>a. bot \<sqsubseteq> b" by blast
qed







end
