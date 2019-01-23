theory Division

imports LongChain inc.SetPcpo

begin
default_sort po



class division =
  fixes DIV :: "'a set set"

  assumes div_non_empty: "DIV \<noteq> {}"

  assumes div_inner_non_empty: "\<And>D. D\<in>DIV  \<Longrightarrow> D \<noteq> {}"

begin

end

class div_cpo = division + po + 




    (* every set is a cpo *)
  assumes div_cpo: "\<And>S D. D\<in>DIV \<Longrightarrow> \<not>finite S \<Longrightarrow> longChain S \<Longrightarrow> S\<subseteq>D \<Longrightarrow> \<exists>x\<in>D. S <<| x"
begin

lemma div_cpo_g: "a\<in>DIV \<Longrightarrow> longChain S \<Longrightarrow> S\<subseteq>a \<Longrightarrow> \<exists>x\<in>a. S <<| x"
  apply(cases "finite S")
  apply (metis is_lub_maximal is_ubI lc_finite longChain_def subset_eq)
  by (simp add: local.div_cpo)

lemma div_cpo_lub_in: "a\<in>DIV \<Longrightarrow> longChain S \<Longrightarrow> S\<subseteq>a \<Longrightarrow> lub S \<in> a"
  using div_cpo_g lub_eqI by blast

lemma div_cpo_lub_ub: "a\<in>DIV \<Longrightarrow> longChain S \<Longrightarrow> S\<subseteq>a \<Longrightarrow> x\<in>S \<Longrightarrow> x \<sqsubseteq> lub S"
  using div_cpo_g holmf_below_lub by blast

lemma div_cpo_lub_least: "C \<in> DIV \<Longrightarrow> longChain S \<Longrightarrow> S \<subseteq> C \<Longrightarrow> (\<And>y. y\<in>S \<Longrightarrow>  y \<sqsubseteq> a) \<Longrightarrow> lub S \<sqsubseteq> a"
  using div_cpo_g holmf_below_iff by blast

lemma div_cpo_adm_below: "C\<in>DIV \<Longrightarrow> longAdm C (\<lambda>x. x\<sqsubseteq>K)"
  by(auto simp add: longAdm_def div_cpo_lub_least)

lemma div_cpo_adm_less: "C\<in>DIV \<Longrightarrow> longAdm C (\<lambda>x. K\<sqsubseteq>x)"
  apply(auto simp add: longAdm_def div_cpo_lub_least)
  using div_cpo_g holmf_below_lub longChain_def by fastforce

lemma div_cpo_adm_below_mono: "C\<in>DIV \<Longrightarrow> monofun f \<Longrightarrow> longAdm C (\<lambda>x. K \<sqsubseteq> (f x))"
  apply(auto simp add: longAdm_def)
  by (metis bot.extremum_uniqueI div_cpo_g is_lubD1 is_ubD longChain_def lub_eqI monofun_def rev_below_trans subsetI)


end

class div_pcpo = div_cpo +  
    (* every division has its own bottom element *)
  assumes div_pcpo: "\<And>D. D\<in>DIV \<Longrightarrow> \<exists>bot\<in>D. \<forall>b\<in>D. bot \<sqsubseteq>b" 
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


lemma div_botI: assumes "\<And>x. x\<in>C \<Longrightarrow> y\<sqsubseteq>x" and "y\<in>C" and "C\<in>DIV"
  shows "y=div_bot C"
  by (simp add: assms(1) assms(2) assms(3) below_antisym div_bot)

end






end
