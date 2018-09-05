(* Dummy for KnasterTarski proof over cpo/pcpo *)

theory KnasterTarski

imports LongChain

begin

default_sort po


lemma Zorns_po_lemma:
  assumes po: "Partial_order r"
    and u: "\<forall>C\<in>Chains r. \<exists>u\<in>Field r. \<forall>a\<in>C. (a, u) \<in> r"
  shows "\<exists>m\<in>Field r. \<forall>a\<in>Field r. (m, a) \<in> r \<longrightarrow> a = m"
  oops

context po
begin
  lemma po_subfield: "Field {(x,y) | x y. x\<sqsubseteq>y \<and> x\<in>S \<and> y\<in>S} = S"
    apply(simp add: Field_def)
    apply(rule)
    by blast+
  
  lemma po2partial_order: "Partial_order {(x,y) | x y. x\<sqsubseteq>y \<and> x\<in>S \<and> y\<in>S}"
    apply(simp add: partial_order_on_def, rule)
     apply(simp add: preorder_on_def, rule)
    using Field_def refl_on_def apply fastforce
    apply (smt CollectD CollectI local.rev_below_trans split_conv transI)
    using antisym_def local.below_antisym by fastforce

lemma po_chain_total: assumes "chain K" shows "K a \<sqsubseteq> K b  \<or>  K b \<sqsubseteq> K a"
  using assms local.chain_mono nat_le_linear by blast


(* Zorn lemma über über-abzählbaren ketten *)
  lemma own_zorn2: 
    assumes "\<And>C. C\<in>Chains {(x,y) | x y. x\<sqsubseteq>y \<and>x\<in>S \<and> y\<in>S} \<Longrightarrow> \<exists>u\<in>S. \<forall>a\<in>C. a \<sqsubseteq> u"
  shows "\<exists>m\<in>S. \<forall>a\<in>S. (m\<sqsubseteq>a \<longrightarrow> a=m)"
  proof -
   let ?r = "{(x,y) | x y. x\<sqsubseteq>y \<and>x\<in>S \<and> y\<in>S}"
    have po: "Partial_order ?r"
      using po2partial_order by blast

    have "\<forall>C\<in>Chains ?r. \<exists>u\<in>Field ?r. \<forall>a\<in>C. (a, u) \<in> ?r" 
      apply(subst po_subfield)
      by (smt Chains_def CollectD CollectI Pair_inject assms)
    hence "\<exists>m\<in>Field ?r. \<forall>a\<in>Field ?r. (m, a) \<in> ?r \<longrightarrow> a = m"
      by (metis (no_types, lifting) Zorns_po_lemma po)
    thus ?thesis
      by (smt DomainE Domain_unfold Field_def Range_def Range_iff Un_iff mem_Collect_eq snd_conv)
  qed

  lemma own_zorn3: 
    assumes "\<And>C. longChain C \<Longrightarrow> C\<noteq>{} \<Longrightarrow> C\<subseteq>S \<Longrightarrow> \<exists>u\<in>S. \<forall>a\<in>C. a \<sqsubseteq> u" and "S\<noteq>{}"
    shows "\<exists>m\<in>S. \<forall>a\<in>S. (m\<sqsubseteq>a \<longrightarrow> a=m)"
  proof -
    have "\<forall>C. (C\<in>Chains {(x,y) | x y. x\<sqsubseteq>y \<and>x\<in>S \<and> y\<in>S} \<longrightarrow> (\<exists>u\<in>S. \<forall>a\<in>C. a \<sqsubseteq> u))"
      using assms  by (auto simp add: longChain_def Chains_def) 
    thus ?thesis 
      using po_class.own_zorn2 by blast
  qed

end



(* Proof follows closely the proof from Greber, see "SA_Greber" *)
lemma knaster_tarski: fixes f :: "'a::po \<Rightarrow>'a"
  assumes monof: "monofun f" 
    and goodf: "\<And>a. a\<in>C \<Longrightarrow> f a\<in>C" 
    and cpo: "\<And>S. longChain S \<Longrightarrow> S\<noteq>{} \<Longrightarrow> S\<subseteq>C \<Longrightarrow> \<exists>x\<in>C. S <<| x"
    and pcpo: "\<exists>bot\<in>C. \<forall>b\<in>C. bot \<sqsubseteq>b"
  shows "\<exists>!x. f x = x \<and> x\<in>C \<and> (\<forall>y\<in>C. f y = y \<longrightarrow> x\<sqsubseteq>y)" (is "\<exists>!x. ?P x")
proof -
  let ?F = "{x. x = f x \<and> x\<in>C}"  (* Set of all fixpoints in the division *)
  let ?Z = "{y. y \<sqsubseteq> f y \<and> (\<forall>x\<in>?F. y\<sqsubseteq>x) \<and> y \<in>C}"

  (* Teil A *)
  obtain bot where bot_bot: "\<And>c. c\<in>C \<Longrightarrow> bot\<sqsubseteq>c" and bot_c: "bot\<in>C" 
    by (meson assms(3) pcpo)
  have z_bot: "bot \<in> ?Z"
  proof -
    have "f bot \<in> C"
      using bot_c goodf by blast
    thus ?thesis
      using bot_bot bot_c by auto
  qed

  let ?r = "{(x,y) | x y. x\<sqsubseteq>y \<and>x\<in>?Z \<and> y\<in>?Z}"

  have lub_in_z: "\<And>S. longChain S \<Longrightarrow> S\<noteq>{} \<Longrightarrow> S \<subseteq> ?Z \<Longrightarrow> lub S \<in> ?Z"
  proof
    fix S
    assume s_chain: "longChain S" and s_empty: "S\<noteq>{}" and s_in: "S \<subseteq> ?Z"
    have "\<And>s x. s\<in>S \<Longrightarrow> x\<in>?F \<Longrightarrow> s\<sqsubseteq>x"
      using s_in by auto
    hence lub_f:"\<And>x. x\<in>?F \<Longrightarrow> lub S \<sqsubseteq> x"
      using cpo s_empty is_lub_thelub_ex is_ub_def s_chain s_in by fastforce

    let ?Kr = "f`S"
    have kr_chain: "longChain ?Kr"
      using longchain_mono monof s_chain by blast
    hence "lub S \<sqsubseteq> f (lub S)"
    proof -
      have "\<And>s. s\<in>S \<Longrightarrow> \<exists>x\<in>?Kr. s\<sqsubseteq>x"
        using s_in by auto
      hence f1: "\<And>s. s\<in>S \<Longrightarrow> s  \<sqsubseteq> lub ?Kr"
        by (smt Ball_Collect goodf holmf_below_lub image_is_empty image_subsetI kr_chain local.cpo s_empty s_in)
(*      using s_in holmf_below_lub by (smt Ball_Collect \<open>longChain (f ` S)\<close> c_cpo goodf image_subset_iff)  (* ToDo: kein SMT/schneller *) *)
      hence "lub S \<sqsubseteq> (lub ?Kr)"
        by (metis (mono_tags) Collect_mem_eq cpo s_empty conj_subset_def is_lub_thelub_ex is_ub_def s_chain s_in)
      hence "lub ?Kr  \<sqsubseteq> f (lub S)"  using s_chain kr_chain assms(1) is_ub_thelub lub_below_iff holmf_below_iff monofunE 
        by (smt Ball_Collect below_refl goodf image_iff image_is_empty local.cpo s_empty s_in subsetI) 
     (*   by (smt Ball_Collect s_empty cpo goodf imageE is_ub_thelub_ex s_in subsetI) (* ToDo kein SMT/schneller *) *)

      thus ?thesis using \<open>lub S \<sqsubseteq> lub (f ` S)\<close> rev_below_trans by blast
    qed
    
    moreover have "lub S \<in> C"
      using cpo s_empty lub_eqI s_chain s_in by blast 
    ultimately show "lub S \<sqsubseteq> f (lub S) \<and> (\<forall>x\<in>{x. x = f x \<and> x \<in> C}. lub S \<sqsubseteq> x) \<and> lub S \<in> C" using lub_f by blast
  qed
  have "\<And>C x. longChain C \<Longrightarrow> C\<noteq>{}\<Longrightarrow>C\<subseteq>?Z \<Longrightarrow> \<forall>a\<in>C. a\<sqsubseteq>lub C"
    by (metis (no_types, lifting) Ball_Collect  cpo is_ub_thelub_ex subset_iff)
  hence "\<And>C. longChain C \<Longrightarrow> C\<noteq>{}\<Longrightarrow>C\<subseteq>?Z \<Longrightarrow> \<exists>u\<in>?Z. \<forall>a\<in>C. a \<sqsubseteq> u"
    by (metis (no_types, lifting) lub_in_z)

  hence "\<exists>m\<in>?Z. \<forall>a\<in>?Z. (m\<sqsubseteq>a \<longrightarrow> a=m)" using bot_bot z_bot by(subst own_zorn3, auto)

  from this obtain w where w_def: "\<And>z. z\<in>?Z \<Longrightarrow> w \<sqsubseteq> z \<Longrightarrow> w = z" and w_z: "w\<in>?Z"
    by auto

  (* D *)
    (* 1. *)
  hence w_least: "\<And>x. x\<in>?F \<Longrightarrow>  w\<sqsubseteq>x"
    by blast

    (* 2. *)
  hence "\<And>x. x\<in>?F \<Longrightarrow> (f w) \<sqsubseteq> x"
    using monof monofunE by fastforce

  hence w_in:"f w \<in> ?Z"
    using goodf monof monofun_def w_z by fastforce

  hence w_fix: "f w = w"
    using w_def w_z by fastforce

  have "?P w"
    using w_fix w_z by auto    
  moreover hence "\<And>x. ?P x \<Longrightarrow> x = w"
    by (simp add: po_eq_conv)
  ultimately show ?thesis
    by metis
qed


end