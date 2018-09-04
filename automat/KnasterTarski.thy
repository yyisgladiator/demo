(* Dummy for KnasterTarski proof over cpo/pcpo *)

theory KnasterTarski

imports HOLCF HOLMF

begin

(* This is going to be problematic, we cannot use pcpo (because uspec is no pcpo) *)
default_sort cpo

class A_class = 
  fixes A :: "'a set set" (* Rename: Division *)
begin
end

class ppcpo = A_class +  cpo + 
  assumes p0: "A \<noteq> {} "  (* A is not empty *) 
  (* assumes "setflat\<cdot>A = UNIV" *)

    (* every division has its own bottom element *)
  assumes p1: "\<And>a. a\<in>A \<Longrightarrow> \<exists>bot\<in>a. \<forall>b\<in>a. bot \<sqsubseteq>b"  (* ToDo: Name + schöner aufschreiben *)

    (* Elements from different divisions are never in a below-relation *)
 (* assumes p2: "\<And>a b. a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> \<exists>aa bb. aa\<in>a \<and> bb\<in>b \<Longrightarrow> a = b" (* ToDo: Name + schöner aufschreiben *) *)

    (* every set is a cpo *)
  assumes p3: "\<And>S a. a\<in>A \<Longrightarrow> longChain S \<Longrightarrow> S\<subseteq>a \<Longrightarrow> \<exists>x\<in>a. S <<| x" (* ToDo: Name + schöner aufschreiben *)
begin

end

(*
class pcpo_A = pcpo + A_class +
  assumes A_def: "A = {UNIV}"
begin
end

subclass (in pcpo_A) ppcpo
proof
  show "A \<noteq> {}"
    by (simp add: local.A_def)
  show "A \<noteq> { {} }"
    by (simp add: local.A_def)
  have "\<And>b. \<bottom> \<sqsubseteq> b" sorry      (* WHY WHY WHYYYY ?  *)
  show "\<And>a. a \<in> A \<Longrightarrow> \<exists>bot\<in>a. \<forall>b\<in>a. bot \<sqsubseteq> b"
    apply (simp only: local.A_def)
    oops

  show "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> \<exists>aa bb. aa \<in> a \<and> bb \<in> b \<Longrightarrow> a = b" oops
  show "\<And>K i a. a \<in> A \<Longrightarrow> chain K \<Longrightarrow> K i \<in> a \<Longrightarrow> (\<Squnion>i. K i) \<in> a " oops
*)



(* There exists a division in which f is complete *)
definition goodFormed :: "('a::ppcpo \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where
"goodFormed f C \<equiv> \<forall>aa\<in>C. f aa \<in>C"



(* ToDo: add LEAST condition *)
definition lfp:: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
"lfp f = (SOME x. f x = x)"



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

  lemma chains2longchains: 
    shows "Chains {(x,y) | x y. x\<sqsubseteq>y \<and>x\<in>S \<and> y\<in>S} = {C. longChain C\<and>C\<subseteq>S}"
    apply rule+
    by(auto simp add: Chains_def longChain_def)

  lemma own_zorn3: 
    assumes "\<And>C. longChain C \<Longrightarrow> C\<subseteq>S \<Longrightarrow> \<exists>u\<in>S. \<forall>a\<in>C. a \<sqsubseteq> u"
    shows "\<exists>m\<in>S. \<forall>a\<in>S. (m\<sqsubseteq>a \<longrightarrow> a=m)"
  proof -
    have "\<forall>C. (C\<in>Chains {(x,y) | x y. x\<sqsubseteq>y \<and>x\<in>S \<and> y\<in>S} \<longrightarrow> (\<exists>u\<in>S. \<forall>a\<in>C. a \<sqsubseteq> u))"
      using assms chains2longchains by blast
    thus ?thesis 
      using po_class.own_zorn2 by blast
  qed

(* Zorn lemma über abzählbare ketten *)
  lemma own_zorn: 
    assumes "\<And>C. chain C \<Longrightarrow> (\<forall>i. C i\<in>S) \<Longrightarrow> \<exists>a\<in>S. (\<forall>i. C i \<sqsubseteq> a)"
    and "S \<noteq> {}"  (* Delete assumption? *)
     shows "\<exists>m\<in>S. \<forall>a\<in>S. (m\<sqsubseteq>a \<longrightarrow> a=m)"
  proof -
    let ?r = "{(x,y) | x y. x\<sqsubseteq>y \<and>x\<in>S \<and> y\<in>S}"
    have "Partial_order ?r"
      using po2partial_order by blast

    moreover have "\<forall>C\<in>Chains ?r. \<exists>u\<in>S. \<forall>a\<in>C. a \<sqsubseteq> u" 
    proof -
      have "\<And>K.  chain K \<Longrightarrow> (\<forall>i. K i\<in>S) \<Longrightarrow> range K \<in> Chains ?r"
        by(auto simp add: Chains_def po_chain_total)
      have "\<And>C. C \<in> Chains ?r \<Longrightarrow> \<exists>K. chain K \<and> range K = C"
        sorry (* Gilt halt nicht ... oder? *)
      thus ?thesis sorry
    qed
    moreover hence "\<forall>C\<in>Chains ?r. \<exists>u\<in>Field ?r. \<forall>a\<in>C. (a, u) \<in> ?r" 
      apply(subst po_subfield)
      by (smt Chains_def CollectD CollectI Pair_inject)
    ultimately have "\<exists>m\<in>Field ?r. \<forall>a\<in>Field ?r. (m, a) \<in> ?r \<longrightarrow> a = m"
      by (metis (no_types, lifting) Zorns_po_lemma)
    thus ?thesis
      by (smt DomainE Domain_unfold Field_def Range_def Range_iff Un_iff mem_Collect_eq snd_conv)

    oops


end




section \<open>uncountable chains\<close>

(* Proof follows closely the proof from Greber, see "SA_Greber" *)
lemma own_knaster_tarski: fixes f :: "'a::ppcpo \<Rightarrow>'a"
  assumes monof: "monofun f" and goodf: "goodFormed f C" and "C \<in> A"
  shows "\<exists>x. f x = x \<and> x\<in>C" (* ToDo: add least condition *)
proof -
  let ?F = "{x. x = f x \<and> x\<in>C}"  (* Set of all fixpoints in the division *)
  let ?Z = "{y. y \<sqsubseteq> f y \<and> (\<forall>x\<in>?F. y\<sqsubseteq>x) \<and> y \<in>C}"

  (* Teil A *)
  obtain bot where bot_bot: "\<And>c. c\<in>C \<Longrightarrow> bot\<sqsubseteq>c" and bot_c: "bot\<in>C" 
    by (meson assms(3) p1)
  have z_bot: "bot \<in> ?Z"
  proof -
    have "f bot \<in> C"
      using bot_c goodFormed_def goodf by blast
    thus ?thesis
      using bot_bot bot_c by auto
  qed

  let ?r = "{(x,y) | x y. x\<sqsubseteq>y \<and>x\<in>?Z \<and> y\<in>?Z}"

  have c_cpo: "\<And>S. longChain S \<Longrightarrow> S \<subseteq> C \<Longrightarrow> \<exists>x\<in>C. S <<| x"
    by (simp add: assms(3) p3) (* CPO-condition *)

  have lub_in_z: "\<And>S. longChain S \<Longrightarrow> S \<subseteq> ?Z \<Longrightarrow> lub S \<in> ?Z"
  proof
    fix S
    assume s_chain: "longChain S" and s_in: "S \<subseteq> ?Z"
    have "\<And>s x. s\<in>S \<Longrightarrow> x\<in>?F \<Longrightarrow> s\<sqsubseteq>x"
      using s_in by auto
    hence lub_f:"\<And>x. x\<in>?F \<Longrightarrow> lub S \<sqsubseteq> x"
      using c_cpo is_lub_thelub_ex is_ub_def s_chain s_in by fastforce

    let ?Kr = "f`S"
    have kr_chain: "longChain ?Kr"
      using longchain_mono monof s_chain by blast
    hence "lub S \<sqsubseteq> f (lub S)"
    proof -
      have "\<And>s. s\<in>S \<Longrightarrow> \<exists>x\<in>?Kr. s\<sqsubseteq>x"
        using s_in by auto
      hence f1: "\<And>s. s\<in>S \<Longrightarrow> s  \<sqsubseteq> lub ?Kr"
      using s_in holmf_below_lub by (smt Ball_Collect \<open>longChain (f ` S)\<close> c_cpo goodFormed_def goodf image_subset_iff)  (* ToDo: kein SMT/schneller *)
      hence "lub S \<sqsubseteq> (lub ?Kr)"
        by (metis (mono_tags) Collect_mem_eq c_cpo conj_subset_def is_lub_thelub_ex is_ub_def s_chain s_in)
      hence "lub ?Kr  \<sqsubseteq> f (lub S)"  using s_chain kr_chain assms(1) is_ub_thelub lub_below_iff holmf_below_iff monofunE 
        by (smt Ball_Collect c_cpo goodFormed_def goodf imageE is_ub_thelub_ex s_in subsetI) (* ToDo kein SMT/schneller *)

      thus ?thesis using \<open>lub S \<sqsubseteq> lub (f ` S)\<close> rev_below_trans by blast
    qed
    
    moreover have "lub S \<in> C"
      using c_cpo lub_eqI s_chain s_in by blast 
    ultimately show "lub S \<sqsubseteq> f (lub S) \<and> (\<forall>x\<in>{x. x = f x \<and> x \<in> C}. lub S \<sqsubseteq> x) \<and> lub S \<in> C" using lub_f by blast
  qed
  have "\<And>C x. longChain C \<Longrightarrow> C\<subseteq>?Z \<Longrightarrow> \<forall>a\<in>C. a\<sqsubseteq>lub C"
    by (metis (no_types, lifting) Ball_Collect c_cpo is_ub_thelub_ex subset_iff)
  hence "\<And>C. longChain C \<Longrightarrow> C\<subseteq>?Z \<Longrightarrow> \<exists>u\<in>?Z. \<forall>a\<in>C. a \<sqsubseteq> u"
    using lub_in_z by force

  hence "\<exists>m\<in>?Z. \<forall>a\<in>?Z. (m\<sqsubseteq>a \<longrightarrow> a=m)" by(subst own_zorn3, auto)

  from this obtain w where w_def: "\<And>z. z\<in>?Z \<Longrightarrow> w \<sqsubseteq> z \<Longrightarrow> w = z" and w_z: "w\<in>?Z"
    by auto

  (* D *)
    (* 1. *)
  hence "\<And>x. x\<in>?F \<Longrightarrow>  w\<sqsubseteq>x"
    by blast

    (* 2. *)
  hence "\<And>x. x\<in>?F \<Longrightarrow> (f w) \<sqsubseteq> x"
    using monof monofunE by fastforce

  hence "f w \<in> ?Z"
    using goodFormed_def goodf monof monofun_def w_z by fastforce

  hence "f w = w"
    using w_def w_z by fastforce

  have "\<And>x. x\<in>?f \<Longrightarrow> w\<sqsubseteq>x"

  thus ?thesis
    using w_z by auto
  oops




section\<open>normal chains\<close>






(* Proof follows closely the proof from Greber, see "SA_Greber" *)
lemma own_knaster_tarski_HOLCF: fixes f :: "'a::ppcpo \<Rightarrow>'a"
  assumes monof: "monofun f" and goodf: "goodFormed f C" and "C \<in> A"
  shows "\<exists>x. f x = x \<and> x\<in>C" (* ToDo: add least condition *)
proof -
  let ?F = "{x. x = f x \<and> x\<in>C}"  (* Set of all fixpoints in the division *)
  let ?Z = "{y. y \<sqsubseteq> f y \<and> (\<forall>x\<in>?F. y\<sqsubseteq>x) \<and> y \<in>C}"

  (* Teil A *)
  obtain bot where bot_bot: "\<And>c. c\<in>C \<Longrightarrow> bot\<sqsubseteq>c" and bot_c: "bot\<in>C" 
    by (meson assms(3) p1)
  have z_bot: "bot \<in> ?Z"
  proof -
    have "f bot \<in> C"
      using bot_c goodFormed_def goodf by blast
    thus ?thesis
      using bot_bot bot_c by auto
  qed


  (* Teil B *)
    (* 1. *)
  from this obtain K where K_ch: "chain K" and K_Z: "\<And>i. K i \<in> ?Z"
    using chain_const by blast
  have "\<And>x i. x\<in>?F \<Longrightarrow> K i\<sqsubseteq>x"
    using K_Z by auto
  moreover from this have "\<And>x. x\<in>?F \<Longrightarrow> (\<Squnion>i. K i) \<sqsubseteq> x"
    by (simp add: K_ch lub_below)

    (* 2. *)
  moreover have "(\<Squnion>i. K i) \<sqsubseteq> f (\<Squnion>i. K i)"
  proof -
    have "chain (\<lambda>i. f (K i))"
      using K_ch assms(1) ch2ch_monofun by blast
    hence f1: "\<And>n. K n \<sqsubseteq> (\<Squnion>n. f (K n))"
      using K_Z below_lub by blast
    have "(\<Squnion>n. f (K n)) \<sqsubseteq> f (Lub K)"
    by (simp add: K_ch \<open>chain (\<lambda>i. f (K i))\<close> assms(1) is_ub_thelub lub_below_iff monofunE)
    then show ?thesis
    using f1 by (meson K_ch below_trans lub_below)
  qed
  moreover have "(\<Squnion>i. K i) \<in> C"
    using K_Z K_ch assms(3) p3 sorry (* by fastforce *)

    (* 3. *)
  ultimately have  "(\<Squnion>i. K i) \<in> ?Z"
    by blast


  (* C *)
  have "\<And>K . chain K \<Longrightarrow> (\<And>i. K i\<in>?Z) \<Longrightarrow> (\<Squnion>i. K i)\<in>?Z" sorry (*see lemma above *)
(*  hence "\<And>K. chain K \<Longrightarrow> (\<And>i. K i\<in>?Z) \<Longrightarrow> (\<forall>x\<in>?F. \<forall>i. (K i) \<sqsubseteq>x)"
    by blast *)
  hence zorn_assumption: "\<And>K. chain K \<Longrightarrow> (\<And>i. K i\<in>?Z) \<Longrightarrow> (\<exists>x\<in>?Z. \<forall>i. (K i) \<sqsubseteq>x)"
    by (meson is_ub_thelub)     
  have "C \<noteq> {}"
    using bot_c by blast
  hence "\<exists>m\<in>?Z. \<forall>a\<in>?Z. (m\<sqsubseteq>a \<longrightarrow> a=m)"  
    sorry (* zorn lemma above *)

    (* Zorn ... DAFUQ ? *)
  from this obtain w where w_def: "\<And>z. z\<in>?Z \<Longrightarrow> w \<sqsubseteq> z \<Longrightarrow> w = z" and w_z: "w\<in>?Z"
    by auto

  (* D *)
    (* 1. *)
  hence "\<And>x. x\<in>?F \<Longrightarrow>  w\<sqsubseteq>x"
    by blast

    (* 2. *)
  hence "\<And>x. x\<in>?F \<Longrightarrow> (f w) \<sqsubseteq> x"
    using monof monofunE by fastforce

  hence "f w \<in> ?Z"
    using goodFormed_def goodf monof monofun_def w_z by fastforce

  hence "f w = w"
    using w_def w_z by fastforce

  thus ?thesis
    using w_z by auto
  oops




lemma knaster_tarski: fixes f :: "'a \<Rightarrow>'a"
  assumes "monofun f"
  obtains x where "f x = x"
  sorry

lemma lfp_condition: assumes "monofun f"
  shows "f (lfp f) = lfp f"
  apply(simp add: lfp_def)
  by (meson assms knaster_tarski someI)


lemma "f\<sqsubseteq>g \<Longrightarrow> lfp f \<sqsubseteq> lfp g"
  sorry

(* We are going to use this for refinement. Does not hold like this, the input might not be monofun *)
lemma lfp_monofun: "monofun lfp"
  oops

end