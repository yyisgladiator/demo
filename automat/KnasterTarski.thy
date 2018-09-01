(* Dummy for KnasterTarski proof over cpo/pcpo *)

theory KnasterTarski

imports HOLCF

begin

(* This is going to be problematic, we cannot use pcpo (because uspec is no pcpo) *)
default_sort cpo

class A_class = 
  fixes A :: "'a set set"
begin
end

class ppcpo = A_class +  cpo + 
  assumes "A \<noteq> {} " and  "A \<noteq> { {} } "    (* A is not empty *) 
  (* assumes "setflat\<cdot>A = UNIV" *)

    (* every division has its own bottom element *)
  assumes p1: "\<And>a. a\<in>A \<Longrightarrow> \<exists>bot\<in>a. \<forall>b\<in>a. bot \<sqsubseteq>b"  (* ToDo: Name + schöner aufschreiben *)

    (* Elements from different divisions are never in a below-relation *)
  assumes p2: "\<And>a b. a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> \<exists>aa bb. aa\<in>a \<and> bb\<in>b \<Longrightarrow> a = b" (* ToDo: Name + schöner aufschreiben *)

    (* every set is a cpo *)
  assumes p3: "\<And>K i a. a\<in>A \<Longrightarrow> chain K \<Longrightarrow> K i\<in>a \<Longrightarrow> (\<Squnion>i. K i) \<in> a" (* ToDo: Name + schöner aufschreiben *)
begin

end


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




(* There exists a division in which f is complete *)
definition goodFormed :: "('a::ppcpo \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" where
"goodFormed f C \<equiv> \<forall>aa\<in>C. f aa \<in>C"



(* ToDo: add LEAST condition *)
definition lfp:: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
"lfp f = (SOME x. f x = x)"



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
  have "bot \<in> ?Z"
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
    using K_Z K_ch assms(3) p3 by fastforce

    (* 3. *)
  ultimately have  "(\<Squnion>i. K i) \<in> ?Z"
    by blast


  (* C *)
    (* Zorn ... DAFUQ ? *)
  obtain w where w_def: "\<And>z. z\<in>?Z \<Longrightarrow> w \<sqsubseteq> z \<Longrightarrow> w = z" and w_z: "w\<in>?Z"
      sorry

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
qed




lemma knaster_tarski: fixes f :: "'a \<Rightarrow>'a"
  assumes "monofun f"
  obtains x where "f x = x"
  sorry

lemma lfp_condition: assumes "monofun f"
  shows "f (lfp f) = lfp f"
  apply(simp add: lfp_def)
  by (meson assms knaster_tarski someI)

(* We are going to use this for refinement. Does not hold like this, the input might not be monofun *)
lemma lfp_monofun: "monofun lfp"
  oops

end