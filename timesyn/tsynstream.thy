theory tsynstream
  imports "../untimed/Streams" "../inc/Event" "../UnivClasses" "../inc/OptionCpo"

begin

default_sort countable
setup_lifting type_definition_cfun


(***************************************)
section \<open>Typ Definition\<close>
(***************************************)

pcpodef 'a tsynstream = "{t :: 'a event stream. True}"
  by auto



(***************************************)
section \<open>Function Definitions\<close>
(***************************************)

definition tsynDom :: "'a tsynstream \<rightarrow> 'a set" where
"tsynDom \<equiv> \<Lambda> ts . {a | a::'a . (Msg a) \<in> sdom\<cdot>(Rep_tsynstream ts)}"

definition tsynLen:: "'a tsynstream \<rightarrow> lnat" where 
"tsynLen \<equiv> \<Lambda> ts. #(Rep_tsynstream ts)"

definition tsynLshd :: "'a tsynstream \<rightarrow> 'a event discr u" where
"tsynLshd \<equiv> \<Lambda> ts.  lshd\<cdot>(Rep_tsynstream ts)"

definition tsynRt :: "'a tsynstream \<rightarrow> 'a tsynstream" where
"tsynRt \<equiv> \<Lambda> ts. Abs_tsynstream (srt\<cdot>(Rep_tsynstream ts))"


definition tsynLscons :: "'a event discr u \<rightarrow> 'a tsynstream \<rightarrow> 'a tsynstream" where
"tsynLscons \<equiv> \<Lambda> t ts. Abs_tsynstream((lscons\<cdot>t)\<cdot>(Rep_tsynstream ts))"


definition tsynMLscons :: "'a discr u \<rightarrow> 'a tsynstream \<rightarrow> 'a tsynstream" where
"tsynMLscons \<equiv> \<Lambda> t ts. tsynLscons\<cdot>(upApply Msg\<cdot>t)\<cdot>ts"

definition tsynConc :: "'a tsynstream \<Rightarrow> 'a tsynstream \<rightarrow> 'a tsynstream" where
"tsynConc ts1 \<equiv> (\<Lambda> ts2. Abs_tsynstream ((Rep_tsynstream ts1) \<bullet> (Rep_tsynstream ts2)))"

definition tsynDelay :: "'m tsynstream \<rightarrow> 'm tsynstream" where
"tsynDelay \<equiv> tsynLscons\<cdot>(up\<cdot>(Discr Tick))"

definition tsynTake :: "nat \<Rightarrow> 'a tsynstream \<rightarrow> 'a tsynstream" where
"tsynTake n \<equiv> \<Lambda> ts. Abs_tsynstream (stake n\<cdot>(Rep_tsynstream ts))"





instantiation tsynstream :: (message) uscl
begin

definition usOkay_tsynstream :: "channel \<Rightarrow> 'm::message tsynstream \<Rightarrow> bool" where
"usOkay_tsynstream c ts \<equiv> (tsynDom\<cdot>ts \<subseteq> ctype c)"

definition usLen_tsynstream :: "'a tsynstream \<rightarrow> lnat" where 
"usLen_tsynstream = tsynLen"

instance
  apply intro_classes 
  apply (simp add: adm_def)
proof 
  fix c :: "channel" and Y :: "nat \<Rightarrow> 'a tsynstream"
  have " chain Y \<Longrightarrow> (\<forall>i::nat. usOkay c (Y i)) \<Longrightarrow> usOkay c (\<Squnion>i::nat. Y i)"
  proof -
    assume a0:"chain Y" and a1:"(\<forall>i::nat. usOkay c (Y i))"
  have 1: "\<forall> i. tsynDom\<cdot>(Y i) \<subseteq> tsynDom\<cdot>(\<Squnion> i. Y i)"
    by (metis SetPcpo.less_set_def a0 is_ub_thelub monofun_cfun_arg)
  show "usOkay c (\<Squnion>i::nat. Y i)"
    using "1" a1 usOkay_tsynstream_def
    by (simp add: usOkay_tsynstream_def a0 subset_cont)
  qed
  then show "chain Y \<longrightarrow> (\<forall>i::nat. usOkay c (Y i)) \<longrightarrow> usOkay c (\<Squnion>i::nat. Y i)" by blast
  qed
end




(***************************************)
section \<open>Lemma\<close>
(***************************************)

(* Rep, Abs *)

lemma tsync_rep_cont [simp]: "cont Rep_tsynstream"
  by (smt Abs_tsynstream_inverse Prelude.contI2 UNIV_I UNIV_def below_tsynstream_def lub_eq lub_tsynstream monofunI po_eq_conv)

lemma tsync_abs_cont [simp]: "cont Abs_tsynstream"
  apply(rule contI2)
  apply (metis Abs_tsynstream_inverse UNIV_I UNIV_def below_tsynstream_def monofun_def)
proof -
have "cont (\<lambda>s. Abs_tsynstream s::'a tsynstream)"
  using cont_Abs_tsynstream by force
  then show "\<forall>f. chain f \<longrightarrow> Abs_tsynstream (\<Squnion>n. f n) \<sqsubseteq> (\<Squnion>n. (Abs_tsynstream (f n)::'a tsynstream))"
    using cont2contlubE eq_imp_below by blast
qed

lemma tsync_rep_abs [simp]: "Rep_tsynstream (Abs_tsynstream sy) = sy"
  using Abs_tsynstream_inverse by blast

(* tsynLscons, tsynMLscons *)

lemma tsync_lscons_cont: "cont  (\<lambda> ts. Abs_tsynstream((t && Rep_tsynstream ts)))" sorry

lemma tsync_lscons_cont2: "cont (\<lambda> ts. Abs_tsynstream (t \<bullet> Rep_tsynstream ts))" sorry

lemma tsync_lscons_cont3: "cont (\<lambda> t. \<Lambda> ts. Abs_tsynstream(t && (Rep_tsynstream ts)))" sorry

lemma tsynmlscons2tsynlscons: "tsynMLscons\<cdot>(updis m)\<cdot>ts = tsynLscons\<cdot>(updis (Msg m))\<cdot>ts"
  by (simp add: tsynMLscons_def)

lemma tsynlscons_insert: "tsynLscons\<cdot>t\<cdot>ts = Abs_tsynstream ((lscons\<cdot>t)\<cdot>(Rep_tsynstream ts))"
  unfolding tsynLscons_def 
  by (simp only: beta_cfun tsync_lscons_cont3 tsync_lscons_cont)

lemma abstsyn2tsynlscons: "Abs_tsynstream (t && ts) = tsynLscons\<cdot>t\<cdot>(Abs_tsynstream ts)"
  by (simp add: tsynlscons_insert)

lemma mlscons_abstsynstream: "Abs_tsynstream (updis (Msg m) && ts) = tsynMLscons\<cdot>(updis m)\<cdot>(Abs_tsynstream ts)"
  by(simp add: tsynmlscons2tsynlscons abstsyn2tsynlscons)

(* Lshd, Rt *)


lemma tsynhd_insert: "tsynLshd\<cdot>ts = lshd\<cdot>(Rep_tsynstream ts)"
  apply(simp add: tsynLshd_def) sorry

lemma tsynrt_insert: "tsynRt\<cdot>ts = Abs_tsynstream (srt\<cdot>(Rep_tsynstream ts))" sorry

lemma tsync_rt_cont: "cont (\<lambda> ts. Abs_tsynstream (srt\<cdot>(Rep_tsynstream ts)))" sorry

lemma tsync_lshd_cont: "cont (\<lambda> ts. lshd\<cdot>(Rep_tsynstream ts))" sorry

lemma tsyntakedropfirst [simp]: "tsynLscons\<cdot>(tsynLshd\<cdot>ts)\<cdot>(tsynRt\<cdot>ts) = ts"
  apply (simp add: tsynLscons_def tsync_lscons_cont3 tsync_lscons_cont tsynRt_def tsync_rt_cont tsynLshd_def tsync_lshd_cont)
  by (metis Rep_tsynstream_inject lscons_conv lshd_updis stream.con_rews(2) stream.sel_rews(3) surj_scons tsync_rep_abs)


(* tsynConc *)

lemma tsync_conc_cont: "cont (\<lambda> ts2. Abs_tsynstream ((Rep_tsynstream ts1) \<bullet> (Rep_tsynstream ts2)))"
  apply (rule contI2)
  apply (metis (no_types, lifting) below_tsynstream_def monofunI monofun_cfun_arg tsync_rep_abs)
proof -
have "cont (\<lambda> ts2. Abs_tsynstream ((Rep_tsynstream ts1) \<bullet> (Rep_tsynstream (ts2:: 'a tsynstream))))"
  using cont_Abs_tsynstream by force
  then show "\<forall>Y::nat \<Rightarrow> 'a tsynstream.
       chain Y \<longrightarrow>
       Abs_tsynstream (Rep_tsynstream ts1 \<bullet> Rep_tsynstream (\<Squnion>i::nat. Y i)) \<sqsubseteq> (\<Squnion>i::nat. Abs_tsynstream (Rep_tsynstream ts1 \<bullet> Rep_tsynstream (Y i)))"
    using cont2contlubE eq_imp_below by blast
qed

lemma tsynconc_insert: "tsynConc ts1\<cdot>ts2 = Abs_tsynstream ((Rep_tsynstream ts1) \<bullet> (Rep_tsynstream ts2))"
  by (simp add: tsynConc_def tsync_conc_cont)

lemma tsyn_approxl [simp]: assumes "ts1 \<sqsubseteq> ts2"
  shows "\<exists> ts. (ts2 = tsynConc ts1\<cdot>ts)"
proof -
  have "(Rep_tsynstream ts1) \<sqsubseteq> (Rep_tsynstream ts2)" by (meson assms below_tsynstream_def)
  hence "\<exists> s. ((Rep_tsynstream ts2) = (Rep_tsynstream ts1) \<bullet> s)" by (metis approxl3) 
  thus ?thesis
    by (metis (mono_tags) Rep_tsynstream_cases Rep_tsynstream_inverse mem_Collect_eq tsynconc_insert) 
qed

(* delay *)

lemma delayfun_abstsynstream: "tsynDelay\<cdot>(Abs_tsynstream s) = Abs_tsynstream (updis \<surd> && s)" 
  by (simp add:  lscons_conv tsynconc_insert tsynDelay_def tsynLscons_def tsync_lscons_cont3 tsync_lscons_cont2)



(* tsynLen *)

lemma tsynInf:  
  shows "tsynLen\<cdot>ts = \<infinity> \<longleftrightarrow> #(Rep_tsynstream ts) = \<infinity>"
  by (simp add: sfilterl4 tsynLen_def)

lemma tsynlen_insert:  "tsynLen\<cdot>ts =  #(Rep_tsynstream ts)" sorry

lemma tsynfinite[simp]: assumes "tsynLen\<cdot>ts < \<infinity>"
  shows "#(Rep_tsynstream ts) < \<infinity>"
proof(rule ccontr)
  assume "\<not> #(Rep_tsynstream ts) < \<infinity>"
  hence "#(Rep_tsynstream ts) = \<infinity>" using inf_ub lnle_def lnless_def by blast
  hence "tsynLen\<cdot>ts = \<infinity>" by (simp add: tsynLen_def)
  thus False using assms by auto 
qed



(* Chains, other stuff *)

lemma rep_tsynstream_chain [simp]: assumes "chain Y"
  shows "chain (\<lambda>i. Rep_tsynstream (Y i))"
  by (meson assms below_tsynstream_def po_class.chain_def)

lemma tsyn_infinite_chain: assumes "chain Y" 
  shows "\<not>finite_chain Y \<longleftrightarrow> \<not>finite_chain (\<lambda>i. Rep_tsynstream (Y i))"
proof -
  have f1: "\<And>f. finite_chain (\<lambda>n. Rep_tsynstream (f n::'a tsynstream)) \<or> \<not> finite_chain f"
    using cont_finch2finch tsync_rep_cont by blast
  obtain nn :: "(nat \<Rightarrow> 'a event stream) \<Rightarrow> nat" where
    "\<And>f. Lub f = f (nn f) \<or> \<not> finite_chain f"
    by (metis (no_types) finite_chain_def maxinch_is_thelub)
  then show ?thesis
    using f1 by (metis (no_types) Rep_tsynstream_inverse assms finite_chain_def lub_tsynstream maxinch_is_thelub)
qed

lemma tsyn_infinite_fin: assumes "chain Y" and "\<not>finite_chain Y"
  shows "tsynLen\<cdot>(Y i) < \<infinity>"
  by (metis Fin_neq_inf assms(1) assms(2) inf_chainl1 inf_ub lnle_def lnless_def rep_tsynstream_chain tsynInf tsyn_infinite_chain)


lemma tsyn_below_eq: assumes "tsynLen\<cdot>ts1 = \<infinity>" and "ts1 \<sqsubseteq> ts2"
  shows "ts1 = ts2"
  by (metis assms Rep_tsynstream_inject below_tsynstream_def eq_slen_eq_and_less mono_fst_infD tsynInf) 



(* tsynTake *)

lemma tsync_take_cont: "cont (\<lambda> ts. Abs_tsynstream (stake n\<cdot>(Rep_tsynstream ts)))" sorry

lemma tsyntake_chain: "chain (\<lambda>i. tsynTake i\<cdot>ts)" sorry

lemma tsyntake_len[simp]: "tsynLen\<cdot>(tsynTake i\<cdot>ts) = min (tsynLen\<cdot>ts) (Fin i)"
  apply(induction i arbitrary: ts)
   apply (simp)
   apply (simp add: Rep_tsynstream_strict tsynlen_insert)
  using Fin_Suc lnsuc_lnle_emb min_def tsyntakedropfirst sorry

lemma tsyntake_infinite_chain: assumes "tsynLen\<cdot>ts = \<infinity>" shows "\<not> max_in_chain n (\<lambda>i. tsynTake i\<cdot>ts)"
 by (smt Abs_cfun_inverse2 HOLCF_trans_rules(2) Suc_n_not_le_n abstsyn2tsynlscons assms below_tsynstream_def inject_Fin is_ub_thelub leI lub_below_iff lub_tsynstream maxinch_is_thelub min.strict_order_iff po_class.chain_def slen_stake_fst_inf stream.take_take tsynTake_def tsync_rep_abs tsync_take_cont tsynlen_insert tsynrt_insert tsyntakedropfirst ub_stake)

(* Well... Smt proof is also available *)
(*     by (smt Abs_cfun_inverse2 Suc_n_not_le_n assms below_tsynstream_def finite_chain_def inf_chainl4 inject_Fin linorder_le_cases lub_tsynstream max_in_chain_def maxinch_is_thelub min_def po_class.chainI stakeostake tsynInf tsynTake_def tsync_rep_abs tsync_take_cont tsyntake_len ub_stake) *)
lemma tsyntake_inf_lub: assumes "tsynLen\<cdot>ts = \<infinity>" shows "(\<Squnion>i. (tsynTake i\<cdot>ts))= ts"
proof -
  have f1: "(\<Squnion>i. (tsynTake i\<cdot>ts) ) \<sqsubseteq> ts" using lub_below
    by (metis (mono_tags, lifting) Abs_cfun_inverse2 below_tsynstream_def tsynTake_def tsync_rep_abs tsync_take_cont tsyntake_chain ub_stake) 
  have "tsynLen\<cdot>(\<Squnion>i. (tsynTake i\<cdot>ts) ) = \<infinity>" using assms 
  proof -
    have f1: "\<forall>n na. (n::nat) \<le> na \<or> na \<le> n"
by (meson linorder_le_cases)
  obtain nn :: "(nat \<Rightarrow> 'a tsynstream) \<Rightarrow> nat" where
    f2: "\<forall>f. f (nn f) \<notsqsubseteq> f (Suc (nn f)) \<or> chain f"
    using po_class.chainI by moura
have "Abs_tsynstream (stake (Suc (nn (\<lambda>n. tsynTake n\<cdot>ts)))\<cdot> (Rep_tsynstream ts)) = tsynTake (Suc (nn (\<lambda>n. tsynTake n\<cdot>ts)))\<cdot>ts"
by (simp add: tsynTake_def tsync_take_cont)
  then have "Rep_tsynstream (tsynTake (Suc (nn (\<lambda>n. tsynTake n\<cdot>ts)))\<cdot>ts) = stake (Suc (nn (\<lambda>n. tsynTake n\<cdot>ts)))\<cdot>(Rep_tsynstream ts)"
    by (metis tsync_rep_abs)
  then have f3: "stake (nn (\<lambda>n. tsynTake n\<cdot>ts))\<cdot> (Rep_tsynstream (tsynTake (Suc (nn (\<lambda>n. tsynTake n\<cdot>ts)))\<cdot>ts)) = Rep_tsynstream (Abs_tsynstream (stake (nn (\<lambda>n. tsynTake n\<cdot>ts))\<cdot>(Rep_tsynstream ts)))"
    by (simp add: min_def_raw)
  have "Abs_tsynstream (stake (nn (\<lambda>n. tsynTake n\<cdot>ts))\<cdot>(Rep_tsynstream ts)) = tsynTake (nn (\<lambda>n. tsynTake n\<cdot>ts))\<cdot>ts"
    by (simp add: tsynTake_def tsync_take_cont)
  then have f4: "chain (\<lambda>n. tsynTake n\<cdot>ts)"
using f3 f2 by (metis below_tsynstream_def ub_stake)
obtain nna :: "(nat \<Rightarrow> 'a event stream) \<Rightarrow> nat" where
  f5: "\<forall>f. f (nna f) \<notsqsubseteq> f (Suc (nna f)) \<or> chain f"
using po_class.chainI by moura
  have "Rep_tsynstream (tsynTake (Suc (nna (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))))\<cdot> ts) = stake (Suc (nna (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))))\<cdot> (Rep_tsynstream ts)"
    by (simp add: tsynTake_def tsync_take_cont)
  then have f6: "stake (nna (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot> (Rep_tsynstream (tsynTake (Suc (nna (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))))\<cdot> ts)) = Rep_tsynstream (Abs_tsynstream (stake (nna (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot> (Rep_tsynstream ts)))"
    by (simp add: min_def_raw)
  have "Abs_tsynstream (stake (nna (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot> (Rep_tsynstream ts)) = tsynTake (nna (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot>ts"
    by (simp add: tsynTake_def tsync_take_cont)
  then have f7: "chain (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))"
    using f6 f5 by (metis ub_stake)
obtain nnb :: "(nat \<Rightarrow> 'a event stream) \<Rightarrow> nat" where
  f8: "\<forall>f. (\<not> finite_chain f \<or> chain f \<and> max_in_chain (nnb f) f) \<and> (finite_chain f \<or> \<not> chain f \<or> (\<forall>n. \<not> max_in_chain n f))"
  using finite_chain_def by moura
  have f9: "\<forall>n t. tsynLen\<cdot>(tsynTake n\<cdot>(t::'a tsynstream)) = min (tsynLen\<cdot>t) (Fin n)"
    by (meson tsyntake_len)
  obtain nnc :: "(nat \<Rightarrow> 'a tsynstream) \<Rightarrow> nat \<Rightarrow> nat" where
    f10: "\<forall>x0 x1. (\<exists>v2\<ge>x1. x0 x1 \<noteq> x0 v2) = (x1 \<le> nnc x0 x1 \<and> x0 x1 \<noteq> x0 (nnc x0 x1))"
    by moura
  then have f11: "(\<not> max_in_chain (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))) (\<lambda>n. tsynTake n\<cdot>ts) \<or> (\<forall>n. \<not> nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)) \<le> n \<or> tsynTake (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot> ts = tsynTake n\<cdot>ts)) \<and> (max_in_chain (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))) (\<lambda>n. tsynTake n\<cdot>ts) \<or> nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)) \<le> nnc (\<lambda>n. tsynTake n\<cdot>ts) (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))) \<and> tsynTake (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot> ts \<noteq> tsynTake (nnc (\<lambda>n. tsynTake n\<cdot>ts) (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))))\<cdot> ts)"
    by (meson max_in_chain_def)
  have f12: "(\<not> max_in_chain (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))) (\<lambda>n. tsynTake n\<cdot>ts) \<or> (\<forall>n. \<not> nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)) \<le> n \<or> tsynTake (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot> ts = tsynTake n\<cdot>ts)) \<and> (max_in_chain (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))) (\<lambda>n. tsynTake n\<cdot>ts) \<or> nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)) \<le> nnc (\<lambda>n. tsynTake n\<cdot>ts) (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))) \<and> tsynTake (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot> ts \<noteq> tsynTake (nnc (\<lambda>n. tsynTake n\<cdot>ts) (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))))\<cdot> ts)"
using f10 by (meson max_in_chain_def)
  have f13: "(\<lambda>t. Abs_tsynstream (stake (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot> (Rep_tsynstream (t::'a tsynstream)))) = Rep_cfun (tsynTake (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))))"
by (simp add: tsynTake_def tsync_take_cont)
  then have f14: "tsynTake (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot>ts = Abs_tsynstream (stake (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot> (Rep_tsynstream ts))"
    by metis
  have f15: "Abs_tsynstream (stake (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot> (Rep_tsynstream ts)) = tsynTake (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot>ts"
    using f13 by metis
have f16: "Rep_cfun (tsynTake (nnc (\<lambda>n. tsynTake n\<cdot>ts) (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))))) = (\<lambda>t. Abs_tsynstream (stake (nnc (\<lambda>n. tsynTake n\<cdot>ts) (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))))\<cdot> (Rep_tsynstream (t::'a tsynstream))))"
by (simp add: tsynTake_def tsync_take_cont)
  obtain nnd :: "(nat \<Rightarrow> 'a event stream) \<Rightarrow> nat \<Rightarrow> nat" where
"\<forall>x0 x1. (\<exists>v2\<ge>x1. x0 x1 \<noteq> x0 v2) = (x1 \<le> nnd x0 x1 \<and> x0 x1 \<noteq> x0 (nnd x0 x1))"
    by moura
  then have f17: "(\<not> max_in_chain (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))) (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)) \<or> (\<forall>n. \<not> nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)) \<le> n \<or> Rep_tsynstream (tsynTake (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot> ts) = Rep_tsynstream (tsynTake n\<cdot>ts))) \<and> (max_in_chain (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))) (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)) \<or> nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)) \<le> nnd (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)) (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))) \<and> Rep_tsynstream (tsynTake (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot> ts) \<noteq> Rep_tsynstream (tsynTake (nnd (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)) (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))))\<cdot> ts))"
    by (meson max_in_chain_def)
  { assume "min \<infinity> (Fin (Suc (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))))) \<noteq> tsynLen\<cdot> (tsynTake (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot>ts)"
    then have "\<not> max_in_chain (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))) (\<lambda>n. tsynTake n\<cdot>ts)"
      using f11 f9 f1 by (metis Suc_n_not_le_n assms)
    moreover
    { assume "tsynTake (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot> ts \<noteq> Abs_tsynstream (\<Squnion>n. Rep_tsynstream (tsynTake n\<cdot>ts))"
then have "(\<Squnion>n. Rep_tsynstream (tsynTake n\<cdot>ts)) \<noteq> Rep_tsynstream (Abs_tsynstream (stake (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot> (Rep_tsynstream ts)))"
  using f14 by fastforce
  then have "\<not> chain (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)) \<or> \<not> max_in_chain (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))) (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))"
    using f15 maxinch_is_thelub by auto }
  ultimately have "(\<Squnion>n. Rep_tsynstream (tsynTake n\<cdot>ts)) = Rep_tsynstream (tsynTake (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)))\<cdot> ts) \<longrightarrow> \<not> chain (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)) \<or> \<not> max_in_chain (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))) (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))"
    using f17 f16 f12 by force }
  then have "(\<not> chain (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts)) \<or> \<not> max_in_chain (nnb (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))) (\<lambda>n. Rep_tsynstream (tsynTake n\<cdot>ts))) \<or> #(\<Squnion>n. Rep_tsynstream (tsynTake n\<cdot>ts)) = \<infinity>"
    using f7 by (simp add: assms maxinch_is_thelub)
  then have "#(\<Squnion>n. Rep_tsynstream (tsynTake n\<cdot>ts)) = \<infinity>"
    using f8 f7 inf_chainl4 by blast
  then show ?thesis
using f4 by (simp add: lub_tsynstream tsynInf)
qed
  thus ?thesis using local.f1 tsyn_below_eq by blast 
qed


(* induction *)


lemma tsynstream_infs: "(\<And>s. (tsynLen\<cdot>s)<\<infinity> \<Longrightarrow> P s) \<Longrightarrow> adm P \<Longrightarrow> P s"
 by (metis (no_types, lifting) adm_def finite_chain_def inf_less_eq leI tsyn_infinite_fin 
      tsyntake_chain tsyntake_inf_lub tsyntake_infinite_chain)


lemma tsynstream_fin_induct_h:
  assumes bottom: "P \<bottom>"
    and delayfun: "\<And>xs. P xs \<Longrightarrow> P (tsynDelay\<cdot>xs)"
    and mlscons: "\<And>xs x. P xs  \<Longrightarrow> P (tsynMLscons\<cdot>(updis x)\<cdot>xs)"
    and fin: "#s < \<infinity>"
  shows "P (Abs_tsynstream s)"
proof (induction rule: stream_fin_induct)
  show " P (Abs_tsynstream \<epsilon>)"
    by (simp add: Abs_tsynstream_strict bottom)
next
  fix x :: "'a event discr u" and xs :: "'a event stream"
  assume x_nbot: "x \<noteq> \<bottom>"
  assume xs_imp: "P (Abs_tsynstream xs)"
  show "P (Abs_tsynstream (x && xs))"
    proof (cases "x=updis \<surd>")
      case True
      have "tsynDelay\<cdot>(Abs_tsynstream xs) = Abs_tsynstream (x && xs)"
        by (simp add: True delayfun_abstsynstream)
      thus "P (Abs_tsynstream (x && xs))"
        using delayfun xs_imp by fastforce
    next
      case False
      obtain m where m_def: "x = up\<cdot>(Discr (Msg m))"
        by (metis False event.exhaust updis_exists x_nbot)                        
      have 1:"Abs_tsynstream (x && xs) = tsynMLscons\<cdot>(updis m)\<cdot>(Abs_tsynstream xs)" 
        apply (simp add: m_def)
        using m_def by (simp add: mlscons_abstsynstream)
      thus "P (Abs_tsynstream (x && xs))"
        by (simp add: mlscons xs_imp)
    qed
next
  show "#s < \<infinity>"
    by (simp add: fin)
qed


lemma tsynstream_fin_induct:
  assumes bottom: "P \<bottom>" 
    and delayfun: "\<And>xs. P xs \<Longrightarrow> P (tsynDelay\<cdot>xs)" 
    and mlscons: "\<And>xs x. P xs \<Longrightarrow> P (tsynMLscons\<cdot>(updis x)\<cdot>xs)"
    and fin: "tsynLen\<cdot>ts < \<infinity>"
  shows "P ts"
proof -
  obtain s where s_def: "Abs_tsynstream s = ts"
    using Rep_tsynstream_inverse by blast
  hence "#s < \<infinity>" 
    using tsync_rep_abs fin tsynfinite by force
  hence "P (Abs_tsynstream s)"
    by (simp add: tsynstream_fin_induct_h bottom delayfun mlscons)
  thus "P ts" 
    by (simp add: s_def)   
qed
 
lemma tsynstream_induct [case_names adm bottom delayfun mlscons, induct type: tsynstream]:
fixes ts :: "'a tsynstream"
assumes adm: "adm P" and bottom: "P \<bottom>"  
  and delayfun: "\<And>ts. P ts \<Longrightarrow> P (tsynDelay\<cdot>ts)" 
  and mlscons: "\<And>ts t. P ts \<Longrightarrow> P (tsynMLscons\<cdot>(updis t)\<cdot>ts)"
shows "P ts" 
by (metis adm bottom delayfun mlscons tsynstream_fin_induct tsynstream_infs)


(* Case rule *)

lemma tsyncases_h:
  assumes bottom: "xs=\<epsilon> \<Longrightarrow> P xs"
    and delayfun: "\<And>as. xs=updis \<surd> && as \<Longrightarrow> P xs"
    and mlscons: "\<And>a as. xs=updis (\<M> a) && as \<Longrightarrow> P xs"
  shows "P xs"
  apply (rule_tac y=xs in scases')
  using bottom apply blast
  by (metis bottom delayfun event.exhaust lscons_conv mlscons surj_scons)

lemma tsyncases:
  assumes bottom: "ts=\<bottom> \<Longrightarrow> P ts"
    and delayfun: "\<And>as. ts=tsynDelay\<cdot>as \<Longrightarrow> P ts"
    and mlscons: "\<And>a as. ts=tsynMLscons\<cdot>(updis a)\<cdot>as \<Longrightarrow> P ts"
  shows "P ts"
  apply (rule_tac xs="Rep_tsynstream ts" in tsyncases_h)
  using Rep_tsynstream_bottom_iff bottom 
  apply blast
  apply (metis Rep_tsynstream_inverse delayfun delayfun_abstsynstream)
  by (metis Rep_tsynstream_inverse mlscons mlscons_abstsynstream)

end