theory IntroCaseStudy_LiftedTL_JB
imports  "../Streams"  "../TStream"
begin

(* tsNth *)
lemma snth_tscons[simp]: assumes "tsTickCount\<cdot>a = Fin 1 "
  shows "tsNth (Suc k)\<cdot>(a \<bullet> s) = tsNth k\<cdot>s"
by (simp add: assms tsDropFirstConc tsNth_Suc)

lemma tsnth_shd[simp]: "tsNth 0\<cdot>s = tsTakeFirst\<cdot>s"
by (simp add: tsNth_def)

(* If two timed streams of same length agree on every element, all their finite prefixes are equal *)
lemma tsnths_eq_lemma [rule_format]: 
  "\<forall>x y. (#\<surd>x) = (#\<surd>y) \<and> (\<forall>n. Fin n < (#\<surd>x) \<longrightarrow> tsNth n\<cdot>x = tsNth n\<cdot>y) 
           \<longrightarrow>tsTake  k\<cdot>x = tsTake k\<cdot>y"
by (smt less2nat_lemma less_SucI min.commute min_def not_less trans_lnle 
    tsDropNth tsDropTake1 tsTakeDrop tsTake_prefix tsnth2tstake_eq tsnth_len 
    tstake_below_eq tstake_len)

(* If two timed streams of same length agree on every element, they are equal *)
lemma tsnths_eq: "\<lbrakk>(#\<surd>x) = (#\<surd>y); \<forall>n. Fin n < (#\<surd>x) \<longrightarrow> tsNth n\<cdot>x = tsNth n\<cdot>y\<rbrakk> \<Longrightarrow> x = y"
using ts_take_eq tsnths_eq_lemma by blast



(* tsConc *)
lemma ts_tsconc_prefix [simp]: "(x::'a tstream) \<sqsubseteq> (x \<bullet> y)"
by (metis Rep_tstream_inverse Rep_tstream_strict minimal monofun_cfun_arg sconc_snd_empty tsconc_insert)

(* Prepending to infinite streams produces infinite streams again *)
lemma slen_tsconc_snd_inf: "(#\<surd> y)=\<infinity> \<Longrightarrow> (#\<surd>(x \<bullet> y)) = \<infinity>"
by (metis Rep_tstream_inverse Rep_tstream_strict sconc_snd_empty slen_sconc_snd_inf tsInfTicks ts_well_conc tsconc_rep_eq)



(* approx, chains, cont *)
(* A finite prefix of length @{term "k"} is created by @{term "stake k"} *)
lemma ts_approxl1: "\<forall>s1 s2. s1 \<sqsubseteq> s2 \<and> (#\<surd> s1) = Fin k \<longrightarrow> tsTake k\<cdot>s2 = s1"
using ts_approxl tstake_conc by blast

(* A prefix of a stream is equal to the original one or a finite prefix *)
lemma ts_approxl2: "s1 \<sqsubseteq> s2 \<Longrightarrow> (s1 = s2) \<or> (\<exists>n. tsTake n\<cdot>s2 = s1 \<and> Fin n = #\<surd>s1)"
by (metis ts_approxl1 ninf2Fin ts_below_eq)

(* In infinite chains, all streams are finite *)
lemma ts_inf_chainl1: "\<lbrakk>chain Y; \<not>finite_chain Y\<rbrakk> \<Longrightarrow> \<exists>k. (#\<surd>(Y i)) = Fin k"
by (metis infI less_irrefl ts_infinite_fin)

(* Each prefix of a stream can be expanded to the original stream *)
(* TODO: check if duplicate *)
lemma ts_approxl3: "(s1::'a tstream) \<sqsubseteq> s2 \<Longrightarrow> \<exists>t. s1\<bullet>t = s2"
using ts_approxl by blast

(* In infinite chains, there is an element which is a true prefix of another one *)
lemma ts_inf_chainl2: "\<lbrakk>chain Y; \<not> finite_chain Y\<rbrakk> \<Longrightarrow> \<exists>j. Y k \<sqsubseteq> Y j \<and> (#\<surd>(Y k)) < #\<surd>(Y j)"
proof -
  assume a1: "chain Y"
  assume a2: "\<not> finite_chain Y"
  moreover
  { assume "\<infinity> \<noteq> #\<surd> Y k"
    then have "\<exists>n. \<not> #\<surd> Y n \<le> #\<surd> Y k"
      using a2 a1 by (metis (no_types) exist_tslen inf_belowI lnle_def trans_lnle)
    then have ?thesis
      using a1 by (meson chain_tord lnle_def monofun_cfun_arg not_less) }
  ultimately show ?thesis
    using a1 by (metis (no_types) chain_tord ts_infinite_fin)
qed

(* Each chain becomes finite by mapping @{term "stake n"} to every element *)
lemma ts_finite_chain_stake: "chain Y \<Longrightarrow> finite_chain (\<lambda>i. tsTake n\<cdot>(Y i))"
proof -
  assume a1: "chain Y"
  have f2: "\<And>n t. max_in_chain n (tsTake_abbrv (t::'a tstream)) \<or> t \<noteq> t \<down> n"
    by (simp add: maxinch_is_thelub)
  have f3: "\<And>f n. finite_chain f \<or> \<not> max_in_chain n (tsTake_abbrv (Lub f::'a tstream)) \<or> \<not> chain f"
    using ts_infinite_lub tstake_infinite_chain by blast
  have "\<And>n t. max_in_chain n (tsTake_abbrv t::'a tstream \<down> n )"
    using f2 by (metis tsTake2take)
  then show ?thesis
    using f3 a1 by (metis chain_monofun contlub_cfun_arg)
qed

(* every finite prefix of the lub is also prefix of some element in the chain *)
lemma ts_lub_approx: "chain Y \<Longrightarrow> \<exists>k. tsTake n\<cdot>(lub (range Y)) = tsTake n\<cdot>(Y k)"
by (metis exist_tslen finite_chain_def is_ub_thelub maxinch_is_thelub tstake_less_below)


end
