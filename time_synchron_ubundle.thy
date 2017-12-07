theory time_synchron_ubundle
  imports "untimed/Streams" "inc/Event" "UnivClasses"

begin

default_sort countable

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
"tsynLshd \<equiv> \<Lambda> s.  lshd\<cdot>(Rep_tsynstream s)"

definition tsynRt :: "'a tsynstream \<rightarrow> 'a tsynstream" where
"tsynRt \<equiv> \<Lambda> s. Abs_tsynstream (srt\<cdot>(Rep_tsynstream s))"


definition tsynLscons :: "'a event discr u \<rightarrow> 'a tsynstream \<rightarrow> 'a tsynstream" where
"tsynLscons \<equiv> \<Lambda> t ts. Abs_tsynstream((lscons\<cdot>t)\<cdot>(Rep_tsynstream ts))"


definition tsynMLscons :: "'a discr u \<rightarrow> 'a tsynstream \<rightarrow> 'a tsynstream" where
"tsynMLscons \<equiv> \<Lambda> t ts. tsynLscons\<cdot>(upApply Msg\<cdot>t)\<cdot>ts"

definition tsynConc :: "'a tsynstream \<Rightarrow> 'a tsynstream \<rightarrow> 'a tsynstream" where
"tsynConc ts1 \<equiv> (\<Lambda> ts2. Abs_tsynstream ((Rep_tsynstream ts1) \<bullet> (Rep_tsynstream ts2)))"

abbreviation tsyncDelay :: "'m tsynstream \<rightarrow> 'm tsynstream" where
"tsyncDelay \<equiv> tsynLscons\<cdot>(up\<cdot>(Discr Tick))"




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


lemma tsynconc_insert: "tsynConc ts1\<cdot>ts2 = Abs_tsynstream ((Rep_tsynstream ts1) \<bullet> (Rep_tsynstream ts2))"
apply (simp add: tsynConc_def)
  oops

lemma tsynstream_fin_induct_h:
  assumes bottom: "P \<bottom>"
    and delayfun: "\<And>xs. P xs \<Longrightarrow> P (tsynDelay\<cdot>xs)"
    and mlscons: "\<And>xs x. P xs \<Longrightarrow> xs\<noteq>\<bottom> \<Longrightarrow> P (tsynMLscons\<cdot>(updis x)\<cdot>xs)"
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
        apply (simp add: True delayfun) sorry
      thus "P (Abs_tsynstream (x && xs))"
        using delayfun xs_imp by fastforce
    next
      case False
      obtain m where m_def: "x = up\<cdot>(Discr (Msg m))"
        by (metis False event.exhaust updis_exists x_nbot)                        
      have xs_nbot: "xs\<noteq>\<bottom>" sorry
      hence "Abs_tsynstream (x && xs) = tsynMLscons\<cdot>(updis m)\<cdot>(Abs_tsynstream xs)"
        using m_def sorry
      thus "P (Abs_tsynstream (x && xs))"
        by (simp add: Abs_tsynstream_bottom_iff assms(3) xs_imp xs_nbot)
      qed
next
  show "#s < \<infinity>"
    by (simp add: fin)
qed

lemma synfinititeTicks[simp]: assumes "tsynlen\<cdot>ts < \<infinity>"
  shows "#(Rep_tsynstream ts) < \<infinity>"
proof(rule ccontr)
  assume "\<not> #(Rep_tsynstream ts) < \<infinity>"
  hence "#(Rep_tsynstream ts) = \<infinity>" using inf_ub lnle_def lnless_def by blast 
  hence "#({\<surd>} \<ominus> (Rep_tsynstream ts)) = \<infinity>" sorry
  hence "tsynlen\<cdot>ts = \<infinity>" sorry
  thus False using assms by auto 
qed

lemma tsynstream_fin_induct:
  assumes bottom: "P \<bottom>" 
    and delayfun: "\<And>xs. P xs \<Longrightarrow> P (tsynDelay\<cdot>xs)" 
    and mlscons: "\<And>xs x. P xs \<Longrightarrow> xs\<noteq>\<bottom> \<Longrightarrow> P (tsynMLscons\<cdot>(updis x)\<cdot>xs)"
    and fin: "tsynlen\<cdot>ts < \<infinity>"
  shows "P ts"
proof -
  obtain s where s_def: "Abs_tsynstream s = ts"
    using Rep_tsynstream_inverse by blast
  hence "#s < \<infinity>" 
    using Rep_Abs fin synfinititeTicks sorry
  hence "P (Abs_tsynstream s)"
    using tsynstream_fin_induct_h bottom delayfun mlscons sorry
  thus "P ts" 
    by (simp add: s_def)   
qed     

 
lemma tsynstream_induct [case_names adm bottom delayfun mlscons, induct type: tsynstream]:
fixes ts :: "'a tsynstream"
assumes adm: "adm P" and bottom: "P \<bottom>"  
  and delayfun: "\<And>ts. P ts \<Longrightarrow> P (tsynDelay\<cdot>ts)" 
  and mlscons: "\<And>ts t. P ts\<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow> P (tsynMLscons\<cdot>(updis t)\<cdot>ts)"
shows "P ts" using adm bottom delayfun mlscons tsynstream_fin_induct sorry


(* Case rule *)

lemma tscases:
  assumes bottom: "ts=\<bottom> \<Longrightarrow> P ts"
    and delayfun: "\<And>as. ts=tsynDelay\<cdot>as \<Longrightarrow> P ts"
    and mlscons: "\<And>a as. ts=tsynMLscons\<cdot>(updis a)\<cdot>as \<Longrightarrow> P ts"
  shows "P ts"
  apply (rule_tac xs="Rep_tsynstream ts" in tscases_h)
  using Rep_tsynstream_bottom_iff bottom apply blast sorry

end