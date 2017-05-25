theory fixrec_tstream
(* This theory enables the use of tStreams with fixrec. Especially pattern-matching with the first 
Element of the stream is supported. Hence it is possible to create seperate cases for "first Element is Tick"
and "first element is Message" *)
  
(* Created by Sebastian Stüber.
   sebastian.stueber@rwth-aachen.de *)
  
  
imports TStream

begin

  

thm match_lscons_def
thm stream_case_def
  thm stream_rep_def
(* demo that the old fixrec is not working *)

  (* this function is removing all ticks *)
fixrec demo::"'a event stream \<rightarrow> 'a event stream" where
"t \<noteq> \<bottom> \<Longrightarrow> t=updis \<surd> \<Longrightarrow> demo\<cdot>(lscons\<cdot>t\<cdot>ts) = ts" |
(unchecked) "t \<noteq> \<bottom> \<Longrightarrow> t\<noteq>updis \<surd> \<Longrightarrow> demo\<cdot>(lscons\<cdot>t\<cdot>ts) = t&&ts"


lemma "t \<noteq> \<bottom> \<Longrightarrow> t\<noteq>updis \<surd> \<Longrightarrow> demo\<cdot>(lscons\<cdot>t\<cdot>ts) = t&&ts"
apply fixrec_simp
oops (* good luck proving this :/ *)
  
(***************************************************)      
  section \<open>Using tstream with fixrec\<close>
(***************************************************)        

(* source: https://www.pdx.edu/computer-science/sites/www.pdx.edu.computer-science/files/Huffman.pdf *)
 
    
    
    
    
    
  subsection \<open>Necessary definitions\<close>
    
    
  definition upApply :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a discr u \<rightarrow> 'b discr u" where
"upApply f \<equiv> \<Lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))"

(* ToDo. Definition & show cont *)
definition upApply2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a discr\<^sub>\<bottom> \<rightarrow> 'b discr\<^sub>\<bottom> \<rightarrow> 'c discr\<^sub>\<bottom>" where 
"upApply2 f \<equiv> \<bottom> " (* Is it possible to define upApply2 using upApply ? ? *)


lemma upApply_mono[simp]:"monofun (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b))))"
  apply(rule monofunI)
  apply auto[1]
  by (metis (full_types, hide_lams) discrete_cpo upE up_below)

lemma upApply_lub: assumes "chain Y"
  shows "((\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))) (\<Squnion>i. Y i))
=(\<Squnion>i. (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))) (Y i))"
apply(rule finite_chain_lub)
apply (simp_all add: assms chfin2finch)
done
 
lemma upApply_cont[simp]:"cont (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b))))"
using chfindom_monofun2cont upApply_mono by blast

lemma upApply_rep_eq [simp]: "upApply f\<cdot>(updis a) = updis (f a)"
by(simp add: upApply_def)


  
  
(* get First Element of tStream *)
thm lshd_def  (* similar to lshd *)  
lift_definition tsLshd :: "'a tstream \<rightarrow> 'a event discr u" is
"\<lambda> ts.  lshd\<cdot>(Rep_tstream ts)"
by (simp add: cfun_def)

lemma lshd_eq: "ts\<sqsubseteq>xs \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow> lshd\<cdot>ts = lshd\<cdot>xs"
  using lessD by fastforce

lemma tslshd_eq: "ts\<sqsubseteq>xs \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow> tsLshd\<cdot>ts = tsLshd\<cdot>xs"
  apply(simp add: tsLshd_def lshd_eq)
  by (simp add: Rep_tstream_bottom_iff below_tstream_def lshd_eq)


(* get rest of tStream *)
thm srt_def   (* similar to srt *)
lift_definition tsRt :: "'a tstream \<rightarrow> 'a tstream" is
"\<lambda>ts. espf2tspf srt ts"
by(simp add: espf2tspf_def cfun_def)
  
(* create new tStream by appending a new first Element *)
  (* sadly the function must be ts_well... 
  .. hence for the input (updis Msg m) and the empty stream a special case must be made *)
thm lscons_def (* similar to lscons *)
definition tsLscons :: "'a event discr u \<rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsLscons \<equiv> \<Lambda> t ts. if (ts=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else espf2tspf (lscons\<cdot>t) ts"

lemma lsconc_well [simp]: assumes "ts_well ts" and "ts\<noteq>\<bottom>"
  shows "ts_well (t&&ts)"
apply(auto simp add: ts_well_def)
  apply (metis Rep_Abs assms(1) sConc_Rep_fin_fin stream.con_rews(2) stream.sel_rews(5) surj_scons)
  by (metis Rep_Abs Rep_tstream_bottom_iff assms(1) assms(2) sConc_fin_well stream.con_rews(2) stream.sel_rews(5) surj_scons ts_well_def)    

 lemma lsconc_well2 [simp]: assumes "ts\<noteq>\<bottom>"
  shows "ts_well (t&&(Rep_tstream ts))"
   using Rep_tstream_bottom_iff assms lsconc_well ts_well_Rep by blast
     
lemma lsconc_tick_well[simp]: "ts_well ts \<Longrightarrow> ts_well (updis \<surd> && ts)"
  by (metis lsconc_well sup'_def tick_msg)

lemma tslscons_mono [simp]: "monofun (\<lambda> ts. if (ts=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else espf2tspf (lscons\<cdot>t) ts)"    
  apply(rule monofunI)
    apply (auto simp add: espf2tspf_def below_tstream_def)
  using Rep_tstream_bottom_iff apply blast
  by (metis (mono_tags, hide_lams) Abs_tstream_inverse Rep_tstream Rep_tstream_bottom_iff lsconc_well mem_Collect_eq monofun_cfun_arg)

lemma tslscons_chain2 [simp]: assumes "chain Y" 
  shows "chain (\<lambda>i. if ((Y i)=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else espf2tspf (lscons\<cdot>t) (Y i))" (is "chain (\<lambda>i. ?f (Y i))")
proof -
  have "monofun ?f" by simp
  thus ?thesis by (meson assms monofun_def po_class.chain_def)
qed
 
lemma tslscons_mono2[simp]: "monofun (\<lambda> t ts. if (ts=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else espf2tspf (lscons\<cdot>t) ts)"    
  apply(rule monofunI, rule fun_belowI)
    apply (auto simp add: espf2tspf_def below_tstream_def)
  using stream.inverts apply force
  using stream.inverts apply force
  by (metis Discr_undiscr Exh_Up not_up_less_UU updis_eq2)

lemma tslscons_chain: "chain Y \<Longrightarrow> chain (\<lambda>i. espf2tspf (lscons\<cdot>(updis \<surd>)) (Y i))"
  by (simp add: below_tstream_def po_class.chain_def espf2tspf_def)
    
lemma tslsconc_cont_h: assumes "chain Y" and "t=updis \<surd>"
  shows "Abs_tstream (updis \<surd> && Rep_tstream (Lub Y)) \<sqsubseteq> (\<Squnion>i. Abs_tstream (updis \<surd> && Rep_tstream (Y i)))"
proof -
  have "\<And>i. ts_well (updis \<surd> && Rep_tstream (Y i))" by simp
  hence "chain (\<lambda>i. Abs_tstream (updis \<surd> && Rep_tstream (Y i)))"
    by (metis (no_types, lifting) Rep_Abs assms(1) below_tstream_def monofun_cfun_arg po_class.chain_def)
  thus ?thesis
    by (smt Abs_tstream_inverse Rep_tstream assms(1) below_tstream_def cont2contlubE contlub_cfun_arg lsconc_tick_well lub_eq mem_Collect_eq po_class.chain_def po_eq_conv rep_tstream_cont)
qed      
    
lemma chain_nBot: assumes "chain Y" and  "(\<Squnion>i. Y i) \<noteq>\<bottom>"
  obtains n::nat where "(\<And>i. ((Y (i+n)) \<noteq>\<bottom>))"
  by (metis assms(1) assms(2) bottomI le_add2 lub_eq_bottom_iff po_class.chain_mono)

declare [[show_types]]

lemma tslsconc_cont_h3:"t \<noteq> updis \<surd> \<Longrightarrow>
         chain Y \<Longrightarrow> (\<And>i. Y i \<noteq>\<bottom>) \<Longrightarrow>
         (if (\<Squnion>i. Y i) = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (\<Squnion>i. Y i)) \<sqsubseteq>
         (\<Squnion>i. if Y i = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y i))"
proof -
  assume a1: "chain Y"
  assume a2: "\<And>i. Y i \<noteq> \<bottom>"
  have f3: "\<forall>s. s \<notin> Collect ts_well \<or> Rep_tstream (Abs_tstream s::'a tstream) = s"
    using Abs_tstream_inverse by blast
  have f4: "\<forall>f fa. \<not> cont f \<or> \<not> chain fa \<or> (f (Lub fa::'a tstream)::'a event stream) = (\<Squnion>n. f (fa n))"
    using cont2contlubE by blast
  obtain nn :: "(nat \<Rightarrow> 'a tstream) \<Rightarrow> nat" where
    f5: "\<forall>f. (\<not> chain f \<or> (\<forall>n. f n \<sqsubseteq> f (Suc n))) \<and> (chain f \<or> f (nn f) \<notsqsubseteq> f (Suc (nn f)))"
    using po_class.chain_def by moura
  then have f6: "\<forall>n. Y n \<sqsubseteq> Y (Suc n)"
    using a1 by blast
  then have f7: "(if Y (nn (\<lambda>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))) = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y (nn (\<lambda>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))))) \<sqsubseteq> (if Y (Suc (nn (\<lambda>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n)))) = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y (Suc (nn (\<lambda>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))))))"
    using a2 by (simp add: below_tstream_def espf2tspf_def monofun_cfun_arg)
  obtain nna :: "(nat \<Rightarrow> 'a event stream) \<Rightarrow> (nat \<Rightarrow> 'a event stream) \<Rightarrow> nat" where
    f8: "\<forall>f fa. f (nna fa f) \<noteq> fa (nna fa f) \<or> Lub f = Lub fa"
    by (meson lub_eq)
  have f9: "Rep_tstream (\<Squnion>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n)) = (\<Squnion>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n)))"
    using f7 f5 f4 by (meson rep_tstream_cont)
  have f10: "Rep_tstream (Abs_tstream (t && Rep_tstream (Y (nna (\<lambda>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))) (\<lambda>n. t && Rep_tstream (Y n)))))) = t && Rep_tstream (Y (nna (\<lambda>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))) (\<lambda>n. t && Rep_tstream (Y n))))"
    using f3 a2 lsconc_well2 by blast
  have "Abs_tstream (t && Rep_tstream (Y (nna (\<lambda>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))) (\<lambda>n. t && Rep_tstream (Y n))))) = espf2tspf (lscons\<cdot>t) (Y (nna (\<lambda>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))) (\<lambda>n. t && Rep_tstream (Y n))))"
    by (simp add: espf2tspf_def)
  then have "t && Rep_tstream (Y (nna (\<lambda>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))) (\<lambda>n. t && Rep_tstream (Y n)))) = Rep_tstream (if Y (nna (\<lambda>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))) (\<lambda>n. t && Rep_tstream (Y n))) = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y (nna (\<lambda>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))) (\<lambda>n. t && Rep_tstream (Y n)))))"
    using f10 a2 by fastforce
  then have f11: "(\<Squnion>n. t && Rep_tstream (Y n)) = (\<Squnion>n. Rep_tstream (if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n)))"
    using f8 by meson
  obtain nnb :: "(nat \<Rightarrow> 'a event stream) \<Rightarrow> nat" where
    f12: "\<forall>f. (\<not> chain f \<or> (\<forall>n. f n \<sqsubseteq> f (Suc n))) \<and> (chain f \<or> f (nnb f) \<notsqsubseteq> f (Suc (nnb f)))"
    using po_class.chain_def by moura
  { assume "Abs_tstream (Rep_tstream (if Lub Y \<noteq> \<bottom> \<or> t = updis \<surd> then espf2tspf (lscons\<cdot>t) (Lub Y) else \<bottom>)) = Abs_tstream (Rep_tstream (\<Squnion>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n)))"
    then have "(\<Squnion>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n)) = (if Lub Y \<noteq> \<bottom> \<or> t = updis \<surd> then espf2tspf (lscons\<cdot>t) (Lub Y) else \<bottom>)"
      by simp
    then have "(if Lub Y \<noteq> \<bottom> \<or> t = updis \<surd> then espf2tspf (lscons\<cdot>t) (Lub Y) else \<bottom>) \<sqsubseteq> (\<Squnion>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))"
      using po_eq_conv by blast }
  moreover
  { assume "Abs_tstream (Rep_tstream (if Lub Y \<noteq> \<bottom> \<or> t = updis \<surd> then espf2tspf (lscons\<cdot>t) (Lub Y) else \<bottom>)) \<noteq> Abs_tstream (Rep_tstream (\<Squnion>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n)))"
    then have "Abs_tstream (Rep_tstream (if Lub Y \<noteq> \<bottom> \<or> t = updis \<surd> then espf2tspf (lscons\<cdot>t) (Lub Y) else \<bottom>)) \<noteq> espf2tspf (lscons\<cdot>t) (Lub Y)"
      using f12 f11 f9 f6 f4 a1 by (metis (no_types) below_tstream_def contlub_cfun_arg espf2tspf_def rep_tstream_cont)
    then have "(if Lub Y \<noteq> \<bottom> \<or> t = updis \<surd> then espf2tspf (lscons\<cdot>t) (Lub Y) else \<bottom>) \<sqsubseteq> (\<Squnion>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))"
      by fastforce }
  ultimately have "(if Lub Y \<noteq> \<bottom> \<or> t = updis \<surd> then espf2tspf (lscons\<cdot>t) (Lub Y) else \<bottom>) \<sqsubseteq> (\<Squnion>n. if Y n = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y n))"
    by fastforce
  then show ?thesis
    by presburger
qed

lemma tslsconc_cont_h2: assumes "t \<noteq> updis \<surd>" and "chain Y"
    shows "(if (\<Squnion>i. Y i) = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (\<Squnion>i. Y i)) \<sqsubseteq>
         (\<Squnion>i. if Y i = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y i))" (is "?f (\<Squnion>i. Y i) \<sqsubseteq> ?x")
  proof(cases "(\<Squnion>i. Y i) = \<bottom>")
    case True
    then show ?thesis by (simp add: assms)
  next
    case False
    have f_chain: "chain (\<lambda>i. ?f (Y i))"  by (simp add: assms(2))
    obtain n  where n_def: "(\<And>i. ((Y ( i+n)) \<noteq>\<bottom>))"  using False assms(2) chain_nBot False by blast
    have lub_eq: "(\<Squnion>i. Y(i+n)) = (\<Squnion>i. Y i)" by(simp add: lub_range_shift assms)
    hence "?f (\<Squnion>i. Y (i+n)) \<sqsubseteq> (\<Squnion>i. ?f (Y (i+n)))" using assms(1) assms(2) chain_shift n_def tslsconc_cont_h3 by blast
    also have "?f (\<Squnion>i. Y (i+n)) = ?f (\<Squnion>i. Y i)" using assms(2) lub_range_shift2 by fastforce
    also have "(\<Squnion>i. ?f (Y (i+n))) = (\<Squnion>i. ?f (Y i))" using f_chain lub_range_shift2 by fastforce
    finally show ?thesis by simp
  qed 
    
lemma tslscons_cont: "cont (\<lambda> ts. if (ts=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else espf2tspf (lscons\<cdot>t) ts)"    
  apply(rule contI2)
   apply simp
  apply(cases "t\<noteq>updis \<surd>")
  using tslsconc_cont_h2 apply fastforce 
   by (simp add: tslsconc_cont_h tslsconc_cont_h2 espf2tspf_def)

lemma tslscons_cont2[simp]: "cont (\<lambda> t . \<Lambda> ts. if (ts=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else espf2tspf (lscons\<cdot>t) ts)"    
proof -
  obtain uu :: "('a event discr\<^sub>\<bottom> \<Rightarrow> 'a tstream \<Rightarrow> 'a tstream) \<Rightarrow> 'a event discr\<^sub>\<bottom>" and tt :: "('a event discr\<^sub>\<bottom> \<Rightarrow> 'a tstream \<Rightarrow> 'a tstream) \<Rightarrow> 'a tstream" where
    f1: "\<forall>f. \<not> cont (f (uu f)) \<or> \<not> cont (\<lambda>u. f u (tt f)) \<or> cont (\<lambda>u. Abs_cfun (f u))"
    by (metis (no_types) cont2cont_LAM)
  have "\<forall>t. monofun (\<lambda>u. if (t::'a tstream) = \<bottom> \<and> u \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>u) t)"
    using mono2mono_fun tslscons_mono2 by fastforce
  then have "cont (\<lambda>t. if t = \<bottom> \<and> uu (\<lambda>u t. if t = \<bottom> \<and> u \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>u) t) \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot> (uu (\<lambda>u t. if t = \<bottom> \<and> u \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>u) t))) t) \<and> cont (\<lambda>u. if tt (\<lambda>u t. if t = \<bottom> \<and> u \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>u) t) = \<bottom> \<and> u \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>u) (tt (\<lambda>u t. if t = \<bottom> \<and> u \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>u) t)))"
    using chfindom_monofun2cont tslscons_cont by blast
  then show ?thesis
    using f1 by presburger
qed
  
  
lemma tslscons_insert: "tsLscons\<cdot>t\<cdot>ts = (if (ts=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else espf2tspf (lscons\<cdot>t) ts)"
  unfolding tsLscons_def
  by (simp only: beta_cfun tslscons_cont2 tslscons_cont)

lemma tslscons_bot[simp]: "tsLscons\<cdot>\<bottom>\<cdot>ts = \<bottom>"
  by(auto simp add: tslscons_insert tsLshd_def espf2tspf_def)

lemma tslscons_bot2[simp]: "tsLscons\<cdot>(updis \<surd>)\<cdot>\<bottom>= Abs_tstream (updis \<surd> && \<bottom>)"
  by(auto simp add: tslscons_insert tsLshd_def espf2tspf_def)
    
lemma tslscons_bot3[simp]: "t\<noteq>(updis \<surd>) \<Longrightarrow> tsLscons\<cdot>t\<cdot>\<bottom>= \<bottom>"
  by(auto simp add: tslscons_insert tsLshd_def espf2tspf_def)    
    
lemma tslscons_nbot [simp]: "t\<noteq>\<bottom> \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow> tsLscons\<cdot>t\<cdot>ts \<noteq>\<bottom>"
  unfolding tslscons_insert
  by (simp add: espf2tspf_def)

lemma tslscons_lshd [simp]: "ts\<noteq>\<bottom> \<Longrightarrow> tsLshd\<cdot>(tsLscons\<cdot>t\<cdot>ts) = t"
by(auto simp add: tslscons_insert tsLshd_def espf2tspf_def)  

lemma tslscons_lshd2 [simp]: "tsLshd\<cdot>(tsLscons\<cdot>(updis \<surd>)\<cdot>ts) = (updis \<surd>)"
  by(auto simp add: tslscons_insert tsLshd_def espf2tspf_def)  

lemma tslscons_srt [simp]: "t\<noteq>\<bottom> \<Longrightarrow> tsRt\<cdot>(tsLscons\<cdot>t\<cdot>ts) = ts"
by(auto simp add: tslscons_insert tsRt_def espf2tspf_def)  

lemma tslscons_srt2 [simp]: "tsRt\<cdot>(tsLscons\<cdot>(updis \<surd>)\<cdot>ts) = ts"
  by(auto simp add: tslscons_insert tsRt_def espf2tspf_def)  
    
    
  
(* Das darf man gerne schöner nennen *)
definition tsMLscons :: "'a discr u \<rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsMLscons \<equiv> \<Lambda> t ts. tsLscons\<cdot>(upApply Msg\<cdot>t)\<cdot>ts"

(* remove the Msg layer. Return bottom on ticks *)
lift_definition unpackMsg::"'a event discr u \<rightarrow> 'a discr u" is
  "\<lambda>t. upApply (\<lambda>x. case x of Msg m \<Rightarrow> m )\<cdot>t"
  using Cfun.cfun.Rep_cfun by blast
  
  
    
lemma tsabs_bot[simp]: "tsAbs\<cdot>\<bottom>=\<bottom>"
  by(simp add: tsabs_insert)

lemma "tsAbs\<cdot>(Abs_tstream ((upApply Msg\<cdot>t)&&ts)) = t&&tsAbs\<cdot>(Abs_tstream ts)"
  oops
  
lemma "ts\<noteq>\<bottom> \<Longrightarrow> tsAbs\<cdot>(tsMLscons\<cdot>t\<cdot>ts) = t && tsAbs\<cdot>ts"
  apply(simp add: tsMLscons_def, auto simp add: upApply_def)  
  apply(auto simp add: tslscons_insert espf2tspf_def)
oops
    
  
  
    subsection \<open>Match definitions\<close>
  (* used with fixrec, see link above *)    
  
definition
  match_tstream :: "'a tstream \<rightarrow> ('a event discr u \<rightarrow> 'a tstream \<rightarrow> ('b ::cpo) match) \<rightarrow> 'b match" where
  "match_tstream = (\<Lambda> xs k.  strictify\<cdot>(\<Lambda> xs. k\<cdot>(tsLshd\<cdot>xs)\<cdot>(tsRt\<cdot>xs))\<cdot>xs)" (*testing a different definition *)
  (* if(xs=\<bottom>) then Fixrec.fail else k\<cdot>(tsLshd\<cdot>xs)\<cdot>(tsRt\<cdot>xs)) " *)

  (* match if first element is tick *)
definition match_delayfun:: "'a tstream \<rightarrow> ('a tstream \<rightarrow> ('b ::cpo) match) \<rightarrow> 'b match" where
 "match_delayfun = (\<Lambda> ts k. match_tstream\<cdot>ts\<cdot>(\<Lambda> a . k))"
 (* (\<Lambda> ts k . if (tsLshd\<cdot>ts\<noteq>updis \<surd>) then Fixrec.fail else match_tstream\<cdot>ts\<cdot>(\<Lambda> a . k))"  *)
  
 (* match if first element is message *) 
definition match_message:: "'a tstream \<rightarrow> ('a discr u \<rightarrow> 'a tstream \<rightarrow> ('b ::cpo) match) \<rightarrow> 'b match" where
 "match_message = (\<Lambda> ts k . if (tsLshd\<cdot>ts=updis \<surd>) then Fixrec.fail else match_tstream\<cdot>ts\<cdot>(\<Lambda> a xs . k\<cdot>(unpackMsg\<cdot>a)\<cdot>xs))" 
 
 (* match if first element is message *) 
definition match_tick:: "'a event discr \<rightarrow> ('b ::cpo) match \<rightarrow> 'b match" where
 "match_tick = (\<Lambda> t k . if t=(Discr \<surd>) then k else Fixrec.fail)" 
    
definition DiscrTick :: "'a event discr" where
  "DiscrTick = Discr \<surd>"
  
lemma match_tick_simps [simp]:
  "a\<noteq>\<surd> \<Longrightarrow> match_tick\<cdot>(Discr a)\<cdot>k = Fixrec.fail"
  "t\<noteq>DiscrTick \<Longrightarrow> match_tick\<cdot>t\<cdot>k = Fixrec.fail"
  "match_tick\<cdot>(Discr \<surd>)\<cdot>k = k"
  "match_tick\<cdot>DiscrTick\<cdot>k = k"
  by (simp_all add: match_tick_def DiscrTick_def)

  
     subsection \<open>Lemmata for match definitions\<close>

  (* ToDo: cont-stuff for die match-sachen *)
lemma match_tstream_cont [simp]:  "monofun (\<lambda> xs . if(xs=\<bottom>) then Fixrec.fail else k\<cdot>(tsLshd\<cdot>xs)\<cdot>(tsRt\<cdot>xs))"
  apply(rule monofunI)
    apply auto
  oops  


  (* maybe an extra condition is required... t\<noteq>\<bottom> and/or ts\<noteq>\<bottom> e.g. *)
lemma match_tstream_simps [simp]:
  "match_tstream\<cdot>\<bottom>\<cdot>k = \<bottom>"
  "ts\<noteq>\<bottom> \<Longrightarrow> t\<noteq>\<bottom> \<Longrightarrow> match_tstream\<cdot>(tsLscons\<cdot>t\<cdot>ts)\<cdot>k = k\<cdot>t\<cdot>ts" 
  "match_tstream\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts)\<cdot>k = k\<cdot>(up\<cdot>DiscrTick)\<cdot>ts"
  "match_tstream\<cdot>(delayFun\<cdot>ts)\<cdot>k = k\<cdot>(up\<cdot>DiscrTick)\<cdot>ts"
    apply (simp_all add: match_tstream_def DiscrTick_def)
    sorry
(* unfolding match_tstream_def apply simp_all *)

     
lemma "monofun (\<lambda>ts. if ts=\<bottom>then Fixrec.fail else match_tstream\<cdot>ts\<cdot>(\<Lambda> a . k))"
  apply(rule monofunI)
apply (auto simp add: match_tstream_def)
  using monofun_cfun_arg sorry

lemma match_delayfun_simps [simp]:
  "match_delayfun\<cdot>\<bottom>\<cdot>k = \<bottom>"
  "match_delayfun\<cdot>(tsLscons\<cdot>(updis (Msg m))\<cdot>ts)\<cdot>k = k\<cdot>ts"
  "match_delayfun\<cdot>(tsLscons\<cdot>(updis \<surd>)\<cdot>ts)\<cdot>k = k\<cdot>ts" 
  "tsLshd\<cdot>ts = updis \<surd> \<Longrightarrow> match_delayfun\<cdot>ts\<cdot>k = k\<cdot>ts"
  "tsLshd\<cdot>ts = updis (Msg m) \<Longrightarrow> match_delayfun\<cdot>ts\<cdot>k = k\<cdot>ts" 
  "match_delayfun\<cdot>(tsMLscons\<cdot>t\<cdot>ts)\<cdot>k = Fixrec.fail"
  "match_delayfun\<cdot>(delayFun\<cdot>ts)\<cdot>k = k\<cdot>ts" (* important *)
    unfolding match_delayfun_def
          apply (auto simp add: match_tstream_def)
      sorry
(* lemma match_delayfun_simps [simp]:
  "match_delayfun\<cdot>\<bottom>\<cdot>k = Fixrec.fail"
  "match_delayfun\<cdot>(tsLscons\<cdot>(updis (Msg m))\<cdot>ts)\<cdot>k = Fixrec.fail"
  "match_delayfun\<cdot>(tsLscons\<cdot>(updis \<surd>)\<cdot>ts)\<cdot>k = k\<cdot>ts" 
  "tsLshd\<cdot>ts = updis \<surd> \<Longrightarrow> match_delayfun\<cdot>ts\<cdot>k = k\<cdot>ts"
  "tsLshd\<cdot>ts = updis (Msg m) \<Longrightarrow> match_delayfun\<cdot>ts\<cdot>k = Fixrec.fail" 
  "match_delayfun\<cdot>(tsMLscons\<cdot>t\<cdot>ts)\<cdot>k = Fixrec.fail"
  "match_delayfun\<cdot>(delayFun\<cdot>ts)\<cdot>k = k\<cdot>ts" (* important *)
  unfolding match_delayfun_def
  apply auto
  sorry *)
    
lemma match_message_simps [simp]:
  "match_message\<cdot>\<bottom>\<cdot>k = \<bottom>" (* Fixrec.fail" *)
  "match_message\<cdot>(tsMLscons\<cdot>t\<cdot>ts)\<cdot>k = k\<cdot>t\<cdot>ts"
  "match_message\<cdot>(delayFun\<cdot>ts)\<cdot>k = \<bottom>" (*  Fixrec.fail"*)
  sorry
    
setup \<open>
  Fixrec.add_matchers
    [ (@{const_name tsLscons}, @{const_name match_tstream}) , 
      (@{const_name delayFun}, @{const_name match_delayfun}),
      (@{const_name tsMLscons}, @{const_name match_message}),
      (@{const_name DiscrTick}, @{const_name match_tick})
    ]
\<close>

  
  
  
  (* Case Studies *)

  

fixrec teees:: "'a tstream \<rightarrow>'a tstream" where
"ts\<noteq>\<bottom> \<Longrightarrow> teees\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = tsInfTick" |  (* t is a 'event discr u', ts a tstream *)
"t\<noteq>DiscrTick \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow> teees\<cdot>(tsLscons\<cdot>(up\<cdot>t)\<cdot>ts) = ts"

lemma [simp]: "teees\<cdot>\<bottom> = \<bottom>"
  by(fixrec_simp)

    (* First Element is a Tick *)
lemma "teees\<cdot>(delayFun\<cdot>ts) = tsInfTick"
  by fixrec_simp
    
    (* First Element is not a Tick *)
lemma "t\<noteq>DiscrTick \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow> teees\<cdot>(tsLscons\<cdot>(up\<cdot>t)\<cdot>ts) = ts"
  by simp

lemma "teees\<cdot>\<bottom>= \<bottom>"
  by simp
    
lemma "ts=\<bottom> \<Longrightarrow> teees\<cdot>(tsLscons\<cdot>t\<cdot>ts) = ts"
  by(fixrec_simp)
    
(* removes first tick (if there is a first tick *)
fixrec tee :: "'a tstream \<rightarrow> 'a tstream" where
"tee\<cdot>(delayFun\<cdot>ts) = ts"  (* this pattern is only called if the input stream starts with a tick *)

fixrec tsAbsNew :: "'a tstream \<rightarrow> 'a stream" where
"tsAbsNew\<cdot>(tsMLscons\<cdot>t\<cdot>ts) = t && tsAbsNew\<cdot>ts" | (* prepend first message and go on *)  
"tsAbsNew\<cdot>(delayFun\<cdot>ts) = tsAbsNew\<cdot>ts"   (* ignore ticks *)  



    
fixrec tsZipNew:: "'a stream \<rightarrow> 'b tstream \<rightarrow> ('a\<times>'b) tstream" where
"x\<noteq>\<bottom> \<Longrightarrow> tsZipNew\<cdot>(lscons\<cdot>x\<cdot>xs)\<cdot>(tsMLscons\<cdot>t\<cdot>ts) = (tsMLscons\<cdot>(upApply2 Pair\<cdot>x\<cdot>t)\<cdot>(tsZipNew\<cdot>xs\<cdot>ts))"  | (* zip if both first elements are defined *)
"x\<noteq>\<bottom> \<Longrightarrow> tsZipNew\<cdot>(lscons\<cdot>x\<cdot>xs)\<cdot>(delayFun\<cdot>ts) = delayFun\<cdot>(tsZipNew\<cdot>xs\<cdot>ts)"  (* ignore ticks *)
(* No other cases required, stuff that does not match will go to bottom *)

  




(* Gimmick *)
thm match_Pair_def
thm  match_up_def
definition match_ibottom :: "('a::cpo) u \<rightarrow> ('c ::cpo) match \<rightarrow> 'c match" where
  "match_ibottom = (\<Lambda> x k. case x of Ibottom \<Rightarrow> k | _ \<Rightarrow> Fixrec.fail)"

setup \<open>
  Fixrec.add_matchers
    [ (@{const_name Ibottom}, @{const_name match_ibottom})]\<close>
  
lemma match_ibottom_simps [simp]:
(*   "match_ibottom\<cdot>\<bottom>\<cdot>k = Fixrec.fail" *)
  "match_ibottom\<cdot>(up\<cdot>a)\<cdot>k = Fixrec.fail"
  "match_ibottom\<cdot>Ibottom\<cdot>k = k"
  sorry
  
fixrec tsRemDupsNew :: "'a discr u \<rightarrow> 'a tstream \<rightarrow> 'a tstream" where
(* No element found yet: *)
"tsRemDupsNew\<cdot>Ibottom\<cdot>(tsMLscons\<cdot>t\<cdot>ts) = tsMLscons\<cdot>t\<cdot>(tsRemDupsNew\<cdot>t\<cdot>ts)" |     (* Element found, prepend it and save it *)
"tsRemDupsNew\<cdot>Ibottom\<cdot>(delayFun\<cdot>ts) = delayFun\<cdot>(tsRemDupsNew\<cdot>Ibottom\<cdot>ts)"  |   (* Ignore Ticks *)
"tsRemDupsNew\<cdot>(up\<cdot>a)\<cdot>(delayFun\<cdot>ts) = delayFun\<cdot>(tsRemDupsNew\<cdot>(up\<cdot>a)\<cdot>ts)"  |      (* Ignore Ticks *)
"tsRemDupsNew\<cdot>(up\<cdot>a)\<cdot>(tsMLscons\<cdot>t\<cdot>ts) = \<bottom>" (* ToDo *)                         (* remove duplicate or save new element *)
  
  *)
  
end  