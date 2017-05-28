theory fixrec_tstream
(* This theory enables the use of tStreams with fixrec. Especially pattern-matching with the first 
Element of the stream is supported. Hence it is possible to create seperate cases for "first Element is Tick"
and "first element is Message" *)
  
(* Created by Sebastian Stüber.
   sebastian.stueber@rwth-aachen.de *)
  
  
imports TStream

begin

  
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
 
subsection \<open>Definitions\<close>  
  
        
lift_definition uMsg :: "'a discr \<rightarrow> 'a event discr" is
"\<lambda> t. case t of (Discr m) \<Rightarrow> (Discr (Msg m))"
  by(simp add: cfun_def)


(* remove the Msg layer. Return bottom on ticks *)
lift_definition unpackMsg::"'a event discr u \<rightarrow> 'a discr u" is
  "\<lambda>t. upApply (\<lambda>x. case x of Msg m \<Rightarrow> m )\<cdot>t"
  using Cfun.cfun.Rep_cfun by blast
  
    
thm lshd_def  (* similar to lshd *)  
(* get First Element of tStream *)
lift_definition tsLshd :: "'a tstream \<rightarrow> 'a event discr u" is
"\<lambda> ts.  lshd\<cdot>(Rep_tstream ts)"
by (simp add: cfun_def)

  
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

(* Das darf man gerne schöner nennen *)
definition tsMLscons :: "'a discr u \<rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsMLscons \<equiv> \<Lambda> t ts. tsLscons\<cdot>(upApply Msg\<cdot>t)\<cdot>ts"



    
    
    
    
subsection \<open>Lemma for definitinos\<close>    
  
lemma upapply2umsg [simp]: "upApply Msg\<cdot>(up\<cdot>x) = up\<cdot>(uMsg\<cdot>x)"  
apply(simp add: upapply_insert uMsg_def)
  by (metis (mono_tags) Discr_undiscr discr.case the_equality undiscr_def)  

lemma lshd_eq: "ts\<sqsubseteq>xs \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow> lshd\<cdot>ts = lshd\<cdot>xs"
  using lessD by fastforce

lemma tslshd_eq: "ts\<sqsubseteq>xs \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow> tsLshd\<cdot>ts = tsLshd\<cdot>xs"
  apply(simp add: tsLshd_def)
  by (simp add: Rep_tstream_bottom_iff below_tstream_def lshd_eq)

    
    
    
lemma lscons_well [simp]: assumes "ts_well ts" and "ts\<noteq>\<bottom>"
  shows "ts_well (t&&ts)"
apply(auto simp add: ts_well_def)
  apply (metis Rep_Abs assms(1) sConc_Rep_fin_fin stream.con_rews(2) stream.sel_rews(5) surj_scons)
  by (metis Rep_Abs Rep_tstream_bottom_iff assms(1) assms(2) sConc_fin_well stream.con_rews(2) stream.sel_rews(5) surj_scons ts_well_def)    

 lemma lsconc_well2 [simp]: assumes "ts\<noteq>\<bottom>"
  shows "ts_well (t&&(Rep_tstream ts))"
   using Rep_tstream_bottom_iff assms lscons_well ts_well_Rep by blast
     
lemma lscons_tick_well[simp]: "ts_well ts \<Longrightarrow> ts_well (updis \<surd> && ts)"
  by (metis lscons_well sup'_def tick_msg)

lemma tslscons_mono [simp]: "monofun (\<lambda> ts. if (ts=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else espf2tspf (lscons\<cdot>t) ts)"    
  apply(rule monofunI)
    apply (auto simp add: espf2tspf_def below_tstream_def)
  using Rep_tstream_bottom_iff apply blast
  by (metis (mono_tags, hide_lams) Abs_tstream_inverse Rep_tstream Rep_tstream_bottom_iff lscons_well mem_Collect_eq monofun_cfun_arg)

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
    by (smt Abs_tstream_inverse Rep_tstream assms(1) below_tstream_def cont2contlubE contlub_cfun_arg lscons_tick_well lub_eq mem_Collect_eq po_class.chain_def po_eq_conv rep_tstream_cont)
qed      

lemma tslscons_cont_h3:"t \<noteq> updis \<surd> \<Longrightarrow>
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

lemma tslscons_cont_h2: assumes "t \<noteq> updis \<surd>" and "chain Y"
    shows "(if (\<Squnion>i. Y i) = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (\<Squnion>i. Y i)) \<sqsubseteq>
         (\<Squnion>i. if Y i = \<bottom> \<and> t \<noteq> updis \<surd> then \<bottom> else espf2tspf (lscons\<cdot>t) (Y i))" (is "?f (\<Squnion>i. Y i) \<sqsubseteq> ?x")
  proof(cases "(\<Squnion>i. Y i) = \<bottom>")
    case True
    then show ?thesis by (simp add: assms)
  next
    case False
    have f_chain: "chain (\<lambda>i. ?f (Y i))"  by (simp add: assms(2))
    obtain n  where n_def: "(\<And>i. ((Y ( i+n)) \<noteq>\<bottom>))"  using False assms(2) chain_nbot False by blast
    have lub_eq: "(\<Squnion>i. Y(i+n)) = (\<Squnion>i. Y i)" by(simp add: lub_range_shift assms)
    hence "?f (\<Squnion>i. Y (i+n)) \<sqsubseteq> (\<Squnion>i. ?f (Y (i+n)))" using assms(1) assms(2) chain_shift n_def tslscons_cont_h3 by blast
    also have "?f (\<Squnion>i. Y (i+n)) = ?f (\<Squnion>i. Y i)" using assms(2) lub_range_shift2 by fastforce
    also have "(\<Squnion>i. ?f (Y (i+n))) = (\<Squnion>i. ?f (Y i))" using f_chain lub_range_shift2 by fastforce
    finally show ?thesis by simp
  qed 
    
lemma tslscons_cont: "cont (\<lambda> ts. if (ts=\<bottom> & t\<noteq>updis \<surd>) then \<bottom> else espf2tspf (lscons\<cdot>t) ts)"    
  apply(rule contI2)
   apply simp
  apply(cases "t\<noteq>updis \<surd>")
  using tslscons_cont_h2 apply fastforce 
   by (simp add: tslsconc_cont_h tslscons_cont_h2 espf2tspf_def)

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

lemma tslscons_nbot2[simp]: "tsLscons\<cdot>(updis \<surd>)\<cdot>ts\<noteq>\<bottom>"
  by(auto simp add: tslscons_insert tsLshd_def espf2tspf_def)
        
lemma tslscons_lshd [simp]: "ts\<noteq>\<bottom> \<Longrightarrow> tsLshd\<cdot>(tsLscons\<cdot>t\<cdot>ts) = t"
by(auto simp add: tslscons_insert tsLshd_def espf2tspf_def)  

lemma tslscons_lshd2 [simp]: "tsLshd\<cdot>(tsLscons\<cdot>(updis \<surd>)\<cdot>ts) = (updis \<surd>)"
  by(auto simp add: tslscons_insert tsLshd_def espf2tspf_def)  

lemma tslscons_srt [simp]: "t\<noteq>\<bottom> \<Longrightarrow> tsRt\<cdot>(tsLscons\<cdot>t\<cdot>ts) = ts"
by(auto simp add: tslscons_insert tsRt_def espf2tspf_def)  

lemma tslscons_srt2 [simp]: "tsRt\<cdot>(tsLscons\<cdot>(updis \<surd>)\<cdot>ts) = ts"
  by(auto simp add: tslscons_insert tsRt_def espf2tspf_def)  

    
lemma tsrt_delayfun[simp]: "tsRt\<cdot>(delayFun\<cdot>ts) = ts"
  by (simp add: delayFun_def tsRt_def espf2tspf_def tsconc_rep_eq)
    
lemma tslshd_delayfun[simp]: "tsLshd\<cdot>(delayFun\<cdot>ts) = updis \<surd>"  
    by (simp add: delayFun_def tsLshd_def espf2tspf_def tsconc_rep_eq)
  
    
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
  "match_tstream = (\<Lambda> xs k.  strictify\<cdot>(\<Lambda> xs. k\<cdot>(tsLshd\<cdot>xs)\<cdot>(tsRt\<cdot>xs))\<cdot>xs)"
  
 (* match if first element is message *) 
definition match_tick:: "'a event discr \<rightarrow> ('b ::cpo) match \<rightarrow> 'b match" where
 "match_tick = (\<Lambda> t k . if t=(Discr \<surd>) then k else Fixrec.fail)" 
    
definition DiscrTick :: "'a event discr" where
  "DiscrTick = Discr \<surd>"





  
     subsection \<open>Lemmata for match definitions\<close>

lemma delayfun_nbot[simp]: "delayFun\<cdot>ts \<noteq> \<bottom>"
  by(simp add: delayFun_def)  
        
  (* maybe an extra condition is required... t\<noteq>\<bottom> and/or ts\<noteq>\<bottom> e.g. *)
lemma match_tstream_simps [simp]:
  "match_tstream\<cdot>\<bottom>\<cdot>k = \<bottom>"
  "ts\<noteq>\<bottom> \<Longrightarrow> t\<noteq>\<bottom> \<Longrightarrow> match_tstream\<cdot>(tsLscons\<cdot>t\<cdot>ts)\<cdot>k = k\<cdot>t\<cdot>ts" 
  "match_tstream\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts)\<cdot>k = k\<cdot>(up\<cdot>DiscrTick)\<cdot>ts"
  "match_tstream\<cdot>(delayFun\<cdot>ts)\<cdot>k = k\<cdot>(up\<cdot>DiscrTick)\<cdot>ts"
  "xs\<noteq>\<bottom>\<Longrightarrow> match_tstream\<cdot>(tsMLscons\<cdot>(up\<cdot>x)\<cdot>xs)\<cdot>k = k\<cdot>(up\<cdot>(uMsg\<cdot>x))\<cdot>xs"
     by(simp_all add: match_tstream_def DiscrTick_def tsMLscons_def uMsg_def)

definition match_umsg:: "'a event discr \<rightarrow> ('a discr \<rightarrow> 'b::cpo match) \<rightarrow> 'b match"  where
"match_umsg = (\<Lambda> t k. case t of (Discr (Msg m)) \<Rightarrow> k\<cdot>(Discr m) | _\<Rightarrow>Fixrec.fail)"

lemma match_umsg_mono: "monofun (\<lambda>k. case t of (Discr (Msg m)) \<Rightarrow> k\<cdot>(Discr m) | _\<Rightarrow>Fixrec.fail)"
  apply(rule monofunI)
  apply(cases "\<exists>m. t = Discr (Msg m)", auto)
  apply (simp add: monofun_cfun_fun)
  by (metis Discr_undiscr discr.case event.exhaust event.simps(5) po_eq_conv)

lemma match_umsg_cont[simp]: "cont (\<lambda>k. case t of (Discr (Msg m)) \<Rightarrow> k\<cdot>(Discr m) | _\<Rightarrow>Fixrec.fail)"
  apply(rule contI2)
  apply(simp add: match_umsg_mono)
  apply(cases "\<exists>m. t = Discr (Msg m)", auto)
  using contlub_cfun_fun po_eq_conv apply blast
  using Discr_undiscr discr.case event.exhaust event.simps(5) po_eq_conv by (smt below_lub po_class.chain_def)

lemma match_umsg_insert: "match_umsg\<cdot>t\<cdot>k = (case t of (Discr (Msg m)) \<Rightarrow> k\<cdot>(Discr m) | _\<Rightarrow>Fixrec.fail)"
by(simp add: match_umsg_def)  
  
   
    
lemma match_tick_simps [simp]:
  "a\<noteq>\<surd> \<Longrightarrow> match_tick\<cdot>(Discr a)\<cdot>k = Fixrec.fail"
  "b\<noteq>(Discr \<surd>) \<Longrightarrow> match_tick\<cdot>b\<cdot>k = Fixrec.fail"
  "t\<noteq>DiscrTick \<Longrightarrow> match_tick\<cdot>t\<cdot>k = Fixrec.fail"
  "match_tick\<cdot>(uMsg\<cdot>m)\<cdot>k = Fixrec.fail"
  "match_tick\<cdot>(Discr \<surd>)\<cdot>k = k"
  "match_tick\<cdot>DiscrTick\<cdot>k = k"
  apply (auto simp add: match_tick_def DiscrTick_def uMsg_def)
  by (metis Discr_undiscr discr.case event.distinct(1) undiscr_Discr)

lemma match_umsg_simps [simp]:
  "match_umsg\<cdot>(Discr \<surd>)\<cdot>k = Fixrec.fail"
  "match_umsg\<cdot>DiscrTick\<cdot>k = Fixrec.fail"
  "match_umsg\<cdot>(Discr (Msg m))\<cdot>k = k\<cdot>(Discr m)"
  "match_umsg\<cdot>(uMsg\<cdot>m2)\<cdot>k = k\<cdot>m2"
  unfolding match_umsg_insert
  apply (auto simp add: DiscrTick_def)
  by (metis (mono_tags, lifting) Abs_cfun_inverse2 Discr_undiscr cont_discrete_cpo discr.case event.case(1) uMsg_def)
   
setup \<open>
  Fixrec.add_matchers
    [ (@{const_name tsLscons},  @{const_name match_tstream}) , 
      (@{const_name DiscrTick}, @{const_name match_tick}),
      (@{const_name uMsg},      @{const_name match_umsg})
    ]
\<close>

  (*
lemma match_up_simps2 [simp]: 
  "match_up\<cdot>(upApply f\<cdot>(up\<cdot>x))\<cdot>k = k\<cdot>(f x)"
apply(simp add: match_up_def upapply_insert)  
 *) 
 
  (* Case Studies *)

fixrec teees:: "'a tstream \<rightarrow>'a tstream" where
"teees\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = tsInfTick" |  (* t is a 'event discr u', ts a tstream *)
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
    

 
    
    
(* removes first tick (if there is a first tick *)
fixrec tee :: "'a tstream \<rightarrow> 'a tstream" where
"tee\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = ts"  (* this pattern is only called if the input stream starts with a tick *)

fixrec tsAbsNew :: "'a tstream \<rightarrow> 'a stream" where
"tsAbsNew\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = tsAbsNew\<cdot>ts" |   (* ignore ticks *)  
"ts\<noteq>\<bottom> \<Longrightarrow> tsAbsNew\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) = up\<cdot>t && tsAbsNew\<cdot>ts"  (* prepend first message and go on *)  

lemma [simp]: "tsAbsNew\<cdot>\<bottom>=\<bottom>"
  by fixrec_simp

lemma [simp]: "tsAbsNew\<cdot>(delayFun\<cdot>ts) = tsAbsNew\<cdot>ts"
  by fixrec_simp

lemma [simp]: "tsAbs\<cdot>(delayFun\<cdot>ts) = tsAbs\<cdot>ts"
  by(simp add: delayFun_def)
    
lemma tsabs_new_msg [simp]: "xs\<noteq>\<bottom> \<Longrightarrow> tsAbsNew\<cdot>(tsMLscons\<cdot>(up\<cdot>x)\<cdot>xs) = up\<cdot>x && (tsAbsNew\<cdot>xs)"
  by fixrec_simp+

  
lemma tsabs_SORRY: "xs\<noteq>\<bottom> \<Longrightarrow> tsAbs\<cdot>(tsMLscons\<cdot>(up\<cdot>x)\<cdot>xs) = up\<cdot>x && (tsAbs\<cdot>xs)"
  apply(subst tsabs_insert)
  oops    
    

lemma tstream_induct_tslscons [case_names Bot tsLscons, induct type: tstream]:
  fixes ts
  assumes "adm P" and "P \<bottom>" and "\<And>xs x. P xs\<Longrightarrow> x\<noteq>\<bottom>\<Longrightarrow>xs\<noteq>\<bottom>\<Longrightarrow> P (tsLscons\<cdot>x\<cdot>xs)"
  shows "P ts"
  apply(induction ts, rename_tac xs)
  apply simp
  apply(induct_tac xs)
    apply(auto simp add: assms)
   apply(rule admI)
  oops

lemma tstream_induct [case_names Bot tsLscons, induct type: tstream]:
  fixes ts
  assumes "P \<bottom>" and "\<And>xs. P xs \<Longrightarrow> P (delayFun\<cdot>xs)" and "\<And>xs x. P xs\<Longrightarrow> x\<noteq>\<bottom>\<Longrightarrow>xs\<noteq>\<bottom>\<Longrightarrow> P (tsMLscons\<cdot>x\<cdot>xs)"
  shows "P ts"
  apply(induction ts, rename_tac s)
  oops
    
lemma "tsAbsNew\<cdot>ts = tsAbs\<cdot>ts"
  oops
    (*
  apply(induct ts)
    apply (simp_all add: tsabs_SORRY)
  by (metis tsabs_SORRY tsabs_new_msg upE)
*)


(*    
   (* only the general idea *)
fixrec tsZipNew:: "'a stream \<rightarrow> 'b tstream \<rightarrow> ('a\<times>'b) tstream" where
"x\<noteq>\<bottom> \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow> tsZipNew\<cdot>(lscons\<cdot>x\<cdot>xs)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) 
    =tsMLscons\<cdot>(upApply2 Pair\<cdot>x\<cdot>(up\<cdot>t))\<cdot>(tsZipNew\<cdot>xs\<cdot>ts) " |  (* zip if both first elements are defined *)

"x\<noteq>\<bottom> \<Longrightarrow> tsZipNew\<cdot>(lscons\<cdot>x\<cdot>xs)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) 
    = delayFun\<cdot>(tsZipNew\<cdot>xs\<cdot>ts)"  (* ignore ticks *)
(* No other cases required, stuff that does not match will go to bottom *)

*)
end  