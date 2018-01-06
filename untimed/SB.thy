theory SB
  imports "../UBundle" Streams
begin

default_sort message

type_synonym 'm SB = "'m stream ubundle"

instantiation stream :: (message) uscl_pcpo
begin

  definition usOkay_stream_def: "usOkay c m \<equiv> sdom\<cdot>m \<subseteq> ctype c"
  
  definition usLen_stream_def: "usLen \<equiv> slen"
  
  instance
    apply intro_classes
    apply (rule admI)
     apply (simp add: usOkay_stream_def l44)
    by (simp add: usOkay_stream_def)
  
  
  end

definition sbRt :: "'m SB \<rightarrow> 'm SB" where
"sbRt \<equiv> \<Lambda> sb. ubMapStream (Rep_cfun srt) sb"

definition sbHdElem :: "'m SB \<rightarrow> (channel \<rightharpoonup> 'm discr\<^sub>\<bottom>)" where
"sbHdElem \<equiv> \<Lambda> sb. (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))" 

definition convDiscrUp :: "(channel \<rightharpoonup> 'm) \<Rightarrow> (channel \<rightharpoonup> 'm discr\<^sub>\<bottom>)" where
"convDiscrUp sb \<equiv> (\<lambda>c. (c \<in> dom sb) \<leadsto> (Iup (Discr (sb \<rightharpoonup> c))))"


section \<open>Lemma\<close>

subsection \<open>sbRt\<close>

lemma sbrt_okay: "usOkay c s \<Longrightarrow> usOkay c (srt\<cdot>s)"
  apply(simp add: usOkay_stream_def)
  by (metis (no_types, lifting) Un_iff sdom2un stream.sel_rews(2) subsetCE subsetI surj_scons)


lemma sbrt_cont [simp]: "cont (ubMapStream (Rep_cfun srt))"
  by (simp add: sbrt_okay ubMapStream_contI2)



  
(* ----------------------------------------------------------------------- *)
  subsection \<open>sbHdElem\<close>
(* ----------------------------------------------------------------------- *)    

lemma sbHdElem_mono: "monofun (\<lambda> sb::'a SB. (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c))))"  
proof(rule monofunI) 
  fix x y ::"'a SB"
  assume "x \<sqsubseteq> y"
  then show "(\<lambda> sb::'a SB. (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))) x \<sqsubseteq> (\<lambda> sb::'a SB. (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))) y"
    by (smt below_option_def fun_below_iff monofun_cfun_arg option.discI option.sel ubdom_below)
qed  
  
lemma sbHdElem_cont_pre: assumes "chain Y" shows "(\<lambda>c. (c \<in> ubDom\<cdot>(\<Squnion>i. Y i))\<leadsto>lshd\<cdot>((\<Squnion>i. Y i) . c)) \<sqsubseteq> (\<Squnion>i. (\<lambda>c. (c \<in> ubDom\<cdot>(Y i))\<leadsto>lshd\<cdot>(Y i . c)))"
proof - 
  fix c
  have "(\<lambda>c. (c \<in> ubDom\<cdot>(\<Squnion>i. Y i))\<leadsto>lshd\<cdot>((\<Squnion>i. Y i) . c)) c \<sqsubseteq> (\<Squnion>i. (\<lambda>c. (c \<in> ubDom\<cdot>(Y i))\<leadsto>lshd\<cdot>(Y i . c)) c)"
  proof(cases "c \<in> ubDom\<cdot>(\<Squnion>i. Y i)")
    case True
    have f1: "\<And>i. ubDom\<cdot>(\<Squnion>i. Y i) =  ubDom\<cdot>(Y i)"
      by (simp add: assms)
    then show ?thesis 
      apply(simp add: True)
    proof -
      have "Some (lshd\<cdot>(\<Squnion>n. Y n . c)) \<sqsubseteq> (\<Squnion>n. Some (lshd\<cdot>(Y n . c)))"
        by (metis assms ch2ch_Rep_cfunL ch2ch_Rep_cfunR if_then_lub)
      then show "Some (lshd\<cdot>(Lub Y . c)) \<sqsubseteq> (\<Squnion>n. Some (lshd\<cdot>(Y n . c)))"
        by (simp add: assms contlub_cfun_arg)
    qed
  next
    case False
    then show ?thesis
      using assms by auto 
  qed  
  then show ?thesis
    by (smt assms cont_pref_eq1I contlub_cfun_arg contlub_lambda eq_imp_below fun_belowI if_then_lub lub_eq op_is_lub optionLub_def po_class.chain_def some_below ubdom_chain_eq2)
qed  
    
lemma sbHdElem_cont: "cont (\<lambda> sb::'a SB. (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c))))"  
  apply(rule contI2)
  apply(auto simp add: sbHdElem_mono sbHdElem_cont_pre)
  using sbHdElem_mono sbHdElem_cont_pre by fastforce

end