theory Lift_Srcdups_Lemmas
  imports TStream
begin 

(*First lemma*)
lemma tsRemDups_step: "tsRemDups\<cdot>(updis a &&\<surd> as) = updis a &&\<surd> tsRemDups\<cdot>(tsDropWhile\<cdot>(Discr a)\<cdot>as)"
  apply(simp add: tsRemDups_def)
  apply(induction as, simp_all)
  apply (metis (no_types, lifting) tsdropwhile_delayfun tslscons_srt tsmlscons_bot2 tsmlscons_lscons tsremdups_h_delayfun tsremdups_h_mlscons tsremdups_h_strict up_defined)
  by (metis TStream.tsremdups_eq TStream.tsremdups_neq tsdropwhile_f tsdropwhile_t tsremdups_insert)

(*Second lemma*)
lemma tsremdups_srt_tsabs:"srt\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>(updis a &&\<surd> as))) = tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile\<cdot>(Discr a)\<cdot>as))"
  by (metis lscons_conv srcdups_srt stream.sel_rews(2) strict_srcdups tsabs_bot tsabs_mlscons tsdropwhile_strict tsdropwhile_tsabs tsmlscons_nbot_rev tsremdups_tsabs)  

lemma tsremdups_srt:"tsRt\<cdot>(tsRemDups\<cdot>(updis a &&\<surd> as)) = tsRemDups\<cdot>(tsDropWhile\<cdot>(Discr a)\<cdot>as)"
  by (metis tsRemDups_step tslscons_srt tsmlscons_lscons up_defined)

(*Third lemma*)
lemma tsremdups_prefix_neq:"x \<sqsubseteq> y \<Longrightarrow> tsRemDups\<cdot>x \<noteq>x \<Longrightarrow> tsRemDups\<cdot>y \<noteq> y"
  proof -
    assume a1: "x \<sqsubseteq> y"
    assume a2: "tsRemDups\<cdot>x \<noteq> x"
    obtain nn :: "lnat \<Rightarrow> nat" where
      "\<forall>l. l = \<infinity> \<or> l = Fin (nn l)"
      using ninf2Fin by moura
    then have "\<forall>t ta. (t::'a tstream \<down> nn (#\<surd> ta) = ta \<or> #\<surd> ta = \<infinity>) \<or> ta \<notsqsubseteq> t"
      by (meson ts_approxl1)
    then have "tsRemDups\<cdot>y = y \<longrightarrow> (\<exists>t. tsRemDups\<cdot>t \<notsqsubseteq> y \<and> t \<sqsubseteq> y)"
      using a2 a1 by (metis (no_types) ts_below_eq tsremdups_tstickcount)
    then show ?thesis
      by (metis (no_types) monofun_cfun_arg)
  qed

(*Fourth lemma*)

(*Admissibility*)
lemma tsremdups_tsmap_com_adm [simp]:
  "adm (\<lambda>a. tsRemDups\<cdot>(tsMap f\<cdot>(tsRemDups\<cdot>a)) = tsMap f\<cdot>(tsRemDups\<cdot>a)
     \<longrightarrow> tsRemDups\<cdot>(tsMap f\<cdot>a) = tsMap f\<cdot>(tsRemDups\<cdot>a))"
  apply(rule adm_imp, auto)
  apply(rule adm_upward)
  apply rule+
  using tsremdups_prefix_neq
  by (metis monofun_cfun_arg)

(*First element is an "a"*)
lemma tsremdups_tsmap_com_shd:
  "shd (tsAbs\<cdot>s) = a \<Longrightarrow> tsRemDups\<cdot>(tsMap f\<cdot>(updis a &&\<surd> s)) = tsMap f\<cdot>(tsRemDups\<cdot>(updis a &&\<surd> s))"
  sorry 

(*timed stream is empty or contains only ticks*)
lemma tsremdups_tsmap_com_tsabs_bot:
 "tsAbs\<cdot>s = \<bottom> \<Longrightarrow> tsRemDups\<cdot>(updis (f a) &&\<surd> tsMap f\<cdot>s) = tsMap f\<cdot>(tsRemDups\<cdot>(updis a &&\<surd> s))"
  proof(induction s)
    case adm
    then show ?case 
      by simp
  next
    case bottom
    then show ?case
      by (simp add: tsremdups_insert) 
  next
    case (delayfun s)
    then show ?case 
    apply (simp add: tsremdups_insert)
    apply(simp add: tsmap_delayfun)
    proof -
      have f1: "\<forall>t a f. shd (tsAbs\<cdot>t) \<noteq> (a::'a) \<or> tsRemDups\<cdot>(tsMap f\<cdot>(updis a &&\<surd> t)::'b tstream) = tsMap f\<cdot>(tsRemDups\<cdot>(updis a &&\<surd> t))"
        by (simp add: tsremdups_tsmap_com_shd)        
      have f2: "tsMap f\<cdot>(updis a &&\<surd> updis a &&\<surd> delay s) = updis (f a) &&\<surd> tsMap f\<cdot>(updis a &&\<surd> delay s)"
        by (meson delayfun_nbot tsmap_mlscons tsmlscons_nbot up_defined)
      have "tsMap f\<cdot>(updis a &&\<surd> delay s) = updis (f a) &&\<surd> tsMap f\<cdot>(delay s)"
        by (meson delayfun_nbot tsmap_mlscons)
      then have "tsRemDups\<cdot> (tsMap f\<cdot>(updis a &&\<surd> updis a &&\<surd> delay s)) = tsRemDups\<cdot>(updis (f a) &&\<surd> delay (tsMap f\<cdot>s))"
        using f2 by (simp add: tsRemDups_step tsdropwhile_t tsmap_delayfun)
      then have f3: "tsRemDups\<cdot> (tsMap f\<cdot>(updis a &&\<surd> updis a &&\<surd> delay s)) = tsRemDups_h\<cdot>(updis (f a) &&\<surd> delay (tsMap f\<cdot>s))\<cdot>None"
        using tsremdups_insert by auto
      have "shd (tsAbs\<cdot>(updis a &&\<surd> delay s)) = a"
        by (simp add: lscons_conv tsabs_mlscons)
      then show "tsRemDups_h\<cdot>(updis (f a) &&\<surd> delay (tsMap f\<cdot>s))\<cdot> None = tsMap f\<cdot>(tsRemDups_h\<cdot>(updis a &&\<surd> delay s)\<cdot>None)"
        using f3 f1 by (metis (no_types) tsRemDups_step tsdropwhile_t tsremdups_insert)
    qed
  next
    case (mlscons s t)
    then show ?case
      using stream.con_rews(2) tsabs_mlscons up_defined by force 
  qed

lemma tsremdups_tsmap_com:
  shows "tsRemDups\<cdot>(tsMap f\<cdot>(tsRemDups\<cdot>s)) = tsMap f\<cdot>(tsRemDups\<cdot>s) \<Longrightarrow> tsRemDups\<cdot>(tsMap f\<cdot>s)= tsMap f\<cdot>(tsRemDups\<cdot>s)"
 proof(induction s)
   case adm
   then show ?case 
     by simp
  next
    case bottom
    then show ?case
      by (simp add: tsremdups_insert)    
  next
    case (delayfun s)
    then show ?case
      by (metis tsmap_delayfun tsremdups_h_delayfun tsremdups_insert tsrt_delayfun)
  next
    case (mlscons s t)  
    have s_tsabs_bot: "tsAbs\<cdot>s = \<bottom> \<Longrightarrow> tsRemDups\<cdot>(updis (f a) &&\<surd> tsMap f\<cdot>s) = tsMap f\<cdot>(tsRemDups\<cdot>(updis a &&\<surd> s))"
      by (simp add: tsremdups_tsmap_com_tsabs_bot) 
    hence f1: "shd (tsAbs\<cdot>s) = a  \<Longrightarrow> ?case"
      by (smt lscons_conv mlscons.hyps shd1 tsabs_mlscons tsmap_mlscons tsmlscons_nbot tsremdups_eq tsremdups_tsmap_com_shd up_defined) 
    have f2: "tsAbs\<cdot>s\<noteq>\<bottom> \<Longrightarrow> shd (tsAbs\<cdot>s)\<noteq>a \<Longrightarrow>f (shd (tsAbs\<cdot>s)) \<noteq> f a \<Longrightarrow> ?case"
      by (smt lscons_conv mlscons.hyps shd1 tsRemDups_step tsabs_mlscons tsdropwhile_t tsmap_mlscons tsmlscons_nbot tsremdups_tsmap_com_shd up_defined)     
    have f3: "tsAbs\<cdot>s\<noteq>\<bottom> \<Longrightarrow> shd (tsAbs\<cdot>s)\<noteq>a \<Longrightarrow>f (shd (tsAbs\<cdot>s)) = f a \<Longrightarrow> ?case"
      by (smt lscons_conv mlscons.hyps shd1 tsRemDups_step tsabs_mlscons tsdropwhile_t tsmap_mlscons tsmlscons_nbot tsremdups_tsmap_com_shd up_defined)  
    then show ?case
      by (metis f1 f2 mlscons.hyps tsmap_mlscons tsremdups_tsmap_com_tsabs_bot) 
  qed

end