(*  Title:        TStreamTheorie_HK.thy
*)

chapter {* Timed Streams *}                                                              

theory TStream_HK

imports TStream
begin


primrec list2ts_alter :: "'a event list \<Rightarrow> 'a tstream"
where
  list2ts_alter_0:   "list2ts_alter [] = \<bottom>" |
  list2ts_alter_Suc: "list2ts_alter (a#as) = tsLscons\<cdot> (updis a) \<cdot>(list2ts_alter as)"

(*Test tsRemDups*)
lemma "tsRemDups\<cdot>(<[Msg 1, Msg 1, Tick, Msg 1]>\<surd>) = <[Msg 1, Tick]>\<surd>"
  apply (simp add: tsremdups_insert)
  by (simp add: tsmlscons_lscons tsremdups_h_delayfun)


(*Lemmas für TStream.thy*)

(*Tests tsProjFst*)
lemma "tsProjFst\<cdot>(<[Msg (1, 11), Msg (2, 12), Tick]>\<surd>) = <[Msg 1, Msg 2, Tick]>\<surd>"
  apply(simp add: tsProjFst_def)
  by (metis (mono_tags, lifting) delayfun_nbot tsmlscons_nbot tsprojfst_delayfun tsprojfst_insert 
  tsprojfst_mlscons tsprojfst_strict up_defined)

lemma "tsProjFst\<cdot>(<[Msg (1, 11), Msg (2, 12), Tick, Msg (100, 200)]>\<surd>) = <[Msg 1, Msg 2, Tick]>\<surd>"
  apply(simp add: tsProjFst_def)
  by (metis (mono_tags, lifting) delayfun_nbot tsmlscons_nbot tsprojfst_delayfun tsprojfst_insert 
  tsprojfst_mlscons tsprojfst_strict up_defined)  

(************************************************)
  subsection \<open>list2ts\<close>    
(************************************************)
thm tslscons_bot2
    
    (* NIEEE: Abs_tstream (updis \<surd> && \<epsilon>) *)
lemma "list2tsM [Msg 1, Msg 2, Tick, Msg 3, Tick, Msg 4] = s"
  apply simp
  oops

lemma list2ts_empty [simp]: "list2ts_alter [] = \<bottom>"
  by simp

lemma list2ts_onetick: "list2ts_alter[\<surd>]= Abs_tstream (updis \<surd> && \<bottom>)"
  by (simp add: tslscons_insert espf2tspf_def)

lemma list2ts_onemsg[simp]:"a\<noteq>\<surd> \<Longrightarrow> list2ts_alter[a] =\<bottom> "
  by simp

lemma list2ts_tickfirst:"list2ts_alter (\<surd>#as) =(Abs_tstream(<[\<surd>]>)) \<bullet> list2ts_alter as"
  apply (simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  apply (subst lscons_conv)+
  by (simp add: tsconc_insert)

lemma list2ts_nottickfirst:"a\<noteq>\<surd> \<and> as=(b # \<surd> # bs) \<Longrightarrow>list2ts_alter (a#as) =Abs_tstream (\<up>a \<bullet> Rep_tstream (list2ts_alter as))"
  apply (simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  by (simp add: lscons_conv)

lemma tstickcount_lscons1: "t\<noteq>\<surd> \<Longrightarrow> #\<surd> tsLscons\<cdot>(updis t)\<cdot>ts = #\<surd> (ts)"
  apply (cases "ts=\<bottom>", simp)
  apply (subst tslscons2lscons,simp)
  apply (simp add: tslscons2lscons tstickcount_insert)
  by (metis lscons_conv sfilter_nin singletonD)

lemma tstickcount_lscons2: " #\<surd> tsLscons\<cdot>(updis \<surd>)\<cdot>ts = lnsuc\<cdot>(#\<surd> (ts))"
  apply (cases "ts=\<bottom>", simp)
  apply (metis DiscrTick_def delayFun_dropFirst delayfun_nbot delayfun_tslscons_bot strict_tstickcount
  tsdropfirst_len)
  apply (subst tslscons2lscons,simp)
  apply (simp add: tslscons2lscons tstickcount_insert)
  by (simp add: lscons_conv)


lemma "#\<surd> (list2ts_alter l) \<le> #\<surd> (list2ts_alter (a#l))"
  apply(cases "a=\<surd>",simp)
  apply (metis DiscrTick_def delayfun_insert delayfun_tslscons less_lnsuc tstickcount_tscons)
  by(simp add:tstickcount_lscons1)
  

lemma list2ts_nbot2[simp]:"list2ts_alter (a@[\<surd>])\<noteq>\<bottom>"
  by (induction a, simp+)

lemma list2ts_nbot1[simp]: "list2ts_alter (a@\<surd>#as)\<noteq>\<bottom>"
  by(induction a, simp+)

lemma list2ts_unfold1:"a\<noteq>\<surd> \<Longrightarrow>list2ts_alter (a # b @ [\<surd>]) =Abs_tstream (\<up>a \<bullet> Rep_tstream (list2ts_alter (b @ [\<surd>])))"
  apply (simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  by (simp add: lscons_conv)

lemma list2ts_droplist: "filter (\<lambda>e. e=\<surd>) as =[] \<Longrightarrow> list2ts_alter as = \<bottom>"
  apply (induction as, simp)
  apply (subgoal_tac "a\<noteq>\<surd>")
  apply (simp add: tslscons_insert)
  by auto

lemma list2ts_unfold2:"a \<noteq> \<surd> \<Longrightarrow> list2ts_alter (a # b @ \<surd> # bs) = Abs_tstream (\<up>a \<bullet> Rep_tstream (list2ts_alter (b @ \<surd> # bs)))"
  apply(induction bs)
  apply(subst list2ts_unfold1,auto)
  apply(simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  by (simp add: lscons_conv)

lemma list2ts_split:"list2ts_alter (a @ \<surd> # as) = (list2ts_alter (a @ [\<surd>])) \<bullet> (list2ts_alter as)"
  apply (induction a, simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  apply (simp add: lscons_conv tsconc_insert)
  apply (simp add: tslscons_insert, auto)
  by (simp add: espf2tspf_def lscons_conv tsconc_insert)+

lemma list2ts_dropend:"filter (\<lambda>e. e=\<surd>) as=[] \<Longrightarrow> list2ts_alter (a @ \<surd> # as) = list2ts_alter(a @ [\<surd>])"
  by(subst list2ts_split, simp add: list2ts_droplist)
  

lemma list2ts_lshd1 [simp]: "a\<noteq>[] \<Longrightarrow> tsLshd\<cdot>(list2ts_alter (a @ [\<surd>])) = updis (hd a)"
  apply(induction a,simp)
  by (metis append_Cons list.sel(1) list2ts_alter_Suc list2ts_nbot2 tslscons_lshd)

lemma list2ts_lshd_tick [simp]: "tsLshd\<cdot>(list2ts_alter (\<surd> # a)) = updis \<surd>"
  by simp

lemma list2ts_srt [simp]: "t\<noteq>\<bottom> \<Longrightarrow> tsRt\<cdot>(list2ts_alter (a # as)) = list2ts_alter (as)"
  by simp

lemma list2ts_lshd [simp]: "a\<noteq>[] \<Longrightarrow> tsLshd\<cdot>(list2ts_alter (a @ \<surd> # as)) = updis (hd a)"
  by(induction a, simp+)

lemma list2ts2list2s_lscons: "list2ts_alter (a # as @ [\<surd>]) = Abs_tstream (lscons\<cdot>(updis a)\<cdot>(list2s (as@[\<surd>])))"
  apply (induction as arbitrary: a, simp+)
  apply (auto simp add: tslscons_insert espf2tspf_def lscons_conv)
  apply (metis list2ts_nbot1 lscons_conv tslscons2lscons tslscons_nbot up_defined)
  apply (subst Rep_Abs)
  apply (auto simp add: ts_well_def)
  apply (simp add: less_le slen_lnsuc)
  apply (metis sconc_scons)
  apply (subst Rep_Abs)
  apply (auto simp add: ts_well_def)
  apply (simp add: less_le slen_lnsuc)
  by (metis sconc_scons)


lemma [simp]:" #({\<surd>} \<ominus> <ls>) \<noteq> \<infinity>"
apply (subgoal_tac "#(<ls>)\<noteq>\<infinity>")
using sfilterl4 apply blast
by simp

lemma list2ts2list2s_well[simp]:"ts_well (list2s ls) \<Longrightarrow> Rep_tstream (list2ts_alter ls) = list2s (ls)"
  apply(induction ls, simp+)
  by (smt Rep_Abs Rep_tstream_inverse absts2tslscons lscons_conv sconc_fst_empty stream.con_rews(2) 
  stream.sel_rews(5) tick_msg ts_well_conc tslscons_insert tslscons_lscons up_defined)

lemma list2s2list2ts_well[simp]:"ts_well (list2s ls) \<Longrightarrow>  Abs_tstream (list2s ls) = list2ts_alter (ls)"
  apply(induction ls, simp+)
  by (smt Rep_Abs Rep_tstream_inverse absts2tslscons lscons_conv sconc_fst_empty stream.con_rews(2) 
  stream.sel_rews(5) tick_msg ts_well_conc tslscons_insert tslscons_lscons up_defined)

(*Test*)
lemma testlist2ts: "list2ts_alter ([\<M> True,\<M> False, \<surd>,\<M> False]) = Abs_tstream (<[Msg True,Msg False,\<surd>]>)"
  apply (simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  apply (subst lscons_conv)+
  by simp

(*Test*)
lemma testlist2tsM: "list2tsM ([\<M> True,\<M> False, \<surd>,\<M> False]) = tsMLscons\<cdot>(updis True)\<cdot>(tsMLscons\<cdot>(updis False)\<cdot>(delayFun\<cdot>\<bottom>))"
  by (simp add: tslscons_insert)

(*list2s*)
lemma list2s_sfoot_ntk:"b\<noteq>\<surd> \<Longrightarrow> sfoot (<(a@[b])>) \<noteq> \<surd> "
  apply(subst sfoot1, simp)
  by (simp add: less_le slen_lnsuc,simp)
  

lemma tswell_list:"ls \<noteq> [] \<Longrightarrow> last ls \<noteq>\<surd> \<Longrightarrow> \<not> ts_well (list2s ls)"
  apply (simp add: ts_well_def, auto)
  using list2s_inj apply fastforce
  by (smt append_butlast_last_id list2s_sfoot_ntk sfoot1)

lemma list2ts_tsntimes:"ts_well (list2s as) \<Longrightarrow>tsntimes n (list2ts_alter as) = tsntimes n (Abs_tstream (list2s as))"
  by simp


lemma list2ts_tsinftimes2: "tsinftimes (list2ts_alter (as@[\<surd>])) = tsinftimes (Abs_tstream (list2s (as@[\<surd>])))"
  apply (subst list2s2list2ts_well,auto)
  apply (simp add: ts_well_def, auto)
  by (simp add: less_le slen_lnsuc)
  
end