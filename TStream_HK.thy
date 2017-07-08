(*  Title:        TStreamTheorie_HK.thy
*)

chapter {* Timed Streams *}                                                              

theory TStream_HK

imports TStream
begin

  (* Vorschlag fuer abbreviation: *)
  (* <[Msg 1]>\<surd>  *)
primrec list2ts :: "'a event list \<Rightarrow> 'a tstream"
where
  list2ts_0:   "list2ts [] = \<bottom>" |
  list2ts_Suc: "list2ts (a#as) = (tsLscons\<cdot>(updis a)\<cdot>(list2ts as))"

abbreviation tstream_abbrev :: "'a event list \<Rightarrow> 'a tstream" ("<_>\<surd>" [1000] 999)
where "<l>\<surd> == list2ts l"

primrec list2ts_alter :: "'a event list \<Rightarrow> 'a tstream"
where
  list2ts_alter_0:   "list2ts_alter [] = \<bottom>" |
  list2ts_alter_Suc: "list2ts_alter (a#as) = (if a=\<surd> then delayFun\<cdot>(list2ts_alter as) else (tsMLscons\<cdot>(updis \<M>\<inverse> a)\<cdot>(list2ts_alter as)))"



(************************************************)
  subsection \<open>list2ts\<close>    
(************************************************)
thm tslscons_bot2
    
    (* NIEEE: Abs_tstream (updis \<surd> && \<epsilon>) *)
lemma "list2ts [Msg 1, Msg 2, Tick, Msg 3, Tick, Msg 4] = s"
  apply simp
  oops

lemma list2ts_empty [simp]: "list2ts [] = \<bottom>"
  by simp

lemma list2ts_onetick: "list2ts[\<surd>]= Abs_tstream (updis \<surd> && \<bottom>)"
  by (simp add: tslscons_insert espf2tspf_def)

lemma list2ts_onemsg[simp]:"a\<noteq>\<surd> \<Longrightarrow> list2ts[a] =\<bottom> "
  by simp

lemma list2ts_tickfirst:"list2ts (\<surd>#as) =(Abs_tstream(<[\<surd>]>)) \<bullet> list2ts as"
  apply (simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  apply (subst lscons_conv)+
  by (simp add: tsconc_insert)

lemma list2ts_nottickfirst:"a\<noteq>\<surd> \<and> as=(b # \<surd> # bs) \<Longrightarrow>list2ts (a#as) =Abs_tstream (\<up>a \<bullet> Rep_tstream (list2ts as))"
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


lemma "#\<surd> (list2ts l) \<le> #\<surd> (list2ts (a#l))"
  apply(cases "a=\<surd>",simp)
  apply (metis DiscrTick_def delayfun_insert delayfun_tslscons less_lnsuc tstickcount_tscons)
  by(simp add:tstickcount_lscons1)
  

lemma list2ts_nbot2[simp]:"list2ts (a@[\<surd>])\<noteq>\<bottom>"
  by (induction a, simp+)

lemma list2ts_nbot1[simp]: "list2ts (a@\<surd>#as)\<noteq>\<bottom>"
  by(induction a, simp+)

lemma list2ts_unfold1:"a\<noteq>\<surd> \<Longrightarrow>list2ts (a # b @ [\<surd>]) =Abs_tstream (\<up>a \<bullet> Rep_tstream (list2ts (b @ [\<surd>])))"
  apply (simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  by (simp add: lscons_conv)

lemma list2ts_droplist: "filter (\<lambda>e. e=\<surd>) as =[] \<Longrightarrow> list2ts as = \<bottom>"
  apply (induction as, simp)
  apply (subgoal_tac "a\<noteq>\<surd>")
  apply (simp add: tslscons_insert)
  by auto

lemma list2ts_unfold2:"a \<noteq> \<surd> \<Longrightarrow> list2ts (a # b @ \<surd> # bs) = Abs_tstream (\<up>a \<bullet> Rep_tstream (list2ts (b @ \<surd> # bs)))"
  apply(induction bs)
  apply(subst list2ts_unfold1,auto)
  apply(simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  by (simp add: lscons_conv)

lemma list2ts_split:"list2ts (a @ \<surd> # as) = (list2ts (a @ [\<surd>])) \<bullet> (list2ts as)"
  apply (induction a, simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  apply (simp add: lscons_conv tsconc_insert)
  apply (simp add: tslscons_insert, auto)
  by (simp add: espf2tspf_def lscons_conv tsconc_insert)+

lemma list2ts_dropend:"filter (\<lambda>e. e=\<surd>) as=[] \<Longrightarrow> list2ts (a @ \<surd> # as) = list2ts(a @ [\<surd>])"
  by(subst list2ts_split, simp add: list2ts_droplist)
  

lemma list2ts_lshd1 [simp]: "a\<noteq>[] \<Longrightarrow> tsLshd\<cdot>(list2ts (a @ [\<surd>])) = updis (hd a)"
  apply(induction a,simp)
  by (metis append_Cons list.sel(1) list2ts_Suc list2ts_nbot2 tslscons_lshd)

lemma list2ts_lshd_tick [simp]: "tsLshd\<cdot>(list2ts (\<surd> # a)) = updis \<surd>"
  by simp

lemma list2ts_srt [simp]: "t\<noteq>\<bottom> \<Longrightarrow> tsRt\<cdot>(list2ts (a # as)) = list2ts (as)"
  by simp

lemma list2ts_lshd [simp]: "a\<noteq>[] \<Longrightarrow> tsLshd\<cdot>(list2ts (a @ \<surd> # as)) = updis (hd a)"
  by(induction a, simp+)

lemma list2ts2list2s_lscons: "list2ts (a # as @ [\<surd>]) = Abs_tstream (lscons\<cdot>(updis a)\<cdot>(list2s (as@[\<surd>])))"
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

lemma list2ts2list2s_well[simp]:"ts_well (list2s ls) \<Longrightarrow> Rep_tstream (list2ts ls) = list2s (ls)"
  apply(induction ls, simp+)
  by (smt Rep_Abs Rep_tstream_inverse absts2tslscons lscons_conv sconc_fst_empty stream.con_rews(2) 
  stream.sel_rews(5) tick_msg ts_well_conc tslscons_insert tslscons_lscons up_defined)

lemma list2s2list2ts_well[simp]:"ts_well (list2s ls) \<Longrightarrow>  Abs_tstream (list2s ls) = list2ts (ls)"
  apply(induction ls, simp+)
  by (smt Rep_Abs Rep_tstream_inverse absts2tslscons lscons_conv sconc_fst_empty stream.con_rews(2) 
  stream.sel_rews(5) tick_msg ts_well_conc tslscons_insert tslscons_lscons up_defined)

(*Test*)
lemma testlist2ts: "list2ts ([\<M> True,\<M> False, \<surd>,\<M> False]) = Abs_tstream (<[Msg True,Msg False,\<surd>]>)"
  apply (simp add: tslscons_insert)
  apply (simp add: espf2tspf_def)+
  apply (subst lscons_conv)+
  by simp

(*Test*)
lemma testlist2ts_alter: "list2ts_alter ([\<M> True,\<M> False, \<surd>,\<M> False]) = tsMLscons\<cdot>(updis True)\<cdot>(tsMLscons\<cdot>(updis False)\<cdot>(delayFun\<cdot>\<bottom>))"
  by (simp add: tslscons_insert)

(*list2s*)
lemma list2s_sfoot_ntk:"b\<noteq>\<surd> \<Longrightarrow> sfoot (<(a@[b])>) \<noteq> \<surd> "
  apply(subst sfoot1, simp)
  by (simp add: less_le slen_lnsuc,simp)
  

lemma tswell_list:"ls \<noteq> [] \<Longrightarrow> last ls \<noteq>\<surd> \<Longrightarrow> \<not> ts_well (list2s ls)"
  apply (simp add: ts_well_def, auto)
  using list2s_inj apply fastforce
  by (smt append_butlast_last_id list2s_sfoot_ntk sfoot1)

lemma list2ts_tsntimes:"ts_well (list2s as) \<Longrightarrow>tsntimes n (list2ts as) = tsntimes n (Abs_tstream (list2s as))"
  by simp


lemma list2ts_tsinftimes2: "tsinftimes (list2ts (as@[\<surd>])) = tsinftimes (Abs_tstream (list2s (as@[\<surd>])))"
  apply (subst list2s2list2ts_well,auto)
  apply (simp add: ts_well_def, auto)
  by (simp add: less_le slen_lnsuc)


(*Lemmas für TStream.thy*)   

lemma tslscons_bot2 [simp]: "t\<noteq>\<surd> \<Longrightarrow>tsLscons\<cdot>(updis t)\<cdot>\<bottom> = \<bottom>"    
    by(auto simp add: tslscons_insert upapply_insert)

lemma tslscons_nbot_rev: "a\<noteq> \<surd> \<Longrightarrow> tsLscons\<cdot>(updis a)\<cdot>as \<noteq> \<bottom> \<Longrightarrow> as\<noteq>\<bottom>"
  using tslscons_bot2 by blast 
 
lemma [simp]:"t \<noteq> \<surd> \<Longrightarrow> uMsg\<cdot>(Discr \<M>\<inverse> t) = Discr t"
by (metis event.exhaust event.simps(4) up_inject upapply2umsg upapply_rep_eq)

(* handle first message *)
lemma tsremdups_h_tslscons_fst2:
"ts\<noteq>\<bottom> \<and> t\<noteq>\<surd> \<Longrightarrow> tsRemDups_h\<cdot>(tsLscons\<cdot>(updis t)\<cdot>ts)\<cdot>None = tsLscons\<cdot>(updis t)\<cdot>(tsRemDups_h\<cdot>ts\<cdot>(Some (Discr (\<M>\<inverse>t))))"
  by (insert tsremdups_h_tslscons_fst [of ts "Discr \<M>\<inverse> t"], simp)


(* handle duplicate message *)
lemma tsremdups_h_tslscons_dup2: 
  "ts\<noteq>\<bottom> \<and> t\<noteq>\<surd> \<Longrightarrow> tsRemDups_h\<cdot>(tsLscons\<cdot>(updis t)\<cdot>ts)\<cdot>(Some (Discr (\<M>\<inverse> t))) = tsRemDups_h\<cdot>ts\<cdot>(Some (Discr (\<M>\<inverse> t)))"
  by (insert tsremdups_h_tslscons_dup [of ts "Discr \<M>\<inverse> t"], simp)

(* handle message *)
lemma tsremdups_h_lscons_ndup2:
  "ts\<noteq>\<bottom> \<Longrightarrow> t\<noteq>a \<Longrightarrow> t\<noteq>\<surd> \<Longrightarrow> a\<noteq>\<surd> \<Longrightarrow> tsRemDups_h\<cdot>(tsLscons\<cdot>(updis t)\<cdot>ts)\<cdot>(Some (Discr (\<M>\<inverse>a))) 
                               = tsLscons\<cdot>(updis t)\<cdot>(tsRemDups_h\<cdot>ts\<cdot>(Some (Discr (\<M>\<inverse>t))))"
  apply (insert tsremdups_h_tslscons_dup[of ts "Discr \<M>\<inverse> t" "Discr (\<M>\<inverse>a)"], auto)
  by (metis event.exhaust event.simps(4))

lemma tsremdups_h_tslscons_dup_2 [simp]: 
  "ts\<noteq>\<bottom> \<Longrightarrow> tsRemDups_h\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts)\<cdot>(Some t) 
          = (tsRemDups_h\<cdot>ts\<cdot>(Some t))"
  by (fixrec_simp)

(*Test tsRemDups*)
lemma "tsRemDups\<cdot>(<[Msg 1, Msg 1, Tick, Msg 1]>\<surd>) = <[Msg 1, Tick]>\<surd>"
  apply (simp add: tsremdups_insert)
  by (metis (no_types, lifting) DiscrTick_def delayfun_tslscons_bot event.distinct(1) tslscons_nbot2 
  tsremdups_h_strict tsremdups_h_tslscons_dup2 tsremdups_h_tslscons_fst2 tsremdups_h_tslscons_tick)


(*Lemmas für TStream.thy*)
lemma tsmap_lscons:
  "ts\<noteq>\<bottom> \<Longrightarrow> tsMap f\<cdot>(tsLscons\<cdot>(updis (\<M> t))\<cdot>ts) = tsLscons\<cdot>(updis (\<M>(f t)))\<cdot>(tsMap f\<cdot>ts)"
  apply (simp add: lscons_conv tsmap_unfold smap_split)
  apply (simp add: tslscons2lscons)
  apply (subst tslscons2lscons)
  apply (metis tsmap_unfold tsmap_strict_rev)
  by (simp add: lscons_conv tsmap_h_well)


lemma tsprojfst_lscons:
  "ts\<noteq>\<bottom> \<Longrightarrow> tsProjFst\<cdot>(tsLscons\<cdot>(updis (\<M>(a,b)))\<cdot>ts) = tsLscons\<cdot>(updis (\<M> a))\<cdot>(tsProjFst\<cdot>ts)"
  by(simp add: tsprojfst_insert tsmap_lscons)

lemma tsprojfst_lscons_bot:
  "tsProjFst\<cdot>(tsLscons\<cdot>(updis \<surd>)\<cdot>ts) = tsLscons\<cdot>(updis (\<surd>))\<cdot>(tsProjFst\<cdot>ts)"
  apply(simp add: tsprojfst_insert tsmap_lscons)
  by (metis DiscrTick_def delayfun_tslscons tsmap_delayfun)

lemma tsprojsnd_lscons:
  "ts\<noteq>\<bottom> \<Longrightarrow> tsProjSnd\<cdot>(tsLscons\<cdot>(updis (\<M>(a,b)))\<cdot>ts) = tsLscons\<cdot>(updis (\<M> b))\<cdot>(tsProjSnd\<cdot>ts)"
  by(simp add: tsprojsnd_insert tsmap_lscons)

(*Tests tsProjFst*)
lemma "tsProjFst\<cdot>(<[Msg (1, 11), Msg (2, 12), Tick]>\<surd>) = <[Msg 1, Msg 2, Tick]>\<surd>"
  by (simp add: tsprojfst_lscons tsprojfst_lscons_bot)

lemma "tsProjFst\<cdot>(<[Msg (1, 11), Msg (2, 12), Tick, Msg (100, 200)]>\<surd>) = <[Msg 1, Msg 2, Tick]>\<surd>"
  by (simp add: tsprojfst_lscons tsprojfst_lscons_bot)
        

end