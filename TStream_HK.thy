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

lemma "#\<surd> (list2ts l) \<le> #\<surd> (list2ts (a#l))"
  apply(cases "a=\<surd>",simp)
  apply (metis DiscrTick_def delayfun_insert delayfun_tslscons less_lnsuc tstickcount_tscons)
  apply simp
  by (smt event.exhaust le_cases3 tsmlscons2tslscons tstickcount_mlscons)

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
  

lemma "tsRemDups\<cdot>(<[Msg 1, Msg 1, Tick, Msg 1]>\<surd>) = <[Msg 1, Tick]>\<surd>"
  apply (simp add: tsremdups_insert)  
  by (metis (no_types) delayfun_tslscons_bot tick_eq_discrtick tslscons_nbot2 tsmlscons2tslscons 
  tsremdups_h_mlscons tsremdups_h_mlscons_dup tsremdups_h_strict tsremdups_h_tslscons_tick)

  
lemma "tsProjFst\<cdot>(<[Msg (1, 11), Msg (2, 12), Tick]>\<surd>) = <[Msg 1, Msg 2, Tick]>\<surd>"
  apply (simp add: tsprojfst_insert tslscons_insert espf2tspf_def)
  apply (simp add: tsmap_unfold lscons_conv)
  by (simp add: ts_well_def)
  (*
  apply simp
  by (metis (no_types, lifting) DiscrTick_def delayfun_tslscons_bot tslscons_nbot tslscons_nbot2 
  tsmlscons2tslscons tsprojfst_delayfun tsprojfst_mlscons tsprojfst_strict up_defined)
  *)
  (*
  apply simp
  proof -
    have "tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot> (\<bottom>::('a \<times> 'b) tstream) \<noteq> \<bottom>"
      by (metis tick_eq_discrtick tslscons_nbot2)
    then have f1: "tsProjFst\<cdot> (tsMLscons\<cdot>(updis (1::'a, 11::'b))\<cdot> (tsLscons\<cdot>(updis (\<M> (2, 12)))\<cdot> (tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>\<bottom>))) = tsMLscons\<cdot>(updis 1)\<cdot> (tsProjFst\<cdot> (tsLscons\<cdot>(updis (\<M> (2, 12::'b)))\<cdot> (tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>\<bottom>)))"
      using tslscons_nbot tsprojfst_mlscons up_defined by blast
    have f2: "tsProjFst\<cdot> (tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot> (\<bottom>::('a \<times> 'b) tstream)) = delayFun\<cdot>\<bottom>"
      by (metis delayfun_tslscons_bot tsprojfst_delayfun tsprojfst_strict)
    have "tsProjFst\<cdot> (tsMLscons\<cdot>(updis (2, 12::'b))\<cdot> (tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>\<bottom>)) = tsMLscons\<cdot>(updis 2)\<cdot> (tsProjFst\<cdot> (tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot> (\<bottom>::('a \<times> 'b) tstream)))"
      by (simp add: tsprojfst_mlscons)
    then show "tsProjFst\<cdot> (tsLscons\<cdot>(updis (\<M> (1::'a, 11::'b)))\<cdot> (tsLscons\<cdot>(updis (\<M> (2, 12)))\<cdot> (tsLscons\<cdot>(updis \<surd>)\<cdot>\<bottom>))) = tsLscons\<cdot>(updis (\<M> 1))\<cdot> (tsLscons\<cdot>(updis (\<M> 2))\<cdot> (tsLscons\<cdot>(updis \<surd>)\<cdot>\<bottom>))"
      using f2 f1 by (simp add: delayfun_tslscons_bot tick_eq_discrtick tsmlscons2tslscons)
  qed
  *)


lemma "tsProjFst\<cdot>(<[Msg (1, 11), Msg (2, 12), Tick, Msg (100, 200)]>\<surd>) = <[Msg 1, Msg 2, Tick]>\<surd>"
  apply (simp add: tsprojfst_insert tslscons_insert espf2tspf_def)
  apply (simp add: tsmap_unfold lscons_conv)
  by (simp add: ts_well_def)
        

end