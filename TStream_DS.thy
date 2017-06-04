(*  Title:        TStream_DS.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Workspace for Development of Functions on Timed Streams
*)

theory TStream_DS
 
imports TStream

begin  

lemma tick_eq_discrtick: "updis \<surd> = up\<cdot>DiscrTick"
by (simp add: DiscrTick_def)

lemma tslscons2lscons: "ts\<noteq>\<bottom> \<Longrightarrow> tsLscons\<cdot>t\<cdot>ts = Abs_tstream (lscons\<cdot>t\<cdot>(Rep_tstream ts))"
by (simp add: tslscons_insert espf2tspf_def)

lemma tslscons_abs: "ts\<noteq>\<bottom> \<Longrightarrow> tsLscons\<cdot>(updis \<surd>)\<cdot>ts = Abs_tstream (updis \<surd> && (Rep_tstream ts))"
by (simp add: tslscons2lscons)

lemma tsmlscons_abs: 
  "ts\<noteq>\<bottom> \<Longrightarrow> tsMLscons\<cdot>(updis t)\<cdot>ts = Abs_tstream (updis (Msg t) && Rep_tstream ts)"
by (simp add: tsMLscons_def tslscons2lscons)

lemma delayfun_abs: "delayFun\<cdot>ts = (Abs_tstream (\<up>\<surd>)\<bullet>ts)"  
by (simp add: delayFun_def)

lemma delayfun_tslscons: "delayFun\<cdot>ts = tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts"
by (simp add: delayFun_def tslscons_insert tsconc_insert DiscrTick_def espf2tspf_def lscons_conv)

lemma delayfun_tslscons_bot: "delayFun\<cdot>\<bottom> = tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>\<bottom>"
by (simp add: delayfun_tslscons tick_eq_discrtick)

lemma tslscons_nbot3 [simp]: "tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts\<noteq>\<bottom>"
by (metis delayfun_nbot delayfun_tslscons)
    
fixrec tsZip :: "'a tstream \<rightarrow> 'b stream \<rightarrow> ('a \<times> 'b) tstream" where
  (* Bottom case *)
"tsZip\<cdot>ts\<cdot>\<bottom> = \<bottom>" | 

  (* One Message, then directly a Tick. Return Pair an Tick directly. 
    (Neccessary, because if the 'stream' ends we would not return a Tick) *)
"x\<noteq>\<bottom> \<Longrightarrow>                
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts))\<cdot>(x && xs)
                            = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>t)\<cdot>x)\<cdot>(delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs))" | 

  (* two messages in tStream. Work on the first *)
"x\<noteq>\<bottom> \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow>              
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t2))\<cdot>ts))\<cdot>(x && xs) 
                            = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>t)\<cdot>x)\<cdot>(tsZip\<cdot>(tsMLscons\<cdot>(up\<cdot>t2)\<cdot>ts)\<cdot>xs)" | 

  (* ignore ticks *)
"xs\<noteq>\<bottom> \<Longrightarrow> 
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts)\<cdot>xs = delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs)"

lemma tszip_strict [simp]: 
"tsZip\<cdot>\<bottom>\<cdot>\<epsilon> = \<bottom>"
"tsZip\<cdot>ts\<cdot>\<epsilon> = \<bottom>"
"tsZip\<cdot>\<bottom>\<cdot>s = \<bottom>"
by (fixrec_simp)+

lemma tszip_tslscons_fixrec: "x\<noteq>\<bottom>  \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow>               
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t2))\<cdot>ts))\<cdot>(x && xs) 
                            = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>t)\<cdot>x)\<cdot>(tsZip\<cdot>(tsMLscons\<cdot>(up\<cdot>t2)\<cdot>ts)\<cdot>xs)"
by (fixrec_simp)

lemma tszip_tslscons_fixrec_tick: "x\<noteq>\<bottom> \<Longrightarrow>           
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts))\<cdot>(lscons\<cdot>x\<cdot>xs)
                            = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>t)\<cdot>x)\<cdot>(delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs))"
by (fixrec_simp)

lemma tszip_tslscons_tick_fixrec: "xs\<noteq>\<bottom> \<Longrightarrow> 
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts)\<cdot>xs = delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs)"
by (fixrec_simp)

lemma tszip_mlscons:
  "tsZip\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>(tsMLscons\<cdot>(updis u)\<cdot>ts))\<cdot>((updis x) && xs)
                           = tsMLscons\<cdot>(updis (t,x))\<cdot>(tsZip\<cdot>(tsMLscons\<cdot>(updis u)\<cdot>ts)\<cdot>xs)"
by (metis (no_types, lifting) tsmlscons_bot2 tsmlscons_lscons tszip_strict(3) tszip_tslscons_fixrec
    up_defined upapply2_rep_eq)

lemma tszip_mlscons_delayfun:
  "tsZip\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>(delayFun\<cdot>ts))\<cdot>((updis x) && xs)
                           = tsMLscons\<cdot>(updis (t,x))\<cdot>(delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs))"
by (metis (no_types, lifting) delayfun_tslscons tsmlscons_lscons tszip_tslscons_fixrec_tick 
    up_defined upapply2_rep_eq)

lemma tszip_delayfun: "xs\<noteq>\<epsilon> \<Longrightarrow> tsZip\<cdot>(delayFun\<cdot>ts)\<cdot>xs = delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs)"
by (simp add: delayfun_tslscons)

lemma 
  "tsZip\<cdot>(Abs_tstream (<[Msg 1, \<surd>, Msg 2, \<surd>]>))\<cdot>(<[True, False]>) = Abs_tstream (<[Msg (1, True), \<surd>, Msg (2, False), \<surd>]>)"
proof -
  have f1: "updis (\<surd>::'a event) && <[]> = \<up>\<surd>"
    by (simp add: sup'_def)
  then have f2: "ts_well (updis (\<surd>::'a event) && <[]>)"
    by (metis tick_msg)
  have f3: "ts_well (updis (\<M> 2::'a) && <[\<surd>]>)"
    by auto
  have f4: "delayFun\<cdot>(Abs_tstream (updis (\<M> 2::'a) && <[\<surd>]>)) = Abs_tstream (updis \<surd> && <[]>) \<bullet> Abs_tstream (updis (\<M> 2) && <[\<surd>]>)"
    using f1 delayfun_abs by auto
  have f5: "Rep_tstream (Abs_tstream (updis \<surd> && <[]>) \<bullet> Abs_tstream (updis (\<M> 2::'a) && <[\<surd>]>)) = <[\<surd>, \<M> 2, \<surd>]>"
    using f3 f2 f1 by (metis (no_types) list2s.simps(2) lscons_conv tsconc_rep_eq1)
  have f6: "updis (\<surd>::('a \<times> bool) event) && <[]> = \<up>\<surd>"
    by (metis list2s_0 sup'_def)
  have f7: "Rep_tstream (Abs_tstream (updis (\<surd>::('a \<times> bool) event) && <[]>) \<bullet> \<bottom>) = <[\<surd>]>"
    by (simp add: lscons_conv)
  have f8: "tsMLscons\<cdot>(updis (2::'a))\<cdot>(delayFun\<cdot>\<bottom>) = Abs_tstream (updis (\<M> 2) && <[\<surd>]>)"
    by (simp add: delayfun_abs tsmlscons_abs)
  have f9: "Rep_tstream (Abs_tstream (updis \<surd> && <[]>) \<bullet> Abs_tstream (updis (\<M> (2::'a, False)) && <[\<surd>]>)) = (updis \<surd> && <[]>) \<bullet> updis (\<M> (2, False)) && <[\<surd>]>"
    by (simp add: tsconc_rep_eq1)
  have "Abs_tstream (updis \<surd> && <[]>) \<bullet> Abs_tstream (updis (\<M> (2::'a, False)) && <[\<surd>]>) \<noteq> \<bottom>"
    using f6 by force
  then have f10: "tsMLscons\<cdot>(updis (1::'a, True))\<cdot> (Abs_tstream (updis \<surd> && <[]>) \<bullet> Abs_tstream (updis (\<M> (2, False)) && <[\<surd>]>)) = Abs_tstream (updis (\<M> (1, True)) && Rep_tstream (Abs_tstream (updis \<surd> && <[]>) \<bullet> Abs_tstream (updis (\<M> (2, False)) && <[\<surd>]>)))"
    using tsmlscons_abs by blast
  have f11: "tsMLscons\<cdot>(updis (2::'a, False))\<cdot> (Abs_tstream (updis \<surd> && <[]>) \<bullet> \<bottom>) = Abs_tstream (updis (\<M> (2, False)) && Rep_tstream (Abs_tstream (updis \<surd> && <[]>) \<bullet> \<bottom>))"
    by (simp add: lscons_conv tsmlscons_abs)
  have "Abs_tstream (updis \<surd> && <[]>) \<bullet> Abs_tstream (updis (\<M> 2::'a) && <[\<surd>]>) \<noteq> \<bottom>"
    using f1 by auto
  then show ?thesis
    using f11 f10 f9 f8 f7 f6 f5 f4 by (metis (no_types) delayfun_abs list2s.simps(2) list2s_0 lscons_conv tsmlscons_abs tszip_mlscons_delayfun tszip_strict(2))
qed

(* ToDo: useful for tsMLscons representation *)
lemma tsmap_mlscons:
  "ts \<noteq> \<bottom> \<Longrightarrow> tsMap f\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>ts) = tsMLscons\<cdot>(updis (f t))\<cdot>(tsMap f\<cdot>ts)"
oops

lemma tsmap_delayfun: "tsMap f\<cdot>(delayFun\<cdot>ts) = delayFun\<cdot>(tsMap f\<cdot>ts)"
oops

lemma tsprojfst_mlscons:
  "ts \<noteq> \<bottom> \<Longrightarrow> tsProjFst\<cdot>(tsMLscons\<cdot>(updis (a,b))\<cdot>ts) = tsMLscons\<cdot>(updis a)\<cdot>(tsProjFst\<cdot>ts)"
oops

lemma tsprojsnd_mlscons:
  "ts \<noteq> \<bottom> \<Longrightarrow> tsProjSnd\<cdot>(tsMLscons\<cdot>(updis (a,b))\<cdot>ts) = tsMLscons\<cdot>(updis a)\<cdot>(tsProjSnd\<cdot>ts)"
oops

lemma tsfilter_mlscons:
  "ts \<noteq> \<bottom> \<Longrightarrow> tsFilter M\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>ts) = tsMLscons\<cdot>(updis t)\<cdot>(tsFilter M\<cdot>ts)"
oops

lemma tsfilter_delayfun: "tsFilter M\<cdot>(delayFun\<cdot>ts) = delayFun\<cdot>(tsFilter M\<cdot>ts)"
oops

(*
definition tsZip_h :: "'a event stream \<rightarrow> 'b stream \<rightarrow> ('a \<times> 'b) event stream" where
"tsZip_h \<equiv> fix\<cdot>(\<Lambda> h s q. if s = \<epsilon> \<or> q = \<epsilon> then \<epsilon> 
                         else if shd s = \<surd> then \<up>\<surd> \<bullet> h\<cdot>(srt\<cdot>s)\<cdot>q
                         else \<up>(\<M> (\<M>\<inverse> (shd s), shd q)) \<bullet> h\<cdot>(srt\<cdot>s)\<cdot>(srt\<cdot>q))"

definition tsZip :: "'a tstream \<rightarrow> 'b stream \<rightarrow> ('a \<times> 'b) tstream" where
"tsZip \<equiv> \<Lambda> ts s. Abs_tstream (tsZip_h\<cdot>(Rep_tstream ts)\<cdot>s)"
*)

definition tsRemDups_h :: "'a option event \<Rightarrow> 'a option event stream \<rightarrow> 'a option event stream" where
"tsRemDups_h \<equiv> fix\<cdot>(\<Lambda> h. (\<lambda> q. (\<Lambda> s. if s = \<epsilon> then \<epsilon> 
                                     else if shd s = \<surd> then (\<up>\<surd> \<bullet> h q\<cdot>(srt\<cdot>s))
                                     else if shd s \<noteq> q then (\<up>(shd s) \<bullet> h (shd s)\<cdot>(srt\<cdot>s))
                                     else h q\<cdot>(srt\<cdot>s))))"

(* ToDo: New Version with fixrec *)
definition tsRemDups :: "'a tstream \<rightarrow> 'a tstream" where
"tsRemDups \<equiv> \<Lambda> ts. Abs_tstream (smap (\<lambda>x. case x of Msg (Some m) \<Rightarrow> (Msg m))\<cdot>(tsRemDups_h (\<M> None)\<cdot>(Rep_tstream (tsMap Some\<cdot>ts))))"

end  