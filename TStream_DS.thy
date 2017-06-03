(*  Title:        TStream_DS.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Workspace for Development of Functions on Timed Streams
*)

theory TStream_DS
 
imports TStream

begin  

lemma tslscons2lscons: "ts\<noteq>\<bottom> \<Longrightarrow> tsLscons\<cdot>t\<cdot>ts = espf2tspf (lscons\<cdot>t) ts"
by (simp add: tslscons_insert)

lemma tsmlscons_abs: "ts\<noteq>\<bottom> \<Longrightarrow> Abs_tstream ((updis (Msg t)) && Rep_tstream ts) = tsMLscons\<cdot>(updis t)\<cdot>ts"
by (simp add: tsMLscons_def tslscons2lscons espf2tspf_def)

lemma tslscons_abs: "ts\<noteq>\<bottom> \<Longrightarrow> Abs_tstream (updis \<surd> && (Rep_tstream ts)) = tsLscons\<cdot>(updis \<surd>)\<cdot>ts"
by (simp add: tslscons_insert espf2tspf_def)

lemma tslscons_abs_bot: "ts=\<bottom> \<Longrightarrow> Abs_tstream (updis \<surd> && (Rep_tstream ts)) = tsLscons\<cdot>(updis \<surd>)\<cdot>\<bottom>"
by (simp add: tslscons_insert espf2tspf_def)

lemma delayfun_abs: "(Abs_tstream (\<up>\<surd>)\<bullet>ts) = delayFun\<cdot>ts"  
by (simp add: delayFun_def)

lemma delayfun_tslscons: "delayFun\<cdot>ts = tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts"
by (simp add: delayFun_def tslscons_insert tsconc_insert DiscrTick_def espf2tspf_def lscons_conv)


    
fixrec tsZip :: "'a tstream \<rightarrow> 'b stream \<rightarrow> ('a \<times> 'b) tstream" where
"tsZip\<cdot>ts\<cdot>\<bottom> = \<bottom>" |  
"x\<noteq>\<bottom> \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow>               
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts)\<cdot>(lscons\<cdot>x\<cdot>xs) = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>t)\<cdot>x)\<cdot>(tsZip\<cdot>ts\<cdot>xs)" | 
  (* zip if both first elements are defined *)
"xs\<noteq>\<bottom> \<Longrightarrow> 
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts)\<cdot>xs = delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs)"  
  (* ignore ticks *)

lemma tszip_strict [simp]: 
"tsZip\<cdot>\<bottom>\<cdot>\<epsilon> = \<bottom>"
"tsZip\<cdot>ts\<cdot>\<epsilon> = \<bottom>"
"tsZip\<cdot>\<bottom>\<cdot>s = \<bottom>"
by (fixrec_simp)+

lemma tszip_tslscons_fixrec: "x\<noteq>\<bottom> \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow>
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts)\<cdot>(lscons\<cdot>x\<cdot>xs)  = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>t)\<cdot>x)\<cdot>(tsZip\<cdot>ts\<cdot>xs)"
by (fixrec_simp)

lemma tszip_tslscons_tick_fixrec: "xs\<noteq>\<bottom> \<Longrightarrow> 
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts)\<cdot>xs = delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs)"
by (fixrec_simp)

lemma tszip_mlscons:
  "tsZip\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>ts)\<cdot>((updis x) && xs) = tsMLscons\<cdot>(updis (t,x))\<cdot>(tsZip\<cdot>ts\<cdot>xs)"
by (metis (no_types, lifting) tsmlscons_bot2 tsmlscons_lscons tszip_tslscons_fixrec tszip_strict(3)
    up_defined upapply2_rep_eq)

lemma tszip_delayfun: "xs\<noteq>\<epsilon> \<Longrightarrow> tsZip\<cdot>(delayFun\<cdot>ts)\<cdot>xs = delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs)"
by (simp add: delayfun_tslscons)



lemma h1:
  "Abs_tstream (<[Msg 1, \<surd>, Msg 2, \<surd>]>) =
    tsMLscons\<cdot>(updis 1)\<cdot>(tsLscons\<cdot>(updis \<surd>)\<cdot>(tsMLscons\<cdot>(updis 2)\<cdot>(tsLscons\<cdot>(updis \<surd>)\<cdot>\<bottom>)))"
by (smt Rep_Abs Rep_tstream_strict list2s_0 list2s_Suc sup'_def tick_msg tslscons_abs_bot
    tslscons_lscons tslscons_nbot2 tsmlscons_abs tsmlscons_rep)

lemma h2: "<[True, False]> = (updis True && updis False && \<epsilon>)"
by (metis list2s_0 list2s_Suc)

lemma h3: "updis \<surd> = up\<cdot>DiscrTick"
by (simp add: DiscrTick_def)

(* Das sollte nicht passieren! *)
lemma 
  "tsZip\<cdot>(Abs_tstream (<[Msg 1, \<surd>, Msg 2, \<surd>]>))\<cdot>(<[True, False]>) = Abs_tstream (<[Msg (1, True), \<surd>]>)"
apply (simp only: h1 h2 h3)
apply (simp add: tszip_mlscons)
by (metis (no_types, hide_lams) Rep_Abs Rep_tstream_strict delayfun_nbot delayfun_tslscons h3
    lscons_conv sup'_def tick_msg tslscons_abs_bot tsmlscons_abs)

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