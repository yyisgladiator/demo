(*  Title:        TStream_DS.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Workspace for Development of Functions on Timed Streams
*)

theory TStream_DS
 
imports TStream

begin  
    
fixrec tsZip :: "'a tstream \<rightarrow> 'b stream \<rightarrow> ('a \<times> 'b) tstream" where
"tsZip\<cdot>ts\<cdot>\<bottom> = \<bottom>" |  
"x\<noteq>\<bottom> \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow>               
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts)\<cdot>(lscons\<cdot>x\<cdot>xs) = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>t)\<cdot>x)\<cdot>(tsZip\<cdot>ts\<cdot>xs)" | 
  (* zip if both first elements are defined *)
"xs\<noteq>\<bottom> \<Longrightarrow> 
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts)\<cdot>xs = delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs)"  
  (* ignore ticks *)

lemma tszip_strict[simp]: 
"tsZip\<cdot>\<bottom>\<cdot>\<epsilon> = \<bottom>"
"tsZip\<cdot>ts\<cdot>\<epsilon> = \<bottom>"
"tsZip\<cdot>\<bottom>\<cdot>s = \<bottom>"
by (fixrec_simp)+

lemma tszip_scons_fixrec: "x\<noteq>\<bottom> \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow>
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts)\<cdot>(lscons\<cdot>x\<cdot>xs)  = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>t)\<cdot>x)\<cdot>(tsZip\<cdot>ts\<cdot>xs)"
by (fixrec_simp)

lemma tszip_scons_tick_fixrec: "xs\<noteq>\<bottom> \<Longrightarrow> 
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts)\<cdot>xs = delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs)"
by (fixrec_simp)

lemma delayfun_simp: "(Abs_tstream (\<up>\<surd>)\<bullet>ts) = delayFun\<cdot>ts"  
by (simp add: delayFun_def)

lemma delayfun_lscons: "delayFun\<cdot>ts = tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts"
by (simp add: delayFun_def tslscons_insert tsconc_insert DiscrTick_def espf2tspf_def lscons_conv)

lemma tszip_scons_tick: "xs\<noteq>\<epsilon> \<Longrightarrow> tsZip\<cdot>(Abs_tstream (\<up>\<surd>)\<bullet>ts)\<cdot>xs = Abs_tstream(\<up>\<surd>) \<bullet> tsZip\<cdot>ts\<cdot>xs"
apply (simp add: delayfun_simp)
apply (subst delayfun_lscons)
by (fixrec_simp)

lemma tick_eq_discrtick: "updis \<surd> = up\<cdot>DiscrTick"
by (simp add: DiscrTick_def)

lemma tslscons_lscons: "ts\<noteq>\<bottom> \<Longrightarrow> tsLscons\<cdot>t\<cdot>ts = espf2tspf (lscons\<cdot>t) ts"
by (simp add: tslscons_insert)

(* Was ist x?
lemma msgscons_lscons: "Abs_tstream (\<up>t\<bullet>ts) = tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>x))\<cdot>(Abs_tstream ts)"
oops

lemma "updis (Msg x) = up\<cdot>(uMsg\<cdot>t)"
oops
*)

lemma tszip_scons: 
  "tsZip\<cdot>(tsLscons\<cdot>(updis t)\<cdot>ts)\<cdot>((updis x) && xs) = tsMLscons\<cdot>(updis ((inversMsg t),x))\<cdot>(tsZip\<cdot>ts\<cdot>xs)"
oops

lemma tszip_scons2: 
  "tsZip\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>ts)\<cdot>((updis x) && xs) = tsMLscons\<cdot>(updis ((t,x)))\<cdot>(tsZip\<cdot>ts\<cdot>xs)"
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