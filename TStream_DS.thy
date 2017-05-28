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

lemma delayfun_lscons: "delayFun\<cdot>ts= tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts"
by (simp add: delayFun_def tslscons_insert tsconc_insert DiscrTick_def espf2tspf_def lscons_conv)  
    
lemma tszip_scons_tick: "xs\<noteq>\<epsilon> \<Longrightarrow> tsZip\<cdot>(Abs_tstream (\<up>\<surd>)\<bullet>ts)\<cdot>xs = Abs_tstream(\<up>\<surd>) \<bullet> tsZip\<cdot>ts\<cdot>xs"
apply (simp add: delayfun_simp)
apply (subst delayfun_lscons)
by (fixrec_simp)

(*
lemma tszip_scons: 
  "t\<noteq>\<surd> \<Longrightarrow> tsZip\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>ts)\<cdot>(updis x && xs) = tsMLscons\<cdot>(updis (\<M>\<inverse> t,x))\<cdot>(tsZip\<cdot>ts\<cdot>xs)"
oops
*)

end  