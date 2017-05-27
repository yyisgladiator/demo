(*  Title:        TStream_DS.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Workspace for Development of Functions on Timed Streams
*)

theory TStream_DS
 
imports fixrec_tstream

begin  

definition upApply :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a discr u \<rightarrow> 'b discr u" where
"upApply f \<equiv> \<Lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))"

lemma upApply_mono [simp]: "monofun (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b))))"
apply (rule monofunI, auto)
by (metis (full_types, hide_lams) discrete_cpo upE up_below)

lemma upApply_cont [simp]: "cont (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b))))"
using chfindom_monofun2cont upApply_mono by blast

lemma upApply_rep_eq [simp]: "upApply f\<cdot>(updis a) = updis (f a)"
by (simp add: upApply_def)

(* ToDo. Definition & show cont *)
definition upApply2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a discr\<^sub>\<bottom> \<rightarrow> 'b discr\<^sub>\<bottom> \<rightarrow> 'c discr\<^sub>\<bottom>" where 
"upApply2 f \<equiv> \<Lambda> a b. (if a=\<bottom>\<or>b=\<bottom> then \<bottom> else updis (f (THE x. a = updis x) (THE x. b = updis x)))"
 (* Is it possible to define upApply2 using upApply? *)
(* ToDo: mono&cont *)


   (* only the general idea *)
fixrec tsZip:: "'a tstream \<rightarrow> 'b stream \<rightarrow> ('a \<times> 'b) tstream" where
"tsZip\<cdot>ts\<cdot>\<bottom> = \<bottom>" |
"x\<noteq>\<bottom> \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow>
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts)\<cdot>(lscons\<cdot>x\<cdot>xs)  = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>t)\<cdot>x)\<cdot>(tsZip\<cdot>ts\<cdot>xs)" | 
  (* zip if both first elements are defined *)
"x\<noteq>\<bottom> \<Longrightarrow> 
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts)\<cdot>(lscons\<cdot>x\<cdot>xs) = delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs)"  
  (* ignore ticks *)
(* No other cases required, stuff that does not match will go to bottom *)

lemma tszip_strict[simp]: 
"tsZip\<cdot>\<bottom>\<cdot>\<epsilon> = \<bottom>"
"tsZip\<cdot>ts\<cdot>\<epsilon> = \<bottom>"
"tsZip\<cdot>\<bottom>\<cdot>s = \<bottom>"
by (fixrec_simp)+

lemma tszip_scons_fixrec: "x\<noteq>\<bottom> \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow>
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts)\<cdot>(lscons\<cdot>x\<cdot>xs)  = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>t)\<cdot>x)\<cdot>(tsZip\<cdot>ts\<cdot>xs)"
by (fixrec_simp)

lemma tszip_scons_tick_fixrec: "x\<noteq>\<bottom> \<Longrightarrow> 
  tsZip\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts)\<cdot>(lscons\<cdot>x\<cdot>xs) = delayFun\<cdot>(tsZip\<cdot>ts\<cdot>xs)"
by (fixrec_simp)
    
lemma tszip_scons_tick: "xs\<noteq>\<epsilon> \<Longrightarrow> tsZip\<cdot>(Abs_tstream (\<up>\<surd>)\<bullet>ts)\<cdot>xs = Abs_tstream(\<up>\<surd>) \<bullet> tsZip\<cdot>ts\<cdot>xs"
oops

lemma tszip_scons: "t\<noteq>\<surd> \<Longrightarrow> ts_well (\<up>(\<M> (\<M>\<inverse> t,x)) \<bullet> Rep_tstream (tsZip\<cdot>ts\<cdot>xs)) 
  \<Longrightarrow> tsZip\<cdot>(Abs_tstream (\<up>t)\<bullet>ts)\<cdot>(\<up>x\<bullet>xs) = Abs_tstream(\<up>(\<M> (\<M>\<inverse> t,x)) \<bullet> Rep_tstream (tsZip\<cdot>ts\<cdot>xs))"
oops


(* Wenn das 1. Element ein tick ist, dann bilde auf tick ab (und wende funktion auf rest an). Ansonsten wende funktion an *)
  (* Vermutlich muss man das strictify-en, damit es cont ist *)
definition ticktify  :: "('a event stream \<rightarrow> 'b event stream) \<rightarrow> 'a event stream \<rightarrow> 'b event stream" where
"ticktify \<equiv> \<Lambda> f ts. if(lshd\<cdot>ts = updis \<surd>) then updis \<surd> && f\<cdot>(srt\<cdot>ts) else f\<cdot>ts"

lemma h2: "cont (\<lambda>ts. if lshd\<cdot>ts = updis \<surd> then updis \<surd> && f\<cdot>(srt\<cdot>ts) else f\<cdot>ts)"
sorry

lemma h1: "cont (\<lambda>f. \<Lambda> ts. if lshd\<cdot>ts = updis \<surd> then updis \<surd> && f\<cdot>(srt\<cdot>ts) else f\<cdot>ts)"
sorry

lemma "ticktify\<cdot>f\<cdot>s = (if(lshd\<cdot>ts = updis \<surd>) then updis \<surd> && f\<cdot>(srt\<cdot>ts) else f\<cdot>ts)"
sorry

end  