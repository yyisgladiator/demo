theory induction_tstream
(* This theory enables the use of tStreams with fixrec. Especially pattern-matching with the first 
Element of the stream is supported. Hence it is possible to create seperate cases for "first Element is Tick"
and "first element is Message" *)
  
(* Created by Sebastian Stüber.
   sebastian.stueber@rwth-aachen.de *)
  
  
imports TStream "~~/src/HOL/HOLCF/Library/Option_Cpo"

begin

  
(* demo that the old fixrec is not working *)

  (* this function is removing all ticks *)
fixrec demo::"'a event stream \<rightarrow> 'a event stream" where
"t \<noteq> \<bottom> \<Longrightarrow> t=updis \<surd> \<Longrightarrow> demo\<cdot>(lscons\<cdot>t\<cdot>ts) = ts" |
(unchecked) "t \<noteq> \<bottom> \<Longrightarrow> t\<noteq>updis \<surd> \<Longrightarrow> demo\<cdot>(lscons\<cdot>t\<cdot>ts) = t&&ts"


lemma "t \<noteq> \<bottom> \<Longrightarrow> t\<noteq>updis \<surd> \<Longrightarrow> demo\<cdot>(lscons\<cdot>t\<cdot>ts) = t&&ts"
apply fixrec_simp
oops (* good luck proving this :/ *)
  
  
 
  (* Case Studies *)

fixrec teees:: "'a tstream \<rightarrow>'a tstream" where
"teees\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = tsInfTick" |  (* t is a 'event discr u', ts a tstream *)
"t\<noteq>DiscrTick \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow> teees\<cdot>(tsLscons\<cdot>(up\<cdot>t)\<cdot>ts) = ts"

lemma [simp]: "teees\<cdot>\<bottom> = \<bottom>"
  by(fixrec_simp)

    (* First Element is a Tick *)
lemma "teees\<cdot>(delayFun\<cdot>ts) = tsInfTick"
  by fixrec_simp
    
    (* First Element is not a Tick *)
lemma "t\<noteq>DiscrTick \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow> teees\<cdot>(tsLscons\<cdot>(up\<cdot>t)\<cdot>ts) = ts"
  by simp

lemma "teees\<cdot>\<bottom>= \<bottom>"
  by simp
    

 
    
    
(* removes first tick (if there is a first tick *)
fixrec tee :: "'a tstream \<rightarrow> 'a tstream" where
"tee\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = ts"  (* this pattern is only called if the input stream starts with a tick *)

fixrec tsAbsNew :: "'a tstream \<rightarrow> 'a stream" where
"tsAbsNew\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = tsAbsNew\<cdot>ts" |   (* ignore ticks *)  
"ts\<noteq>\<bottom> \<Longrightarrow> tsAbsNew\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) = up\<cdot>t && tsAbsNew\<cdot>ts"  (* prepend first message and go on *)  

lemma [simp]: "tsAbsNew\<cdot>\<bottom>=\<bottom>"
  by fixrec_simp

lemma [simp]: "tsAbsNew\<cdot>(delayFun\<cdot>ts) = tsAbsNew\<cdot>ts"
  by fixrec_simp

lemma [simp]: "tsAbs\<cdot>(delayFun\<cdot>ts) = tsAbs\<cdot>ts"
  by(simp add: delayFun_def)
    
lemma tsabs_new_msg [simp]: "xs\<noteq>\<bottom> \<Longrightarrow> tsAbsNew\<cdot>(tsMLscons\<cdot>(up\<cdot>x)\<cdot>xs) = up\<cdot>x && (tsAbsNew\<cdot>xs)"
  by fixrec_simp+

lemma tsmlscons2tslscons: "xs\<noteq>\<bottom> \<Longrightarrow> (tsMLscons\<cdot>(up\<cdot>x)\<cdot>xs) = tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>x))\<cdot>xs"
  by(simp add: tsMLscons_def)
    
lemma tsabs_tsmlscons: "xs\<noteq>\<bottom> \<Longrightarrow> tsAbs\<cdot>(tsMLscons\<cdot>(updis x)\<cdot>xs) = (updis x) && (tsAbs\<cdot>xs)"
  apply(subst tsmlscons2tslscons, simp)
  apply(subst tsabs_insert)
    apply(simp add: tslscons_lscons uMsg_def lscons_conv)
  by (simp add: tsabs_insert)

lemma "tsAbsNew\<cdot>ts= tsAbs\<cdot>ts"
  apply(induction)
     apply simp_all
  using updis_exists tsabs_tsmlscons by fastforce
    
    

    
    (* tsRemDups Prototyping *)
    
fixrec tsRemDups:: "'a tstream \<rightarrow> 'a discr option \<rightarrow> 'a tstream" where
"tsRemDups\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts)\<cdot>option = delayFun\<cdot>(tsRemDups\<cdot>ts\<cdot>option)"  | (* Ignore ticks *)
"ts\<noteq>\<bottom> \<Longrightarrow> tsRemDups\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts)\<cdot>None = tsMLscons\<cdot>(up\<cdot>t)\<cdot>(tsRemDups\<cdot>ts\<cdot>(Some t))" | (* Handle first Message *)
"ts\<noteq>\<bottom> \<Longrightarrow> tsRemDups\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts)\<cdot>(Some a) = (if t=a then (tsRemDups\<cdot>ts\<cdot>(Some t)) else tsMLscons\<cdot>(up\<cdot>t)\<cdot>(tsRemDups\<cdot>ts\<cdot>(Some t)))"   (* Handle duplicate Message *)


(* Element ist gleich dem letzten Element \<Rightarrow> Löschen *)
lemma "ts\<noteq>\<bottom>\<Longrightarrow> tsRemDups\<cdot>(tsMLscons\<cdot>(up\<cdot>t)\<cdot>ts)\<cdot>(Some t) = tsRemDups\<cdot>ts\<cdot>(Some t)"
by(simp add: tsmlscons2tslscons)

  (* Anderes Element. Speichern und ausgeben *)
lemma "ts\<noteq>\<bottom>\<Longrightarrow> t\<noteq>a\<Longrightarrow>tsRemDups\<cdot>(tsMLscons\<cdot>(up\<cdot>t)\<cdot>ts)\<cdot>(Some  a) = tsMLscons\<cdot>(up\<cdot>t)\<cdot>(tsRemDups\<cdot>ts\<cdot>(Some t))"
by(simp add: tsmlscons2tslscons)
  
  
lift_definition tsExamp :: "nat tstream" is "<[Msg 1, Msg 2, \<surd>, Msg 2, \<surd>]>"  
  by(simp add: ts_well_def)

    (* ToDo ... run the example on tsRemDups *)

    
    
lemma [simp]: "(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>i) \<noteq>\<bottom>"
  sorry

    
    (* sender playground *)
fixrec sender:: "'a tstream \<rightarrow> bool tstream \<rightarrow> tr \<rightarrow> ('a \<times> bool) tstream" where
"sender\<cdot>\<bottom>\<cdot>acks\<cdot>bool = \<bottom>" |
"sender\<cdot>i\<cdot>\<bottom>\<cdot>bool = \<bottom>" |
"acks\<noteq>\<bottom>\<Longrightarrow>sender\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>i)\<cdot>acks\<cdot>bool = sender\<cdot>i\<cdot>acks\<cdot>bool"  (* |*)
(* "i\<noteq>\<bottom> \<Longrightarrow> tsLshd\<cdot>i\<noteq>(up\<cdot>DicrTick) \<Longrightarrow>sender\<cdot>i\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>bool = sender\<cdot>i\<cdot>acks\<cdot>bool"  *)

    
end  