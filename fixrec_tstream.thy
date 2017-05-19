theory fixrec_tstream
(* This theory enables the use of tStreams with fixrec. Especially pattern-matching with the first 
Element of the stream is supported. Hence it is possible to create seperate cases for "first Element is Tick"
and "first element is Message" *)
  
(* Created by Sebastian Stüber.
   sebastian.stueber@rwth-aachen.de *)
  
  
imports TStream

begin

  


(* demo that the old fixrec is not working *)
  
  (* this function is removing all ticks *)
fixrec demo::"'a event stream \<rightarrow> 'a event stream" where
"t \<noteq> \<bottom> \<Longrightarrow> t=updis \<surd> \<Longrightarrow> demo\<cdot>(lscons\<cdot>t\<cdot>ts) = ts" |
(unchecked) "t \<noteq> \<bottom> \<Longrightarrow> t\<noteq>updis \<surd> \<Longrightarrow> demo\<cdot>(lscons\<cdot>t\<cdot>ts) = t&&ts"


lemma "t \<noteq> \<bottom> \<Longrightarrow> t\<noteq>updis \<surd> \<Longrightarrow> demo\<cdot>(lscons\<cdot>t\<cdot>ts) = t&&ts"
apply fixrec_simp
oops (* good luck proving this :/ *)
  
(***************************************************)      
  section \<open>Using tstream with fixrec\<close>
(***************************************************)        

(* source: https://www.pdx.edu/computer-science/sites/www.pdx.edu.computer-science/files/Huffman.pdf *)
 
    
    
    
    
    
  subsection \<open>Necessary definitions\<close>
    
    
  definition upApply :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a discr u \<rightarrow> 'b discr u" where
"upApply f \<equiv> \<Lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))"

(* ToDo. Definition & show cnot *)
definition upApply2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a discr\<^sub>\<bottom> \<rightarrow> 'b discr\<^sub>\<bottom> \<rightarrow> 'c discr\<^sub>\<bottom>" where 
"upApply2 f \<equiv> \<bottom> " (* Is it possible to define upApply2 using upApply ? ? *)


lemma upApply_mono[simp]:"monofun (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b))))"
  apply(rule monofunI)
  apply auto[1]
  by (metis (full_types, hide_lams) discrete_cpo upE up_below)

lemma upApply_lub: assumes "chain Y"
  shows "((\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))) (\<Squnion>i. Y i))
=(\<Squnion>i. (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))) (Y i))"
apply(rule finite_chain_lub)
apply (simp_all add: assms chfin2finch)
done
 
lemma upApply_cont[simp]:"cont (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b))))"
using chfindom_monofun2cont upApply_mono by blast

lemma upApply_rep_eq [simp]: "upApply f\<cdot>(updis a) = updis (f a)"
by(simp add: upApply_def)


  
  
(* get First Element of tStream *)
thm lshd_def  (* similar to lshd *)  
lift_definition tsLshd :: "'a tstream \<rightarrow> 'a event discr u" is
"\<lambda> ts.  lshd\<cdot>(Rep_tstream ts)"
by (simp add: cfun_def)


(* get rest of tStream *)
thm srt_def   (* similar to srt *)
lift_definition tsRt :: "'a tstream \<rightarrow> 'a tstream" is
"\<lambda>ts. espf2tspf srt ts"
by(simp add: espf2tspf_def cfun_def)

  
(* create new tStream by appending a new first Element *)
  (* sadly the function must be ts_well... 
  .. hence for the input (updis Msg m) and the empty stream a special case must be made *)
thm lscons_def (* similar to lscons *)
definition tsLscons :: "'a event discr u \<rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsLscons \<equiv> \<Lambda> t ts. if (ts=\<bottom>) then (Abs_tstream (\<up>\<surd>)) else espf2tspf (lscons\<cdot>t) ts"

lemma lsconc_well [simp]: assumes "ts_well ts" and "ts\<noteq>\<bottom>"
  shows "ts_well (t&&ts)"
apply(auto simp add: ts_well_def)
  apply (metis Rep_Abs assms(1) sConc_Rep_fin_fin stream.con_rews(2) stream.sel_rews(5) surj_scons)
  by (metis Rep_Abs Rep_tstream_bottom_iff assms(1) assms(2) sConc_fin_well stream.con_rews(2) stream.sel_rews(5) surj_scons ts_well_def)    

    
lemma "ts_well (\<up>\<surd>)"
  by simp

lemma lsconc_tick_well[simp]: "ts_well ts \<Longrightarrow> ts_well (updis \<surd> && ts)"
  by (metis lsconc_well sup'_def tick_msg)
    
lemma tslscons_mono: "monofun (\<lambda>ts. if (ts=\<bottom> \<and>t=updis \<surd>) then (Abs_tstream (\<up>\<surd>)) else if ts=\<bottom> then \<bottom> else espf2tspf (lscons\<cdot>t) ts)"    
  apply(rule monofunI)
    apply (auto simp add: espf2tspf_def)
  apply (metis (mono_tags) Abs_tstream_inverse Rep_tstream below_tstream_def lsconc_tick_well lscons_conv mem_Collect_eq minimal monofun_cfun_arg sconc_snd_empty tick_msg)
  by (metis (no_types, lifting) Abs_tstream_inverse Rep_tstream Rep_tstream_bottom_iff below_tstream_def lsconc_well mem_Collect_eq monofun_cfun_arg)

lemma "monofun (\<lambda> ts. (if ts = \<bottom> then Abs_tstream (\<up>\<surd>) else espf2tspf (lscons\<cdot>t) ts))"
  apply(rule monofunI)
  apply auto
  oops
    
        (* ToDo; important! *)
(* An tslscons definition anpassen :D *)
lemma tslscons_cont [simp]: "cont (\<lambda>ts. if (ts=\<bottom> \<and>t=updis \<surd>) then (Abs_tstream (\<up>\<surd>)) else if ts=\<bottom> then \<bottom> else espf2tspf (lscons\<cdot>t) ts)"    (is "cont ?f")
  sorry

    
(* Das darf man gerne schöner nennen *)
definition tsMLscons :: "'a discr u \<rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsMLscons \<equiv> \<Lambda> t ts. tsLscons\<cdot>(upApply Msg\<cdot>t)\<cdot>ts"

(* remove the Msg layer. Return bottom on ticks *)
definition unpackMsg::"'a event discr u \<rightarrow> 'a discr u" where
  "unpackMsg = upApply (\<lambda>x. case x of Msg m \<Rightarrow> m )"
  
  
  
  
    subsection \<open>Match definitions\<close>
  (* used with fixrec, see link above *)    
  
definition
  match_tstream :: "'a tstream \<rightarrow> ('a event discr u \<rightarrow> 'a tstream \<rightarrow> ('b ::cpo) match) \<rightarrow> 'b match" where
  "match_tstream = (\<Lambda> xs k.  strictify\<cdot>(\<Lambda> xs. k\<cdot>(tsLshd\<cdot>xs)\<cdot>(tsRt\<cdot>xs))\<cdot>xs)" (*testing a different definition *)
  (* if(xs=\<bottom>) then Fixrec.fail else k\<cdot>(tsLshd\<cdot>xs)\<cdot>(tsRt\<cdot>xs)) " *)

  (* match if first element is tick *)
definition match_delayfun:: "'a tstream \<rightarrow> ('a tstream \<rightarrow> ('b ::cpo) match) \<rightarrow> 'b match" where
 "match_delayfun = (\<Lambda> ts k . if (tsLshd\<cdot>ts\<noteq>updis \<surd>) then Fixrec.fail else match_tstream\<cdot>ts\<cdot>(\<Lambda> a . k))" 
  
 (* match if first element is message *) 
definition match_message:: "'a tstream \<rightarrow> ('a discr u \<rightarrow> 'a tstream \<rightarrow> ('b ::cpo) match) \<rightarrow> 'b match" where
 "match_message = (\<Lambda> ts k . if (tsLshd\<cdot>ts=updis \<surd>) then Fixrec.fail else match_tstream\<cdot>ts\<cdot>(\<Lambda> a xs . k\<cdot>(unpackMsg\<cdot>a)\<cdot>xs))" 
   
 
 
 
     subsection \<open>Lemmata for match definitions\<close>

  (* ToDo: cont-stuff for die match-sachen *)
lemma match_tstream_cont [simp]:  "monofun (\<lambda> xs . if(xs=\<bottom>) then Fixrec.fail else k\<cdot>(tsLshd\<cdot>xs)\<cdot>(tsRt\<cdot>xs))"
  apply(rule monofunI)
    apply auto
oops  

  (* maybe an extra condition is required... t\<noteq>\<bottom> and/or ts\<noteq>\<bottom> e.g. *)
lemma match_tstream_simps [simp]:
  "match_tstream\<cdot>\<bottom>\<cdot>k = \<bottom>"
  "ts\<noteq>\<bottom> \<Longrightarrow> match_tstream\<cdot>(tsLscons\<cdot>t\<cdot>ts)\<cdot>k = k\<cdot>t\<cdot>ts" 
  apply (simp_all add: match_tstream_def)
  sorry
(* unfolding match_tstream_def apply simp_all *)

lemma match_delayfun_simps [simp]:
  "match_delayfun\<cdot>\<bottom>\<cdot>k = Fixrec.fail"
  "match_delayfun\<cdot>(tsLscons\<cdot>(updis (Msg m))\<cdot>ts)\<cdot>k = Fixrec.fail"
  "match_delayfun\<cdot>(tsLscons\<cdot>(updis \<surd>)\<cdot>ts)\<cdot>k = k\<cdot>ts" 
  "tsLshd\<cdot>ts = updis \<surd> \<Longrightarrow> match_delayfun\<cdot>ts\<cdot>k = k\<cdot>ts"
  "tsLshd\<cdot>ts = updis (Msg m) \<Longrightarrow> match_delayfun\<cdot>ts\<cdot>k = Fixrec.fail" 
  "match_delayfun\<cdot>(tsMLscons\<cdot>t\<cdot>ts)\<cdot>k = Fixrec.fail"
  "match_delayfun\<cdot>(delayFun\<cdot>ts)\<cdot>k = k\<cdot>ts" (* important *)
  sorry
    
lemma match_message_simps [simp]:
  "match_message\<cdot>\<bottom>\<cdot>k = Fixrec.fail"
  "match_message\<cdot>(tsMLscons\<cdot>t\<cdot>ts)\<cdot>k = k\<cdot>t\<cdot>ts"
  "match_message\<cdot>(delayFun\<cdot>ts)\<cdot>k = Fixrec.fail"
  sorry
    
setup \<open>
  Fixrec.add_matchers
    [ (@{const_name tsLscons}, @{const_name match_tstream}) , 
      (@{const_name delayFun}, @{const_name match_delayfun}),
      (@{const_name tsMLscons}, @{const_name match_message})
    ]
\<close>

  
  
  
  (* Case Studies *)

  

fixrec teees:: "'a tstream \<rightarrow>'a tstream" where
"teees\<cdot>(tsLscons\<cdot>t\<cdot>ts) = ts"  (* t is a 'event discr u', ts a tstream *)

(* removes first tick (if there is a first tick *)
fixrec tee :: "'a tstream \<rightarrow> 'a tstream" where
"tee\<cdot>(delayFun\<cdot>ts) = ts"  (* this pattern is only called if the input stream starts with a tick *)

fixrec tsAbsNew :: "'a tstream \<rightarrow> 'a stream" where
"tsAbsNew\<cdot>(tsMLscons\<cdot>t\<cdot>ts) = t && tsAbsNew\<cdot>ts" | (* prepend first message and go on *)  
"tsAbsNew\<cdot>(delayFun\<cdot>ts) = tsAbsNew\<cdot>ts"   (* ignore ticks *)  



    
fixrec tsZipNew:: "'a stream \<rightarrow> 'b tstream \<rightarrow> ('a\<times>'b) tstream" where
"x\<noteq>\<bottom> \<Longrightarrow> tsZipNew\<cdot>(lscons\<cdot>x\<cdot>xs)\<cdot>(tsMLscons\<cdot>t\<cdot>ts) = (tsMLscons\<cdot>(upApply2 Pair\<cdot>x\<cdot>t)\<cdot>(tsZipNew\<cdot>xs\<cdot>ts))"  | (* zip if both first elements are defined *)
"x\<noteq>\<bottom> \<Longrightarrow> tsZipNew\<cdot>(lscons\<cdot>x\<cdot>xs)\<cdot>(delayFun\<cdot>ts) = delayFun\<cdot>(tsZipNew\<cdot>xs\<cdot>ts)"  (* ignore ticks *)
(* No other cases required, stuff that does not match will go to bottom *)

  




(* Gimmick *)
thm match_Pair_def
thm  match_up_def
definition match_ibottom :: "('a::cpo) u \<rightarrow> ('c ::cpo) match \<rightarrow> 'c match" where
  "match_ibottom = (\<Lambda> x k. case x of Ibottom \<Rightarrow> k | _ \<Rightarrow> Fixrec.fail)"

setup \<open>
  Fixrec.add_matchers
    [ (@{const_name Ibottom}, @{const_name match_ibottom})]\<close>
  
lemma match_ibottom_simps [simp]:
(*   "match_ibottom\<cdot>\<bottom>\<cdot>k = Fixrec.fail" *)
  "match_ibottom\<cdot>(up\<cdot>a)\<cdot>k = Fixrec.fail"
  "match_ibottom\<cdot>Ibottom\<cdot>k = k"
  sorry
  
fixrec tsRemDupsNew :: "'a discr u \<rightarrow> 'a tstream \<rightarrow> 'a tstream" where
(* No element found yet: *)
"tsRemDupsNew\<cdot>Ibottom\<cdot>(tsMLscons\<cdot>t\<cdot>ts) = tsMLscons\<cdot>t\<cdot>(tsRemDupsNew\<cdot>t\<cdot>ts)" |     (* Element found, prepend it and save it *)
"tsRemDupsNew\<cdot>Ibottom\<cdot>(delayFun\<cdot>ts) = delayFun\<cdot>(tsRemDupsNew\<cdot>Ibottom\<cdot>ts)"  |   (* Ignore Ticks *)
"tsRemDupsNew\<cdot>(up\<cdot>a)\<cdot>(delayFun\<cdot>ts) = delayFun\<cdot>(tsRemDupsNew\<cdot>(up\<cdot>a)\<cdot>ts)"  |      (* Ignore Ticks *)
"tsRemDupsNew\<cdot>(up\<cdot>a)\<cdot>(tsMLscons\<cdot>t\<cdot>ts) = \<bottom>" (* ToDo *)                         (* remove duplicate or save new element *)
  
  
  
end  