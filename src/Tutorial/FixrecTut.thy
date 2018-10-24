section {* Tutorial for Fixrec-Proofs *} 

  
  (* The name "Fixrec.thy" seems to be reserved or something... *)
theory FixrecTut

(* Official tutorial: https://isabelle.in.tum.de/library/HOL/HOLCF-Tutorial/document.pdf  
  and look at the second import! *)
imports "../TStream" "~~/src/HOL/HOLCF/Tutorial/Fixrec_ex"
begin

  (* Allways nice to know what the default_sort is *)
default_sort countable

  
subsection {* Streams / lNat*}
  
fixrec sSuc :: "nat stream \<rightarrow> nat stream" where
"sSuc\<cdot>\<bottom>=\<bottom>" |
"x\<noteq>\<bottom> \<Longrightarrow> sSuc\<cdot>(x&&xs) = (upApply Suc\<cdot>x)&&(sSuc\<cdot>xs)"


  (* missing cases are implicitly created *)
fixrec myTake :: "lnat \<rightarrow> 'a stream \<rightarrow> 'a stream" where
"x\<noteq>\<bottom> \<Longrightarrow> myTake\<cdot>(lnsuc\<cdot>ln)\<cdot>(x&&xs) = x && myTake\<cdot>ln\<cdot>xs"

lemma "myTake\<cdot>\<bottom>\<cdot>xs = \<bottom>"
by(fixrec_simp)
  
lemma "myTake\<cdot>ln\<cdot>\<bottom> = \<bottom>"
  apply(fixrec_simp)
  oops
    
lemma "myTake\<cdot>ln\<cdot>\<bottom> = \<bottom>"
  apply(fixrec_simp)
  apply(cases ln)
  by auto

  
(* It is recommended to explicitly add all cases... *)
fixrec myTake2 :: "lnat \<rightarrow> 'a stream \<rightarrow> 'a stream" where
"myTake2\<cdot>\<bottom>\<cdot>xs = \<bottom>" |  
"myTake2\<cdot>ln\<cdot>\<bottom> = \<bottom>" |
"x\<noteq>\<bottom> \<Longrightarrow> myTake2\<cdot>(lnsuc\<cdot>ln)\<cdot>(x&&xs) = x && myTake\<cdot>ln\<cdot>xs"  
  (* x\<noteq>\<bottom> is required! Otherwise (x&&xs) could be bot *)
  
lemma "myTake2\<cdot>\<bottom>\<cdot>xs = \<bottom>"
  and "myTake2\<cdot>ln\<cdot>\<bottom> = \<bottom>"
  by(fixrec_simp)+
    
    
    
    
    
(* all cases must be mutually exclusive! *)
fixrec fix1 :: "lnat \<rightarrow>  'a stream" where
"fix1\<cdot>(lnsuc\<cdot>ln) = \<bottom>" |
"fix1\<cdot>ln = \<bottom>"  
  

  (* this function is removing all ticks ... And not working *)
fixrec demo::"'a event stream \<rightarrow> 'a event stream" where
"t \<noteq> \<bottom> \<Longrightarrow> t=updis \<surd> \<Longrightarrow> demo\<cdot>(lscons\<cdot>t\<cdot>ts) = ts" |
(unchecked) "t \<noteq> \<bottom> \<Longrightarrow> t\<noteq>updis \<surd> \<Longrightarrow> demo\<cdot>(lscons\<cdot>t\<cdot>ts) = t&&ts"  (* NEVER use unchecked *)
(* We need to use it, because fixrec does not know, that the cases are not overlapping *)

lemma "t \<noteq> \<bottom> \<Longrightarrow> t\<noteq>updis \<surd> \<Longrightarrow> demo\<cdot>(lscons\<cdot>t\<cdot>ts) = t&&ts"
  apply fixrec_simp
oops (* good luck proving this :/ *)


  
  

section \<open>TStream\<close>
  
  (* The definitions, otherwise this would not work *)
thm match_tstream_def
thm match_tick_def
thm match_umsg_def
  
  (* And the simplifiers that fixrec is using *)
thm match_tstream_simps
thm match_tick_simps
thm match_umsg_simps
   

  
 
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



(* New abbreviations for fixrec - use *)

(* Wenn wir das haben... brauchen wir überhaupt noch delayfun? *)
abbreviation delay_abbr :: "'a tstream \<Rightarrow>  'a tstream" ("fixDelay")
where "fixDelay ts \<equiv> (tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts)"

abbreviation tsmlscons_abbr :: "'a discr \<Rightarrow> 'a tstream \<Rightarrow>  'a tstream" ("_ fix&&\<surd> _ ")
where "t fix&&\<surd> ts \<equiv> (tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts)"


fixrec tsAbsNew :: "'a tstream \<rightarrow> 'a stream" where
"tsAbsNew\<cdot>(fixDelay ts) = tsAbsNew\<cdot>ts" |   (* ignore ticks *)  
"ts\<noteq>\<bottom> \<Longrightarrow> tsAbsNew\<cdot>(t fix&&\<surd> ts) = up\<cdot>t && tsAbsNew\<cdot>ts"  (* prepend first message and go on *)  



lemma [simp]: "tsAbsNew\<cdot>\<bottom>=\<bottom>"
  by fixrec_simp

lemma [simp]: "tsAbsNew\<cdot>(delayFun\<cdot>ts) = tsAbsNew\<cdot>ts"
  by fixrec_simp
  
lemma tsabs_new_msg [simp]: "xs\<noteq>\<bottom> \<Longrightarrow> tsAbsNew\<cdot>(tsMLscons\<cdot>(up\<cdot>x)\<cdot>xs) = up\<cdot>x && (tsAbsNew\<cdot>xs)"
  by fixrec_simp


end  