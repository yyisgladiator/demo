theory induction_tstream
(* This theory enables the use of tStreams with fixrec. Especially pattern-matching with the first 
Element of the stream is supported. Hence it is possible to create seperate cases for "first Element is Tick"
and "first element is Message" *)
  
(* Created by Sebastian Stüber.
   sebastian.stueber@rwth-aachen.de *)
  
  
imports TStream "~~/src/HOL/HOLCF/Library/Option_Cpo"

begin

lemma tstickcount_adm [simp]: "adm (\<lambda>a. #\<surd> a \<le> #\<surd> f\<cdot>a)"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a tstream"
  assume a1: "chain Y"
  assume a2: "\<forall>i. #\<surd> Y i \<le> #\<surd> f\<cdot>(Y i)"
  obtain nn :: "(nat \<Rightarrow> 'a tstream) \<Rightarrow> nat \<Rightarrow> nat" where
      "\<forall>f. \<not> chain f \<or> finite_chain f \<or> (\<forall>n. Fin n \<le> #\<surd> f (nn f n))"
    by (meson exist_tslen)
  then have f3: "\<And>n. Fin n \<le> #\<surd> f\<cdot>(Y (nn Y n)) \<or> finite_chain Y"
    using a2 a1 trans_lnle by blast
  have "\<And>l c ca f n. (l::lnat) \<le> c\<cdot>(ca\<cdot>(Lub f::'a tstream)::'b tstream) \<or> \<not> l \<le> c\<cdot>(ca\<cdot>(f n)) \<or> \<not> chain f"
    by (meson is_ub_thelub lnle_def monofun_cfun_arg trans_lnle)
  then show "#\<surd> \<Squnion>n. Y n \<le> #\<surd> f\<cdot>(\<Squnion>n. Y n)"
    using f3 a2 a1 by (metis Suc_n_not_le_n l42 less2nat linorder_not_less lncases order_less_irrefl)
qed

lemma "t\<noteq>\<bottom>\<Longrightarrow>#\<surd> (tsMLscons\<cdot>t\<cdot>ts) = #\<surd>ts"
  apply(cases "ts=\<bottom>")
   apply simp
  oops
    
lemma assumes "\<And>ts. f\<cdot>(delayFun\<cdot>ts) = delayFun\<cdot>(f\<cdot>ts)"
  shows "#\<surd>ts \<le> #\<surd>(f\<cdot>ts)"
  apply (induction ts) 
apply simp_all
  apply (metis assms delayFun.rep_eq lnsuc_lnle_emb tstickcount_tscons)
  oops
    
    
    
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
    
fixrec tsRemDups:: "('a::countable) tstream \<rightarrow> 'a discr option \<rightarrow> 'a tstream" where
"tsRemDups\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts)\<cdot>option = delayFun\<cdot>(tsRemDups\<cdot>ts\<cdot>option)"  | (* Ignore ticks *)
"ts\<noteq>\<bottom> \<Longrightarrow> tsRemDups\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts)\<cdot>None = tsMLscons\<cdot>(up\<cdot>t)\<cdot>(tsRemDups\<cdot>ts\<cdot>(Some t))" | (* Handle first Message *)
"ts\<noteq>\<bottom> \<Longrightarrow> tsRemDups\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts)\<cdot>(Some a) = (if t=a then (tsRemDups\<cdot>ts\<cdot>(Some t)) else tsMLscons\<cdot>(up\<cdot>t)\<cdot>(tsRemDups\<cdot>ts\<cdot>(Some t)))"   (* Handle duplicate Message *)


(* Element ist gleich dem letzten Element \<Rightarrow> Löschen *)
lemma "ts\<noteq>\<bottom>\<Longrightarrow> tsRemDups\<cdot>(tsMLscons\<cdot>(up\<cdot>t)\<cdot>ts)\<cdot>(Some t) = tsRemDups\<cdot>ts\<cdot>(Some t)"
by(simp add: tsmlscons2tslscons)

  (* Anderes Element. Speichern und ausgeben *)
lemma "ts\<noteq>\<bottom>\<Longrightarrow> t\<noteq>a\<Longrightarrow>tsRemDups\<cdot>(tsMLscons\<cdot>(up\<cdot>t)\<cdot>ts)\<cdot>(Some  a) = tsMLscons\<cdot>(up\<cdot>t)\<cdot>(tsRemDups\<cdot>ts\<cdot>(Some t))"
by(simp add: tsmlscons2tslscons)
  
  
lift_definition tsExampIn :: "nat tstream" is "<[Msg 1, Msg 2, \<surd>, Msg 2, \<surd>]>"  
  by(simp add: ts_well_def)

lift_definition tsExampResult :: "nat tstream" is "<[Msg 1, Msg 2, \<surd>,  \<surd>]>"  
  by(simp add: ts_well_def)

lemma tsmsg_notwell2 [simp]: "\<not>ts_well (\<up>(Msg m))"
  apply(simp add: ts_well_def, auto)
  by (metis Inf'_neq_0 event.distinct(1) fold_inf inf_ub inject_lnsuc less_le lscons_conv sfoot1 sfoot_one slen_scons strict_slen sup'_def)
    
      
lemma tsmsg_notwell: "t\<noteq>updis \<surd> \<Longrightarrow> \<not>ts_well (t && \<bottom>)"
  apply(simp add: ts_well_def)
  sorry
    
  
lemma tslscons2ts: "ts_well (t&&ts) \<Longrightarrow> Abs_tstream (t&&ts) = tsLscons\<cdot>t\<cdot>(Abs_tstream ts)"
  apply(subst tslscons_insert, auto simp add: espf2tspf_def)
  apply (metis tsmsg_notwell lscons_well stream.con_rews(1) up_defined)
  apply (metis Rep_Abs stream.con_rews(2) stream.sel_rews(5) ts_well_drop1)
  by (metis Rep_tstream_strict induction_tstream.tsmsg_notwell stream.con_rews(1) ts_well_Rep)  

    thm delayfun_abststream
lemma tsdelay2ts: "ts_well ts \<Longrightarrow> Abs_tstream ((updis \<surd>)&&ts) = delayFun\<cdot>(Abs_tstream ts)"
  by (metis delayfun_abststream)

lemma tsmessage2ts: "ts_well ((updis (Msg m)) && ts) \<Longrightarrow> Abs_tstream ((updis (Msg m))&&ts) = tsMLscons\<cdot>(updis m)\<cdot>(Abs_tstream ts)"
  by(simp add: tsMLscons_def tslscons2ts)

lemma tsmessage2ts2: "ts_well (\<up>(Msg m) \<bullet>  ts) \<Longrightarrow> Abs_tstream (\<up>(Msg m) \<bullet>  ts) = tsMLscons\<cdot>(updis m)\<cdot>(Abs_tstream ts)"
  by (metis lscons_conv tsmessage2ts)
  

        thm lscons_conv
lemma "tsRemDups\<cdot>tsExampIn\<cdot>None = tsExampResult"
  apply(simp add: tsExampIn_def tsExampResult_def)
  apply(simp add: tsmessage2ts2 ts_well_def tsmlscons2tslscons)
  oops
    

    (* ToDo ... run the example on tsRemDups *)

    
    
lemma tslscons_discrtick [simp]: "(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>i) \<noteq>\<bottom>"
  apply(simp add: tslscons_insert)
  by (metis DiscrTick_def tslscons_insert tslscons_nbot2)
  

lemma [simp]: "ts\<noteq>\<bottom>\<Longrightarrow>match_tstream\<cdot>ts\<cdot>k = k\<cdot>(tsLshd\<cdot>ts)\<cdot>(tsRt\<cdot>ts)"
oops
lemma [simp]: "ts\<noteq>\<bottom> \<Longrightarrow> tsLshd\<cdot>ts\<noteq>\<bottom>" 
  oops
    
    
    
    (* sender playground *)
    
 (* first input "'a tstream":  input for the ABP sender from the user. *)
 (* second input: "bool tstream" acks from the receiver. *)
 (* third input: "bool discr" buffer for the next expected ack.*)

(* output: "('a \<times> bool) tstream" output to receiver *)
fixrec sender:: "'a tstream \<rightarrow> bool tstream \<rightarrow> bool discr \<rightarrow> ('a \<times> bool) tstream" where
  (* Bottom fälle *)
"sender\<cdot>\<bottom>\<cdot>acks\<cdot>bool = \<bottom>" |
"sender\<cdot>i\<cdot>\<bottom>\<cdot>bool = \<bottom>" |

  (* If an input is an Tick, return Tick *)
"sender\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>i)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>bool = delayFun\<cdot>(sender\<cdot>i\<cdot>acks\<cdot>bool)"   |

  (* i have an input and no Ack \<longrightarrow> send message*)
 "is\<noteq>\<bottom> \<Longrightarrow>sender\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>i))\<cdot>is)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>bool = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>i)\<cdot>(up\<cdot>bool))\<cdot>(sender\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>i))\<cdot>is)\<cdot>acks\<cdot>bool)"  |

 
 (* Some strange case... Not sure if we need this *)
 "acks\<noteq>\<bottom> \<Longrightarrow>sender\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>is)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>ack))\<cdot>acks)\<cdot>bool = sender\<cdot>is\<cdot>acks\<cdot>bool" | 

 (* We have a return value from the receiver! *)
"is\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom>\<Longrightarrow>sender\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>i))\<cdot>is)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>ack))\<cdot>acks)\<cdot>bool = 
  (if(ack = bool) (* correctly send the current input. Go to next input *)
  then sender\<cdot>is\<cdot>acks\<cdot>(Discr (\<not>(undiscr bool)))
    
    (* Wrong Ack. (Perhaps From the previous input. Resend current tupel*)
   else tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>i)\<cdot>(up\<cdot>bool))\<cdot>(sender\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>i))\<cdot>is)\<cdot>acks\<cdot>bool))"


(* Lemmate über Sender *)
(* Genommen aus BS01, Seite 103 *)

(*i = input 
  as = acks 
  ds = output *)


(* fds \<sqsubseteq> i, where fds = map((\<alpha>.ds, \<Pi>1) *)
(* only send input, and in the right order *)
lemma "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(sender\<cdot>i\<cdot>acks\<cdot>bool)\<cdot>None)) \<sqsubseteq> tsAbs\<cdot>i"
  oops

(* \<alpha>.fb = fb, where fb = map((\<alpha>.ds, \<Pi>2) *)
(* Sent different bit for different messanges *)    
lemma "tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(sender\<cdot>i\<cdot>acks\<cdot>bool)\<cdot>None))\<cdot>None = tsProjSnd\<cdot>(tsRemDups\<cdot>(sender\<cdot>i\<cdot>acks\<cdot>bool)\<cdot>None)"
  oops

    
(* 2 more are missing... *)
    
    
end  