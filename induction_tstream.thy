theory induction_tstream
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

  
lemma tsabs_SORRY: "xs\<noteq>\<bottom> \<Longrightarrow> tsAbs\<cdot>(tsMLscons\<cdot>(up\<cdot>x)\<cdot>xs) = up\<cdot>x && (tsAbs\<cdot>xs)"
  apply(subst tsabs_insert)
  oops    

    
    
    


    
(* Define a "induction" lemma for tStreams *)

lemma stream_fin_induct: "P \<bottom> \<Longrightarrow> (\<And>x xs. x\<noteq>\<bottom>\<Longrightarrow>P xs \<Longrightarrow> P (x&&xs)) \<Longrightarrow> #xs<\<infinity>\<Longrightarrow>P xs"
  by (metis finind infI lnless_def sconc_fst_empty sconc_scons' sup'_def up_defined)

  (* by (metis finind lnless_def ninf2Fin sconc_fst_empty sconc_scons' sup'_def)*)
  
lemma stream_infs: "(\<And>s. #s<\<infinity> \<Longrightarrow> P s) \<Longrightarrow> adm P \<Longrightarrow> P s"
  by (metis inf_less_eq leI notinfI3 slen_stake_fst_inf stream.take_induct)

lemma tstream_infs: "(\<And>s. #\<surd>s<\<infinity> \<Longrightarrow> P s) \<Longrightarrow> adm P \<Longrightarrow> P s"
  by (metis (no_types, lifting) adm_def finite_chain_def inf_less_eq leI ts_infinite_fin tstake_chain tstake_inf_lub tstake_infinite_chain)
        
lemma tstream_adm_fin: "adm P \<Longrightarrow> (\<forall>ts. #\<surd>ts<\<infinity> \<longrightarrow> P ts) \<Longrightarrow>  adm (\<lambda>a. ts_well a \<longrightarrow> P (Abs_tstream a))"    
  apply(rule admI)
    apply auto
  by (metis (no_types, lifting) adm_def finite_chain_def inf_less_eq leI ts_infinite_fin tstake_chain tstake_inf_lub tstake_infinite_chain)  

lemma tsmsg_notwell: "\<not>ts_well((updis (Msg m)) && \<bottom>)"
  apply(simp add: ts_well_def)
  by (metis Inf'_neq_0 event.distinct(1) fold_inf lnat.sel_rews(2) lscons_conv sfilterl4 sfoot1 sfoot_one slen_scons strict_slen sup'_def)

lemma tstream_fin_induct_h:
  assumes 
        "P \<bottom>" 
    and "\<And>xs. P xs \<Longrightarrow> P (delayFun\<cdot>xs)" and "\<And>xs x. P xs\<Longrightarrow> x\<noteq>\<bottom>\<Longrightarrow>xs\<noteq>\<bottom>\<Longrightarrow> P (tsMLscons\<cdot>x\<cdot>xs)"
    and "#s<\<infinity>"
  shows "ts_well s \<Longrightarrow> P (Abs_tstream s)"
proof (induction rule: stream_fin_induct)
  case 1
  then show ?case
    by (simp add: assms(1)) 
next
  case (2 u s)
   assume u_def: "u \<noteq> \<bottom>" and "(ts_well s \<Longrightarrow> P (Abs_tstream s))" and  "ts_well (u && s)"
      have s_well: "ts_well s"  using "2.prems"(1) ts_well_drop1 u_def by fastforce
      then show "P (Abs_tstream (u && s))"
                proof (cases "u=updis \<surd>")
                  case True
                    have "delayFun\<cdot>(Abs_tstream s) = Abs_tstream (u&&s)"
                      by (simp add: True delayfun_abststream s_well)
                  then show ?thesis
                    using \<open>ts_well s \<Longrightarrow> P (Abs_tstream s)\<close> assms(2) s_well by force
                next
                  case False
                    obtain m where m_def: "u = up\<cdot>(Discr (Msg m))"
                      by (metis (full_types) Exh_Up False discr.exhaust event.exhaust u_def)                        
                    have "s\<noteq>\<bottom>"
                      using "2.prems" m_def tsmsg_notwell by blast
                     hence "Abs_tstream (u&&s) = tsMLscons\<cdot>(updis m)\<cdot>(Abs_tstream s)"
                       by (metis Abs_Rep Rep_Abs Rep_tstream_bottom_iff m_def s_well tslscons_lscons tsmlscons2tslscons)
                  then show ?thesis
                    by (metis \<open>ts_well s \<Longrightarrow> P (Abs_tstream s)\<close> assms(3) s_well tsmlscons_bot2 up_defined)
                qed   
next
  case 3
  then show ?case by (simp add: assms(4))
qed

lemma tstream_fin_induct:
  assumes 
        "P \<bottom>" 
    and "\<And>xs. P xs \<Longrightarrow> P (delayFun\<cdot>xs)" and "\<And>xs x. P xs\<Longrightarrow> x\<noteq>\<bottom>\<Longrightarrow>xs\<noteq>\<bottom>\<Longrightarrow> P (tsMLscons\<cdot>x\<cdot>xs)"
    and "#\<surd>ts<\<infinity>"
  shows "P ts"
proof -
  obtain s where s_def: "Abs_tstream s = ts" and s_well: "ts_well s" using Abs_Rep ts_well_Rep by blast
  hence "#s < \<infinity>" using assms(4) finititeTicks by force
  hence "P (Abs_tstream s)"
    by (simp add: assms(1) assms(2) assms(3) s_well tstream_fin_induct_h)
  thus ?thesis by (simp add: s_def)    
qed     
  
  
lemma tstream_induct [case_names Adm Bot delayFun tsMLscons, induct type: tstream]:
  fixes ts
  assumes 
        "adm P"
    and "P \<bottom>"  
    and "\<And>ts. P ts \<Longrightarrow> P (delayFun\<cdot>ts)" and "\<And>ts t. P ts\<Longrightarrow> t\<noteq>\<bottom>\<Longrightarrow>ts\<noteq>\<bottom>\<Longrightarrow> P (tsMLscons\<cdot>t\<cdot>ts)"
  shows "P ts"
  by (metis assms(1) assms(2) assms(3) assms(4) tstream_fin_induct tstream_infs)

  
  
lemma "tsAbsNew\<cdot>ts= tsAbs\<cdot>ts"
  apply(induction)
     apply simp_all
  oops
    
end  