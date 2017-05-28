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


    
lemma tstream_adm: assumes "chain Y"  
          and "\<And>i. ts_well (Y i) \<Longrightarrow> P (Abs_tstream (Y i))" 
          and "ts_well (\<Squnion>i. Y i)"
          and "adm P"
        shows " P (Abs_tstream (\<Squnion>i. Y i))"
proof -
  obtain n where n_def: "ts_well (Y n)" sorry (* gilt glaub ich nicht *)
  obtain K where K_ch: "chain K" and K_lub: "(\<Squnion>i. Y i) = (\<Squnion>i. K i)" 
                and K_p:  "\<And>i. P(Abs_tstream (K i))" and K_well: "\<And>i. ts_well (K i)" sorry
  hence "chain (\<lambda>i. Abs_tstream (K i))"
    by (simp add: below_tstream_def po_class.chain_def)
  thus ?thesis
    by (metis (mono_tags, lifting) K_lub K_p K_well Rep_Abs adm_def assms(4) lub_eq lub_tstream) 
qed

lemma tsmlscons_obtain: assumes "t\<noteq>\<bottom>" and "xs\<noteq>\<bottom>"  
  obtains x where "Rep_tstream (tsMLscons\<cdot>t\<cdot>xs) = x&&(Rep_tstream xs)" and "x\<noteq>\<bottom>"
proof -
  obtain n where n_def: "t = updis n"
    by (metis (full_types) assms(1) discr.exhaust upE) 
  thus ?thesis
    by (simp add: assms(2) that tslscons_lscons tsmlscons2tslscons)
qed
  

lemma tsmsg_notwell: "\<not>ts_well((updis (Msg m)) && \<bottom>)"
  apply(simp add: ts_well_def)
  by (metis Inf'_neq_0 event.distinct(1) fold_inf lnat.sel_rews(2) lscons_conv sfilterl4 sfoot1 sfoot_one slen_scons strict_slen sup'_def)
    
lemma tstream_induct_h:
  fixes ts
  assumes 
        "P \<bottom>" 
    and "\<And>xs. P xs \<Longrightarrow> P (delayFun\<cdot>xs)" and "\<And>xs x. P xs\<Longrightarrow> x\<noteq>\<bottom>\<Longrightarrow>xs\<noteq>\<bottom>\<Longrightarrow> P (tsMLscons\<cdot>x\<cdot>xs)"
    and "adm P"
  shows "ts_well s \<Longrightarrow> P (Abs_tstream s)"
    proof (induction s)
      case adm
      then show ?case using adm_def assms(4) tstream_adm by blast
    next
      case bottom
      then show ?case
        by (simp add: assms(1)) 
    next
      case (lscons u s)
      assume u_def: "u \<noteq> \<bottom>" and "(ts_well s \<Longrightarrow> P (Abs_tstream s))" and  "ts_well (u && s)"
      have s_well: "ts_well s" using lscons.prems ts_well_drop1 u_def by fastforce
      then show ?case
                proof (cases "u=updis \<surd>")
                  case True
                    have "delayFun\<cdot>(Abs_tstream s) = Abs_tstream (u&&s)"
                      by (simp add: True delayfun_abststream s_well)
                  then show ?thesis
                    using assms(2) lscons.IH s_well by force 
                next
                  case False
                    obtain m where m_def: "u = up\<cdot>(Discr (Msg m))"
                      by (metis (full_types) Exh_Up False discr.exhaust event.exhaust u_def)                        
                    have "s\<noteq>\<bottom>"
                      using lscons.prems m_def tsmsg_notwell by blast
                     hence "Abs_tstream (u&&s) = tsMLscons\<cdot>(updis m)\<cdot>(Abs_tstream s)"
                       by (metis Abs_Rep Rep_Abs Rep_tstream_bottom_iff m_def s_well tslscons_lscons tsmlscons2tslscons)
                  then show ?thesis by (simp add: \<open>s \<noteq> \<epsilon>\<close> assms(3) lscons.IH s_well)
                qed
    qed

    
lemma tstream_induct [case_names Adm Bot tsLscons, induct type: tstream]:
  fixes ts
  assumes 
        "adm P"
    and "P \<bottom>"  
    and "\<And>ts. P ts \<Longrightarrow> P (delayFun\<cdot>ts)" and "\<And>ts t. P ts\<Longrightarrow> t\<noteq>\<bottom>\<Longrightarrow>ts\<noteq>\<bottom>\<Longrightarrow> P (tsMLscons\<cdot>t\<cdot>ts)"
  shows "P ts"
proof -
  obtain s where s_def: "ts = Abs_tstream s \<and> ts_well s"  using Abs_tstream_cases by blast
  thus ?thesis
    by (simp add: s_def assms(1) assms(2) assms(3) assms(4) tstream_induct_h) 
qed
  
  
lemma "tsAbsNew\<cdot>ts= tsAbs\<cdot>ts"
  apply(induction)
     apply simp_all
  oops
    
end  