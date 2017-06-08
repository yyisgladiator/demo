(*  Title:        TStream_DS.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Workspace for Development of Functions on Timed Streams
*)

theory TStream_DS
 
imports TStream

begin  
default_sort countable

(* Here I just try a few things. *)

lemma tszip_tstickcount [simp]: "xs\<noteq>\<epsilon> \<Longrightarrow> #\<surd>(tsZip\<cdot>ts\<cdot>xs) = #\<surd>ts"
apply (induction ts)
apply (simp_all)
apply (metis tszip_delayfun delayFun_dropFirst delayfun_nbot tsdropfirst_len)
apply (simp add: tstickcount_mlscons)
oops

lemma tsabs_delayfun: "tsAbs\<cdot>(delayFun\<cdot>ts) = tsAbs\<cdot>ts"
by(simp add: delayFun_def)

lemma tsabs_mlscons: "ts\<noteq>\<bottom> \<Longrightarrow> tsAbs\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>ts) = (updis t) && (tsAbs\<cdot>ts)"
apply (simp add: tsmlscons2tslscons)
apply (subst tsabs_insert)
apply (simp add: tslscons_lscons uMsg_def lscons_conv)
by (simp add: tsabs_insert)

lemma tsabs_tszip_slen [simp]: "xs\<noteq>\<epsilon> \<Longrightarrow> #(tsAbs\<cdot>(tsZip\<cdot>ts\<cdot>(updis x && xs))) = #(tsAbs\<cdot>ts)"
apply (induction ts)
apply (simp_all)
apply (simp add: tsabs_delayfun tszip_delayfun)
apply (simp add: tszip_mlscons)
apply (subst tsabs_mlscons)
oops


 
lift_definition tsExampIn :: "nat tstream" is "<[Msg 1, Msg 2, \<surd>, Msg 2, \<surd>]>"
by (subst ts_well_def, auto)

lift_definition tsExampResult :: "nat tstream" is "<[Msg 1, Msg 2, \<surd>,  \<surd>]>"  
by (subst ts_well_def, auto)

lemma "tsRemDups\<cdot>tsExampIn = tsExampResult"
apply (simp add: tsExampIn_def tsExampResult_def tsRemDups_insert)
apply (subst absts2tsmlscons_msg2)
apply (metis One_nat_def eq_onp_same_args list2s.simps(1) list2s.simps(2) lscons_conv sup'_def 
       tsExampIn.rsp)
apply (subst absts2tsmlscons_msg2)
apply (metis sconc_scons ts_well_conc1 ts_well_sing_conc)
by (smt Abs_tstream_strict Rep_Abs Rep_tstream_strict absts2delayfun absts2tsmlscons_msg2
    discr.inject lscons_conv lscons_well n_not_Suc_n numeral_2_eq_2 sinftimes_unfold strictI
    strict_icycle sup'_def tick_msg ts_well_conc tslscons_bot2 tslscons_nbot2 tsmlscons_lscons
    tsremdups_h_delayfun tsremdups_h_mlscons tsremdups_h_strict tsremdups_h_tslscons_dup)

lemma 
  "tsZip\<cdot>(Abs_tstream (<[Msg 1, \<surd>, Msg 2, \<surd>]>))\<cdot>(<[True, False]>) = Abs_tstream (<[Msg (1, True), \<surd>, Msg (2, False), \<surd>]>)"
proof -
  have f1: "updis (\<surd>::'a event) && <[]> = \<up>\<surd>"
    by (simp add: sup'_def)
  then have f2: "ts_well (updis (\<surd>::'a event) && <[]>)"
    by (metis tick_msg)
  have f3: "ts_well (updis (\<M> 2::'a) && <[\<surd>]>)"
    by auto
  have f4: "delayFun\<cdot>(Abs_tstream (updis (\<M> 2::'a) && <[\<surd>]>)) = Abs_tstream (updis \<surd> && <[]>) \<bullet> Abs_tstream (updis (\<M> 2) && <[\<surd>]>)"
    using f1 delayfun_insert by auto
  have f5: "Rep_tstream (Abs_tstream (updis \<surd> && <[]>) \<bullet> Abs_tstream (updis (\<M> 2::'a) && <[\<surd>]>)) = <[\<surd>, \<M> 2, \<surd>]>"
    using f3 f2 f1 by (metis (no_types) list2s.simps(2) lscons_conv tsconc_rep_eq1)
  have f6: "updis (\<surd>::('a \<times> bool) event) && <[]> = \<up>\<surd>"
    by (metis list2s_0 sup'_def)
  have f7: "Rep_tstream (Abs_tstream (updis (\<surd>::('a \<times> bool) event) && <[]>) \<bullet> \<bottom>) = <[\<surd>]>"
    by (simp add: lscons_conv)
  have f8: "tsMLscons\<cdot>(updis (2::'a))\<cdot>(delayFun\<cdot>\<bottom>) = Abs_tstream (updis (\<M> 2) && <[\<surd>]>)"
    by (simp add: delayfun_insert tsmlscons_lscons3)
  have f9: "Rep_tstream (Abs_tstream (updis \<surd> && <[]>) \<bullet> Abs_tstream (updis (\<M> (2::'a, False)) && <[\<surd>]>)) = (updis \<surd> && <[]>) \<bullet> updis (\<M> (2, False)) && <[\<surd>]>"
    by (simp add: tsconc_rep_eq1)
  have "Abs_tstream (updis \<surd> && <[]>) \<bullet> Abs_tstream (updis (\<M> (2::'a, False)) && <[\<surd>]>) \<noteq> \<bottom>"
    using f6 by force
  then have f10: "tsMLscons\<cdot>(updis (1::'a, True))\<cdot> (Abs_tstream (updis \<surd> && <[]>) \<bullet> Abs_tstream (updis (\<M> (2, False)) && <[\<surd>]>)) = Abs_tstream (updis (\<M> (1, True)) && Rep_tstream (Abs_tstream (updis \<surd> && <[]>) \<bullet> Abs_tstream (updis (\<M> (2, False)) && <[\<surd>]>)))"
    using tsmlscons_lscons3 by blast
  have f11: "tsMLscons\<cdot>(updis (2::'a, False))\<cdot> (Abs_tstream (updis \<surd> && <[]>) \<bullet> \<bottom>) = Abs_tstream (updis (\<M> (2, False)) && Rep_tstream (Abs_tstream (updis \<surd> && <[]>) \<bullet> \<bottom>))"
    by (simp add: lscons_conv tsmlscons_lscons3)
  have "Abs_tstream (updis \<surd> && <[]>) \<bullet> Abs_tstream (updis (\<M> 2::'a) && <[\<surd>]>) \<noteq> \<bottom>"
    using f1 by auto
  then show ?thesis
    using f11 f10 f9 f8 f7 f6 f5 f4 by (metis (no_types) delayfun_insert list2s.simps(2) list2s_0 lscons_conv tsmlscons_lscons3 tszip_mlscons_msgdelayfun tszip_strict(2))
qed

(*
definition tsZip_h :: "'a event stream \<rightarrow> 'b stream \<rightarrow> ('a \<times> 'b) event stream" where
"tsZip_h \<equiv> fix\<cdot>(\<Lambda> h s q. if s = \<epsilon> \<or> q = \<epsilon> then \<epsilon> 
                         else if shd s = \<surd> then \<up>\<surd> \<bullet> h\<cdot>(srt\<cdot>s)\<cdot>q
                         else \<up>(\<M> (\<M>\<inverse> (shd s), shd q)) \<bullet> h\<cdot>(srt\<cdot>s)\<cdot>(srt\<cdot>q))"

definition tsZip :: "'a tstream \<rightarrow> 'b stream \<rightarrow> ('a \<times> 'b) tstream" where
"tsZip \<equiv> \<Lambda> ts s. Abs_tstream (tsZip_h\<cdot>(Rep_tstream ts)\<cdot>s)"

definition tsRemDups_h :: "'a option event \<Rightarrow> 'a option event stream \<rightarrow> 'a option event stream" where
"tsRemDups_h \<equiv> fix\<cdot>(\<Lambda> h. (\<lambda> q. (\<Lambda> s. if s = \<epsilon> then \<epsilon> 
                                     else if shd s = \<surd> then (\<up>\<surd> \<bullet> h q\<cdot>(srt\<cdot>s))
                                     else if shd s \<noteq> q then (\<up>(shd s) \<bullet> h (shd s)\<cdot>(srt\<cdot>s))
                                     else h q\<cdot>(srt\<cdot>s))))"

definition tsRemDups :: "'a tstream \<rightarrow> 'a tstream" where
"tsRemDups \<equiv> \<Lambda> ts. Abs_tstream (smap (\<lambda>x. case x of Msg (Some m) \<Rightarrow> (Msg m))\<cdot>(tsRemDups_h (\<M> None)\<cdot>(Rep_tstream (tsMap Some\<cdot>ts))))"
*)

end  