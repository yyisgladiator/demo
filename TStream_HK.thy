(*  Title:        TStreamTheorie_HK.thy
*)

chapter {* Timed Streams *}                                                              

theory TStream_HK

imports TStream
begin

primrec list2ts :: "'a event list \<Rightarrow> 'a tstream"
where
  list2ts_0:   "list2ts [] = \<bottom>" |
  list2ts_Suc: "list2ts (a#as) = (tsLscons\<cdot>(updis a)\<cdot>(list2ts as))"


primrec list2ts_alter :: "'a event list \<Rightarrow> 'a tstream"
where
  list2ts_alter_0:   "list2ts_alter [] = \<bottom>" |
  list2ts_alter_Suc: "list2ts_alter (a#as) = (if a=\<surd> then delayFun\<cdot>(list2ts_alter as) else (tsMLscons\<cdot>(updis \<M>\<inverse> a)\<cdot>(list2ts_alter as)))"

(*
primrec l2ts::"nat \<Rightarrow> 'a event discr u list \<Rightarrow> 'a tstream \<Rightarrow> 'a tstream" where
"l2ts 0 l ts= ts"|
"l2ts (Suc n) l ts = (if l=[] then ts else l2ts n (butlast l) (tsLscons\<cdot>(last l)\<cdot>ts))"

definition l2tstream::"'a event discr u list \<Rightarrow> 'a tstream" where
"l2tstream l = l2ts (length l) l \<bottom> "
*)


(************************************************)
  subsection \<open>list2ts\<close>    
(************************************************)

lemma testlist2ts: "list2ts ([\<M> True,\<M> False, \<surd>,\<M> False]) = Abs_tstream (<[Msg True,Msg False,\<surd>]>)"
apply (simp add: tslscons_insert)
apply (simp add: espf2tspf_def)+
apply (subst lscons_conv)+
by simp

lemma testlist2ts_alter: "list2ts_alter ([\<M> True,\<M> False, \<surd>,\<M> False]) = tsMLscons\<cdot>(updis True)\<cdot>(tsMLscons\<cdot>(updis False)\<cdot>(delayFun\<cdot>\<bottom>))"
by (simp add: tslscons_insert)
(*
lemma testl2tstream: "l2tstream ([updis (\<M> 1),updis (\<M> 1),(updis \<surd>),updis (\<M> 1)]) = Abs_tstream (<[Msg 1,Msg 1,\<surd>]>)"
apply (simp add: l2tstream_def tslscons_insert)
apply (simp add: espf2tspf_def)+
apply (subst lscons_conv)+
by simp
*)