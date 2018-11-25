(*  Title:        Receiver.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Receiver Component of the ABP on Timed Streams
*)

chapter {* Receiver of the Alternating Bit Protocol *}
                                                            
theory Receiver                 
imports TStream
                                        
begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* definition *}
(* ----------------------------------------------------------------------- *)

definition tsRecSnd :: "('a \<times> 'b) tstream \<rightarrow> 'a tstream" where
"tsRecSnd \<equiv> \<Lambda> dat. tsProjFst\<cdot>(tsRemDups\<cdot>dat)"

definition tsRec :: "('a \<times> 'b) tstream \<rightarrow> ('b tstream \<times> 'a tstream)" where
"tsRec \<equiv> \<Lambda> dat. (tsProjSnd\<cdot>dat, tsRecSnd\<cdot>dat)"

(* ----------------------------------------------------------------------- *)
subsection {* basic properties *}
(* ----------------------------------------------------------------------- *)

lemma tsrecsnd_insert: "tsRecSnd\<cdot>dat = tsProjFst\<cdot>(tsRemDups\<cdot>dat)"
  by (simp add: tsRecSnd_def)

lemma tsrecsnd_strict [simp]: "tsRecSnd\<cdot>\<bottom> = \<bottom>"
  by (simp add: tsRecSnd_def tsremdups_insert)

lemma tsrecsnd_delayfun: "tsRecSnd\<cdot>(delayFun\<cdot>dat) = delayFun\<cdot>(tsRecSnd\<cdot>dat)"
  by (simp add: tsRecSnd_def tsremdups_insert tsremdups_h_delayfun tsprojfst_delayfun)

lemma tsrecsnd_nbot [simp]: "dat\<noteq>\<bottom> \<Longrightarrow> tsRecSnd\<cdot>dat \<noteq> \<bottom>"
  by (simp add: tsrecsnd_insert)

lemma tsrecsnd_tstickcount [simp]: "#\<surd>(tsRecSnd\<cdot>dat) = #\<surd>dat"
  by (simp add: tsrecsnd_insert)

lemma tsrecsnd_inftick [simp]: "tsRecSnd\<cdot>tsInfTick = tsInfTick"
  by (simp add: tsrecsnd_delayfun)

lemma tsrec_insert: "tsRec\<cdot>dat = (tsProjSnd\<cdot>dat, tsRecSnd\<cdot>dat)"
  by (simp add: tsRec_def)

lemma tsrec_strict [simp]: "tsRec\<cdot>\<bottom> = \<bottom>"
  by (simp add: tsRec_def)

lemma tsrec_delayfun: "tsRec\<cdot>(delayFun\<cdot>dat) = (delayFun\<cdot>(tsProjSnd\<cdot>dat), delayFun\<cdot>(tsRecSnd\<cdot>dat))"
  by (simp add: tsprojsnd_delayfun tsrec_insert tsrecsnd_delayfun)

lemma tsrec_nbot [simp]: "dat\<noteq>\<bottom> \<Longrightarrow> tsRec\<cdot>dat \<noteq> \<bottom>"
  by (simp add: tsrec_insert)

lemma tsrec_inftick [simp]: "tsRec\<cdot>tsInfTick = (tsInfTick, tsInfTick)"
  by (simp add: tsrec_insert tsprojsnd_delayfun)
    
end