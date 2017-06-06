(*  Title:        TimedABP_DS.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Workspace for the  Definition of Alternating Bit Protocol on Timed Streams
*)

chapter {* Alternating Bit Protocol *}       
                                                            
theory TimedABP_DS
imports "../TStream_DS"

begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* components definition *}
(* ----------------------------------------------------------------------- *)

definition tsRecSnd :: "('a \<times> 'b) tstream \<rightarrow> 'a tstream" where
"tsRecSnd \<equiv> \<Lambda> dat. tsProjFst\<cdot>(tsRemDups\<cdot>dat)"

definition tsRec :: "('a \<times> 'b) tstream \<rightarrow> ('b tstream \<times> 'a tstream)" where
"tsRec \<equiv> \<Lambda> dat. (tsProjSnd\<cdot>dat, tsRecSnd\<cdot>dat)"

(* ----------------------------------------------------------------------- *)
section {* basic properties *}
(* ----------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------- *)
subsection {* receiver *}
(* ----------------------------------------------------------------------- *)

lemma tsrecsnd_insert: "tsRecSnd\<cdot>dat = tsProjFst\<cdot>(tsRemDups\<cdot>dat)"
by (simp add: tsRecSnd_def)

lemma tsrecsnd_strict [simp]: "tsRecSnd\<cdot>\<bottom> = \<bottom>"
oops

lemma tsrecsnd_mlscons_dup:
  "tsRecSnd\<cdot>(tsMLscons\<cdot>(updis (d1, d2))\<cdot>(tsMLscons\<cdot>(updis (d1, d4))\<cdot>dat))
         = tsMLscons\<cdot>(updis d1)\<cdot>(tsRecSnd\<cdot>dat)"
oops

lemma tsrecsnd_mlscons_ndup: "d1\<noteq>d3 \<Longrightarrow>
  tsRecSnd\<cdot>(tsMLscons\<cdot>(updis (d1, d2))\<cdot>(tsMLscons\<cdot>(updis (d3, d4))\<cdot>dat))
         = tsMLscons\<cdot>(updis d1)\<cdot>(tsMLscons\<cdot>(updis d3)\<cdot>(tsRecSnd\<cdot>dat))"
oops

lemma tsrecsnd_mlscons_delayfun_dup: 
  "tsRecSnd\<cdot>(tsMLscons\<cdot>(updis (d1, d2))\<cdot>(delayFun\<cdot>(tsMLscons\<cdot>(updis (d1, d4))\<cdot>dat)))
          = tsMLscons\<cdot>(updis d1)\<cdot>(delayFun\<cdot>(tsRecSnd\<cdot>dat))"
oops

lemma tsrecsnd_mlscons_delayfun_ndup: "d1\<noteq>d3 \<Longrightarrow>
  tsRecSnd\<cdot>(tsMLscons\<cdot>(updis (d1, d2))\<cdot>(delayFun\<cdot>(tsMLscons\<cdot>(updis (d3, d4))\<cdot>dat)))
         = tsMLscons\<cdot>(updis d1)\<cdot>(delayFun\<cdot>(tsMLscons\<cdot>(updis d3)\<cdot>(tsRecSnd\<cdot>dat)))"
oops

lemma tsrecsnd_delayfun: "tsRecSnd\<cdot>(delayFun\<cdot>dat) = delayFun\<cdot>(tsRecSnd\<cdot>dat)"
oops

lemma tsrecsnd_tstickcount [simp]: "#\<surd>(tsRecSnd\<cdot>dat) = #\<surd>dat"
oops

lemma tsrec_insert: "tsRec\<cdot>dat = (tsProjSnd\<cdot>dat, tsRecSnd\<cdot>dat)"
by (simp add: tsRec_def)

lemma tsrec_strict [simp]: "tsRec\<cdot>\<bottom> = \<bottom>"
oops

lemma tsrec_delayfun: "tsRec\<cdot>(delayFun\<cdot>dat) = (delayFun\<cdot>(tsProjSnd\<cdot>dat), delayFun\<cdot>(tsRecSnd\<cdot>dat))"
oops

(* ----------------------------------------------------------------------- *)
section {* testing *}
(* ----------------------------------------------------------------------- *)

text {* equivalence classes: empty tstream, finite tstream, infinite tstream *}

(* ----------------------------------------------------------------------- *)
subsection {* receiver *}
(* ----------------------------------------------------------------------- *)

lift_definition OneTrue3OneFalse :: "(nat \<times> bool) tstream" is
  "<[Msg (1, True), Msg (1, True), \<surd>, Msg (1, True), \<surd>, Msg (1, False), \<surd>]>"
by (subst ts_well_def, auto)

lift_definition True3False :: "bool tstream" is
  "<[Msg True, Msg True, \<surd>, Msg True, \<surd>, Msg False, \<surd>]>"
by (subst ts_well_def, auto)

lift_definition OneOne :: "nat tstream" is
  "<[Msg 1, \<surd>, \<surd>, Msg 1, \<surd>]>"
by (subst ts_well_def, auto)

lemma "tsRec\<cdot>\<bottom> = \<bottom>"
oops

lemma "tsRec\<cdot>OneTrue3OneFalse = (True3False, OneOne)"
oops

lemma "tsRec\<cdot>(OneTrue3OneFalse \<bullet> tsInfTick) = (True3False \<bullet> tsInfTick, OneOne \<bullet> tsInfTick)"
oops
    
end