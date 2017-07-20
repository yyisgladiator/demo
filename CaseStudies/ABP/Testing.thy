(*  Title:        Testing.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Testing of the ABP components
*)

chapter {* Components of the Alternating Bit Protocol *}
                                                            
theory Testing
imports Medium Recv Sender

begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* testing *}
(* ----------------------------------------------------------------------- *)

text {* equivalence classes: empty tstream, finite tstream, infinite tstream *}

(* ----------------------------------------------------------------------- *)
subsection {* sender *}
(* ----------------------------------------------------------------------- *)

definition tsSndExampInp_1 :: "nat tstream" where
  "tsSndExampInp_1 = <[Msg 1, Msg 2, \<surd>, Msg 1, \<surd>]>\<surd>"


definition tsSndExampInp_2 :: "bool tstream" where
  "tsSndExampInp_2 = <[\<surd>, Msg True, Msg True, \<surd>, Msg False, \<surd>, Msg True, \<surd>]>\<surd>"

definition tsSndExampOut :: "(nat \<times> bool) tstream" where
  "tsSndExampOut = <[Msg (1, True), \<surd>,  Msg (2, False), Msg (2, False), \<surd>, \<surd>, Msg (1, True), \<surd>, \<surd>]>\<surd>"

(* ToDo: testing lemmata for sender *)

lemma tsmed_test_bot: "tsSnd\<cdot>\<bottom>\<cdot>tsInfTick = \<bottom>"
oops

lemma tssnd_test_fin: 
  "tsSnd\<cdot>tsSndExampInp_1\<cdot>(tsSndExampInp_2 \<bullet> tsInfTick)\<cdot>(Discr True) = tsSndExampOut"
oops

lemma tssnd_test_inf:
  "tsSnd\<cdot>(tsSndExampInp_1 \<bullet> tsInfTick)\<cdot>(tsSndExampInp_2 \<bullet> tsInfTick)\<cdot>(Discr True) 
       = tsSndExampOut \<bullet> tsInfTick"
oops

(* ----------------------------------------------------------------------- *)
subsection {* medium *}
(* ----------------------------------------------------------------------- *)

definition tsMedExampInp :: "nat tstream" where
  "tsMedExampInp = <[Msg 1, \<surd>, Msg 2, \<surd>, Msg 3, \<surd>]>\<surd>"


definition tsMedExampOut :: "nat tstream" where
  "tsMedExampOut = <[Msg 1, \<surd>, \<surd>, Msg 3, \<surd>]>\<surd>"


lemma tsmed_test_bot: "tsMed\<cdot>\<bottom>\<cdot>((\<up>True) \<infinity>) = \<bottom>"
by (simp add: tsmed_insert)

(* ToDo: testing lemmata for medium *)

lemma tsmed_test_fin: "tsMed\<cdot>tsMedExampInp\<cdot>((\<up>True) \<infinity>) = tsMedExampInp"
oops

lemma tsmed_test_fin2: "tsMed\<cdot>tsMedExampInp\<cdot>(<[True, False]> \<infinity>) = tsMedExampOut"
oops

lemma tsmed_test_inf:
  "tsMed\<cdot>(tsMedExampInp \<bullet> tsInfTick)\<cdot>((\<up>True) \<infinity>) = (tsMedExampInp \<bullet> tsInfTick)"
oops

(* ----------------------------------------------------------------------- *)
subsection {* receiver *}
(* ----------------------------------------------------------------------- *)

definition tsRecExampInp :: "(nat \<times> bool) tstream" where
  "tsRecExampInp = <[Msg (1, True), Msg (1, True), \<surd>, Msg (1, True), \<surd>, Msg (1, False), \<surd>]>\<surd>"

definition tsRecExampOut_1 :: "bool tstream" where
  "tsRecExampOut_1 = <[Msg True, Msg True, \<surd>, Msg True, \<surd>, Msg False, \<surd>]>\<surd>"

definition tsRecExampOut_2 :: "nat tstream" where
  "tsRecExampOut_2 = <[Msg 1, \<surd>, \<surd>, Msg 1, \<surd>]>\<surd>"

(* ToDo: testing lemmata for receiver *)

lemma tsrec_test_bot: "tsRec\<cdot>\<bottom> = \<bottom>"
oops

lemma tsrec_test_fin: "tsRec\<cdot>tsRecExampInp = (tsRecExampOut_1, tsRecExampOut_2)"
oops

lemma tsrec_test_inf:
  "tsRec\<cdot>(tsRecExampInp \<bullet> tsInfTick) = (tsRecExampOut_1 \<bullet> tsInfTick, tsRecExampOut_2 \<bullet> tsInfTick)"
oops
    
end