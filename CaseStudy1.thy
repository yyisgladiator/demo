(*  Title:        CaseStudy1
    Author:       Sebastian Stüber
    E-Mail:       sebastian.stueber@rwth-aachen.de
    Description:  Demo of TSB's / message class
*)


theory CaseStudy1
imports TSBTheorie

begin


(* Definiere Datentyp über dem die Ströme gebildet werden sollen *)
datatype M = Nats nat | Bools bool



(* Instanziiere M als "message". nötig da TSB über ::message definiert ist *)

(* Wichtig: die methode "ctype_XXX"  muss IMMER definiert sein.  (wobei XXX der name des Datentyps ist)

    Leider gibt es (noch) keine warnung wenn man die weglässt (oder den Namen anders schreibt...) *)
      (* und in den papers zum klassen system von Isabelle hab ich auch nichts gefunden... *)
instantiation M :: message
begin

  (* Definiert auf welchem Kanal welche Elemente fließen dürfen *)
   fun ctype_M :: "channel \<Rightarrow> M set" where
  "ctype_M c1 = range Nats" |
  "ctype_M c2 = range Bools"

  instance 
  by countable_datatype
end


(* das "empty" tsb. Auf keinem Kanal ist ein Strom *)
lift_definition tsb0 :: "M TSB" is "empty"
by simp

lemma "tsb0 = tsbLeast {}"
by(simp add: tsbLeast_def optionLeast_def tsb0_def)

lemma "tsbDom\<cdot>tsb0 = {}"
by(simp add: tsbdom_insert tsb0.rep_eq)





(* Helper für tsb1. Die erleichtern das leben *)
  lift_definition ts1_1 :: "M tstream" is "<[Msg (Nats 42), \<surd>, Msg (Nats 1337), \<surd>]>"
  by(simp add: ts_well_def)
  
  lift_definition ts1_2 :: "M tstream" is "<[Msg (Bools True), \<surd>, Msg (Bools False), \<surd>]>"
  by(simp add: ts_well_def)

lift_definition tsb1 :: "M TSB" is "[c1 \<mapsto> ts1_1, c2 \<mapsto> ts1_2]"
apply(simp add: tsb_well_def)
apply(simp add: tstickcount_insert tsdom_insert ts1_2.rep_eq ts1_1.rep_eq)
by auto

lemma "tsb1 . c1 = ts1_1"
by(simp add: tsbgetch_insert tsb1.rep_eq)

lemma "tsbDom\<cdot>tsb1 = {c1, c2}"
apply(simp add: tsbdom_insert tsb1.rep_eq)
by (simp add: insert_commute)





  
  lift_definition ts2_1 :: "M tstream" is "\<up>\<surd>\<infinity>"
  by(simp add: ts_well_def)
  
  lift_definition ts2_2 :: "M tstream" is "<[Msg (Bools True), \<surd>]>\<infinity>"
  by(simp add: ts_well_def slen_sinftimes)
  
  
lift_definition tsb2 :: "M TSB" is "[c1 \<mapsto> ts2_1, c2 \<mapsto> ts2_2]"
apply(rule tsb_wellI)
 apply(simp add: tsdom_insert tsbgetch_insert ts2_1.rep_eq ts2_2.rep_eq)
 apply(auto)
apply(simp add: tstickcount_insert ts2_1.rep_eq ts2_2.rep_eq sfilter_sinf)
by blast







(* und nochmal einen anderen Datentyp, weils so schön ist *)
instantiation nat :: message
begin

   fun ctype_nat :: "channel \<Rightarrow> nat set" where
  "ctype_nat c1 = {1,2,3}" |
  "ctype_nat c2 = {4,5,6}"

  instance ..
end


(* Helper für tsb3. Die erleichtern das leben *)
  lift_definition ts3_1 :: "nat tstream" is "<[Msg 2, \<surd>, Msg 3, \<surd>]>"
  by(simp add: ts_well_def)
  
  lift_definition ts3_2 :: "nat tstream" is "<[Msg 4, \<surd>, Msg 5, \<surd>]>"
  by(simp add: ts_well_def)

lift_definition tsb3 :: "nat TSB" is "[c1 \<mapsto> ts3_1, c2 \<mapsto> ts3_2]"
apply(simp add: tsb_well_def)
apply(simp add: tstickcount_insert tsdom_insert ts3_2.rep_eq ts3_1.rep_eq)
by auto



(* Helper für tsb4. Die erleichtern das leben *)
  lift_definition ts4_1 :: "nat tstream" is "<[Msg 2, \<surd>]>"
  by(simp add: ts_well_def)
  
  lift_definition ts4_2 :: "nat tstream" is "<[Msg 4, \<surd>]>"
  by(simp add: ts_well_def)

lift_definition tsb4 :: "nat TSB" is "[c1 \<mapsto> ts4_1, c2 \<mapsto> ts4_2]"
apply(simp add: tsb_well_def)
by(simp add: tstickcount_insert tsdom_insert ts4_2.rep_eq ts4_1.rep_eq)

lemma [simp]: "tsTake 1\<cdot>ts3_1 = ts4_1"
apply(simp add: tsTake_def)
apply(simp add: ts3_1.rep_eq)
by(simp add: tstakefirst_insert ts3_1.rep_eq ts4_1_def)

lemma [simp]: "tsTake 1\<cdot>ts3_2 = ts4_2"
apply(simp add: tsTake.simps ts3_2.rep_eq tstakefirst_insert)
apply(simp add: ts4_2_def)
done


thm tsb_eq

declare One_nat_def [simp del]

lemma "tsb3 \<down> 1 = tsb4"
apply (rule tsb_eq, simp_all)
apply(simp add: tsbdom_insert tsb4.rep_eq tsb3.rep_eq)
apply(simp add: tsb3.rep_eq tsbdom_insert)
by(auto simp add: tsb3.rep_eq tsbgetch_insert tsb4.rep_eq)


end
