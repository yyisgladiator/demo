



theory AutomatonPrelude

imports "../../untimed/CaseStudy/Automaton" "../tsynStream" "../tsynBundle"

begin

fun prepend:: "'a::type list \<Rightarrow> 'a::type \<Rightarrow> 'a::type list" where
    "prepend xs x= x#xs"

(* SWS: der Datentyp Name (Message) sollte nicht immer gleich sein, sonst hast du schnell mehrere Datentypen die alle gleich heißen *)
(* SWS: nach konvention ist der Datentyp-Konstruktor groß geschrieben. Also (Bool "bool" | Nat "nat") *)
(* SWS: auch nach konvention sind datentypen klein geschrieben... also "message"... *)
(* SWS: das Pair kannst du auch anders codieren: Pair_nat_bool2 "nat" "bool". Nur so als Info, hat nicht wirkliche vorteile *)
datatype Message = nat "nat" | bool "bool" | Pair_nat_bool "(nat\<times>bool)" (* SWS: Leerzeile :D *)
instance Message :: countable
apply(intro_classes)    (* SWS: 2 Leerzeichen einrücken *)
by(countable_datatype)

instantiation Message :: message
begin (* SWS: ganze "fun" einrücken" *)
fun ctype_Message :: "channel  \<Rightarrow> Message set" where (* SWS: coole kommentare! *)
"ctype_Message c1 = range bool"  (*MediumRS.as -> Sender.as*)| 
"ctype_Message c2 = range Pair_nat_bool"  (*MediumSR.dr -> Receiver.dr*)| 
"ctype_Message c3 = range Pair_nat_bool"  (*Sender.ds -> MediumSR.ds*)| 
"ctype_Message c4 = range bool"  (*Receiver.ar -> MediumRS.ar*)| 
"ctype_Message c5 = range nat"  (*Receiver.o*)| 
"ctype_Message c6 = range nat"  (*Sender.i*)    (* SWS: Leerzeile + instance einrücken *)
instance
by(intro_classes)
end


end