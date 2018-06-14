



theory AutomatonPrelude

imports "../../untimed/CaseStudy/Automaton" "../tsynStream" "../tsynBundle" "abp/CounterDataTypes"

begin

fun prepend:: "'a::type list \<Rightarrow> 'a::type \<Rightarrow> 'a::type list" where
    "prepend xs x= x#xs"

datatype Message = nat "nat" | bool "bool" | Pair_nat_bool "(nat\<times>bool)"
instance Message :: countable
apply(intro_classes)
by(countable_datatype)

instantiation Message :: message
begin
fun ctype_Message :: "channel  \<Rightarrow> Message set" where
"ctype_Message c1 = range bool"  (*MediumRS.as -> Sender.as*)| 
"ctype_Message c2 = range Pair_nat_bool"  (*MediumSR.dr -> Receiver.dr*)| 
"ctype_Message c3 = range Pair_nat_bool"  (*Sender.ds -> MediumSR.ds*)| 
"ctype_Message c4 = range bool"  (*Receiver.ar -> MediumRS.ar*)| 
"ctype_Message c5 = range nat"  (*Receiver.o*)| 
"ctype_Message c6 = range nat"  (*Sender.i*)
instance
by(intro_classes)
end


end