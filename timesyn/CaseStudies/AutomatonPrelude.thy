(*
 * DO NOT MODIFY!
 * This file was generated and will be overridden when the models change.
 *
 * Generated on Jul 4, 2018 5:25:36 PM by transformer 1.0.0
 *)
theory AutomatonPrelude

imports "../../untimed/CaseStudy/dAutomaton" "../../untimed/CaseStudy/ndAutomaton" "../tsynStream" "../tsynBundle" 

begin

fun prepend:: "'a::type list \<Rightarrow> 'a::type \<Rightarrow> 'a::type list" where
"prepend xs x= x#xs"

datatype abpMessage = Nat "nat" | Bool "bool" | Pair_nat_bool "(nat\<times>bool)"

instance abpMessage :: countable
  apply(intro_classes)
  by(countable_datatype)

instantiation abpMessage :: message
begin
  fun ctype_abpMessage :: "channel  \<Rightarrow> abpMessage set" where
  "ctype_abpMessage c = (
    if c = \<C> ''as'' then range Bool else                 (* MediumRS.as -> Sender.as *)
    if c = \<C> ''dr'' then range Pair_nat_bool else        (* MediumSR.dr -> Receiver.dr *)
    if c = \<C> ''ds'' then range Pair_nat_bool else        (* Sender.ds -> MediumSR.ds *)
    if c = \<C> ''ar'' then range Bool else                 (* Receiver.ar -> MediumRS.ar *)
    if c = \<C> ''o'' then range Nat else                   (* Receiver.o *)
    if c = \<C> ''i'' then range Nat else                   (* Sender.i *)
    {})"

  instance
    by(intro_classes)
end

lift_definition createAsBundle :: "bool \<Rightarrow> abpMessage tsyn SB" is
"\<lambda>x. [ \<C> ''as'' \<mapsto> \<up>(Msg (Bool x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createDrBundle :: "(nat\<times>bool) \<Rightarrow> abpMessage tsyn SB" is
"\<lambda>x. [ \<C> ''dr'' \<mapsto> \<up>(Msg (Pair_nat_bool x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createDsBundle :: "(nat\<times>bool) \<Rightarrow> abpMessage tsyn SB" is
"\<lambda>x. [ \<C> ''ds'' \<mapsto> \<up>(Msg (Pair_nat_bool x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createArBundle :: "bool \<Rightarrow> abpMessage tsyn SB" is
"\<lambda>x. [ \<C> ''ar'' \<mapsto> \<up>(Msg (Bool x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createOBundle :: "nat \<Rightarrow> abpMessage tsyn SB" is
"\<lambda>x. [ \<C> ''o'' \<mapsto> \<up>(Msg (Nat x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createIBundle :: "nat \<Rightarrow> abpMessage tsyn SB" is
"\<lambda>x. [ \<C> ''i'' \<mapsto> \<up>(Msg (Nat x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

end