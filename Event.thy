theory Event
  imports Channel

begin

(* ----------------------------------------------------------------------- *)
section {* Type definition *}
(* ----------------------------------------------------------------------- *)


text {* Definition of  datatype  @{text "'m event"}; extends @{text "'m"} with a @{term "Tick"}. *}
datatype 'm event = Msg 'm ( "\<M> _" 65)| Tick

text {* Inverse of Msg.*}
abbreviation
  inversMsg ::  "'a event \<Rightarrow> 'a"  ("\<M>\<inverse> _")
    where "inversMsg e \<equiv> (case e of \<M> m \<Rightarrow> m)"

text {* Prove that datatype event is countable. Needed, since the domain-constructor defined
 to work for countable types.*}
instance event :: (countable) countable
by countable_datatype

(* use a datatype with event direcly as time-syncronus message on streams *)
instantiation event :: (message) message
begin
  definition ctype_event:: "channel \<Rightarrow> 'a event set" where "ctype_event c = {Tick} \<union> (Msg ` (ctype c))"

  instance..
end


text {* Introduce symbol for ticks (@{text "\<surd>"}), marks the end of each time slot. *}
syntax
  "@Tick"     :: "'a event"       ("\<surd>")

translations
  "\<surd>"  == "CONST Tick"

end