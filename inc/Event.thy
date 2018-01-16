theory Event
  imports HOLCF

begin
default_sort countable


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



text {* Introduce symbol for ticks (@{text "\<surd>"}), marks the end of each time slot. *}
syntax
  "@Tick"     :: "'a event"       ("\<surd>")

translations
  "\<surd>"  == "CONST Tick"


(* If we get a message, apply the function directly to the message *)
(* On ticks return tick *)
fun eventApply :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a event \<Rightarrow> 'b event" where
"eventApply _ Tick = Tick" |
"eventApply f (Msg a) = Msg (f a)"


end