theory Event
  imports inc.Channel inc.UnivClasses

begin
default_sort countable


(* ----------------------------------------------------------------------- *)
section {* Type definition *}
(* ----------------------------------------------------------------------- *)


text {* Definition of  datatype  @{text "'m event"}; extends @{text "'m"} with a @{term "Tick"}. *}
datatype 'm event = Msg 'm ( "\<M> _" 65)| Tick 
setup_lifting type_definition_event

text {* Inverse of Msg.*}
abbreviation
  inversMsg ::  "'a event \<Rightarrow> 'a"  ("\<M>\<inverse> _")
    where "inversMsg e \<equiv> (case e of \<M> m \<Rightarrow> m)"

text {* Prove that datatype event is countable. Needed, since the domain-constructor defined
 to work for countable types.*}
instance event :: (countable) countable
by countable_datatype

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


(* If we get a message, apply the function directly to the message *)
(* On ticks return tick *)
fun eventApply :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a event \<Rightarrow> 'b event" where
"eventApply _ Tick = Tick" |
"eventApply f (Msg a) = Msg (f a)"


lemma ctype_eventI: assumes "a \<in> ctype c"
  shows "Msg a \<in> ctype c"
  by (simp add: assms ctype_event_def)

lemma ctype_event_iff: "a \<in> ctype c \<longleftrightarrow> Msg a \<in> ctype c"
  by (simp add: ctype_event_def image_iff)

(*For DoubleInputAutomaton*)
lemma dom2exElem:assumes"dom f = {c1,c2} "shows " \<exists>aa ba. f = [c1 \<mapsto> aa, c2 \<mapsto> ba]"
    by (smt assms domD dom_eq_singleton_conv dom_fun_upd fun_upd_def fun_upd_triv fun_upd_twist fun_upd_upd insertI1 insert_absorb)
  
lemma domEventExhaust:assumes"dom f = {c1,c2} "shows " \<exists>aa ba. f = [c1 \<mapsto> \<M> aa, c2 \<mapsto> \<M> ba] \<or> f = [c1 \<mapsto> \<surd>, c2 \<mapsto> \<M> ba] \<or> f = [c1 \<mapsto> \<M> aa, c2 \<mapsto> \<surd>] \<or> f = [c1 \<mapsto> \<surd>, c2 \<mapsto> \<surd>]"
proof-
  obtain x y where "f = [c1 \<mapsto> x, c2 \<mapsto> y]"
    using assms dom2exElem by blast
  have h1:"\<exists>aa. x = \<M> aa \<or> x = \<surd>"
    using event.exhaust by auto
  have h2:"\<exists>aa. y = \<M> aa \<or> y = \<surd>"
    using event.exhaust by auto
  show "\<exists>(aa::'a) ba::'a. f = [c1 \<mapsto> \<M> aa, c2 \<mapsto> \<M> ba] \<or> f = [c1 \<mapsto> \<surd>, c2 \<mapsto> \<M> ba] \<or> f = [c1 \<mapsto> \<M> aa, c2 \<mapsto> \<surd>] \<or> f = [c1 \<mapsto> \<surd>, c2 \<mapsto> \<surd>]"
    using \<open>(f::channel \<Rightarrow> 'a event option) = [c1 \<mapsto> x::'a event, c2 \<mapsto> y::'a event]\<close> h1 h2 by blast
qed


end