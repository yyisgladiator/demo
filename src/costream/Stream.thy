section \<open>Lazy Streams\<close> 

theory Stream
imports inc.LNat inc.SetPcpo
begin

section \<open>The Datatype of Lazy Streams for counterexample\<close>

default_sort countable

(* deletes the Rule "1 = Suc 0" *)
 declare One_nat_def[simp del]

(* declare [[show_types]] *)
text \<open>\<open>discr u\<close> lifts an arbitrary type \<open>'a\<close> to the
  discrete \<open>pcpo\<close> and the usual rest operator \<open>rt\<close> on streams.\<close>

codatatype 'a stream = Sbot | SCons (lshd:"'a discr u") (srt: "'a stream")
                                        (infixr "&&" 65)

instantiation stream::(countable) pcpo
(*TODO below and proof*)
begin
instance
  sorry
end

definition sdrop      :: "nat \<Rightarrow> 'a stream \<rightarrow> 'a stream" where
"sdrop n \<equiv> Fix.iterate n\<cdot>(Abs_cfun srt)"

definition shd        :: "'a stream \<Rightarrow> 'a" where
"shd s \<equiv> THE a. lshd s = updis a"

definition slen       :: "'a stream \<rightarrow> lnat" where
"slen \<equiv> fix\<cdot>(\<Lambda> h. strictify\<cdot>(\<Lambda> s. lnsuc\<cdot>(h\<cdot>(srt s))))"

abbreviation slen_abbr :: "'a stream \<Rightarrow> lnat" ("#_" [1000] 999)
where "#s == slen\<cdot>s"

text \<open>@{term snth}: Get the \<open>n\<close>th element of the stream.\<close>
definition snth       :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a" where
"snth k s \<equiv> shd (sdrop k\<cdot>s)" 

text\<open>@{term sfoot}: Get the last element of a not empty, finite stream\<close>
definition sfoot      :: "'a stream \<Rightarrow> 'a" where
"sfoot s = snth (THE a. lnsuc\<cdot>(Fin a) = #s) s"

text \<open>@{term sdom}: Retrieve the set of all values in a stream.\<close>
definition sdom       :: "'a stream \<rightarrow> 'a set" where
"sdom \<equiv> \<Lambda> s. {snth n s | n. Fin n < #s}" 
(*
TODO: 
  1. check where SB.thy doesn't work with this stream Theorie
  2. add lemmas in THIS Theory so it works (DO NOT CHANGE LEMMAS OR PROOFS IN OTHER THEORIES!!!!)
  3. repeat for other theories until dAutomaton_causal works.
*)
end