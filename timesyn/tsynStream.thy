(*  Title:  tsynStream
    Author: Sebastian Stüber
    e-mail: sebastian.stueber@rwth-aachen.de

    Description: time-syncronus streams. A time-inverval may at most have one message. 
      No message is described with "Tick"
      Notice that the time-interpretation is different to "tstream": 
        <[Msg 1, Tick]> are 2 time-steps, in the first one the message 1 is sent, in the second no
        message is sent
*)


theory tsynStream

imports "../untimed/Streams" "../inc/Event"

begin


(* TODO: move to Event.thy *)
(* If we get a message, apply the function directly to the message *)
(* On ticks return tick *)
fun eventApply :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a event \<Rightarrow> 'b event" where
"eventApply _ Tick = Tick" |
"eventApply f (Msg a) = Msg (f a)"


section \<open>Definitions\<close>


(* returns the set with all Msg in t. No ticks *)
definition tsynDom :: "'a event stream \<rightarrow> 'a set" where
"tsynDom \<equiv> \<Lambda> ts . {a | a. (Msg a) \<in> sdom\<cdot>ts}"



thm smap_def
definition tsynMap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a event stream \<rightarrow> 'b event stream" where
"tsynMap f = smap (eventApply f)"


(* Behaves like sscanlA, but on time-syncronus streams *)
(* Ignore all ticks, do not modify the state and output tick *)
definition tsynScanlA :: "('s \<Rightarrow>'a \<Rightarrow> ('b \<times>'s)) \<Rightarrow> 's  \<Rightarrow> 'a event stream \<rightarrow> 'b event stream" where
"tsynScanlA f = sscanlA (\<lambda> s a. case a of (Msg m) \<Rightarrow> (Msg (fst (f s m)), (snd (f s m))) | Tick \<Rightarrow> (Tick, s))"


(* Behaves like sscanlA, but on time-syncronus streams *)
(* Ignore all ticks, do not modify the state and output tick *)
definition tsynScanl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b  \<Rightarrow> 'a event stream \<rightarrow> 'b event stream" where
"tsynScanl f b0 = tsynScanlA (\<lambda>b a. (f b a,f b a)) b0 "




section \<open>Lemma\<close>

subsection \<open>tsynMap\<close>
lemma tsynmap_len [simp]: "#(tsynMap f\<cdot>s) = #s"
  by (simp add: tsynMap_def)

lemma tsynmap_bot [simp]: "tsynMap f\<cdot>\<bottom> = \<bottom>"
  by (simp add: tsynMap_def)

lemma tsynmap_tick [simp]: "tsynMap f\<cdot>(\<up>Tick \<bullet> s) = \<up>Tick \<bullet> tsynMap f\<cdot>s"
  by (simp add: tsynMap_def)

lemma tsynmap_msg [simp]: "tsynMap f\<cdot>(\<up>(Msg m) \<bullet> s) = \<up>(Msg (f m)) \<bullet> tsynMap f\<cdot>s"
  by (simp add: tsynMap_def)



subsection \<open>tsynScanlA\<close>

lemma tsynscanla_len [simp]: "#(tsynScanlA f b\<cdot>s) = #s"
  unfolding tsynScanlA_def
  using sscanla_len by blast

lemma tsynscanla_bot [simp]: "tsynScanlA f b\<cdot>\<bottom> = \<bottom>"
  unfolding tsynScanlA_def
  by auto

lemma tsynscanla_tick [simp]: "tsynScanlA f b\<cdot>(\<up>Tick \<bullet> s) = \<up>Tick \<bullet> (tsynScanlA f b\<cdot>s)"
  unfolding tsynScanlA_def
  by auto

lemma tsynscanla_msg [simp]: "tsynScanlA f b\<cdot>(\<up>(Msg m) \<bullet> s) = \<up>(Msg (fst (f b m))) \<bullet> (tsynScanlA f (snd (f b m))\<cdot>s)"
  unfolding tsynScanlA_def
  by auto

lemma tsynscanla_one [simp]: "tsynScanlA f b\<cdot>(\<up>x) = \<up>(eventApply (\<lambda>a. fst (f b a)) x)"
  apply(simp add: tsynScanlA_def)
  by (metis (mono_tags, lifting) event.exhaust event.simps(4) event.simps(5) eventApply.simps(1) eventApply.simps(2) fst_conv)

subsection \<open>tsynScanl\<close>

lemma tsynscanl_len [simp]: "#(tsynScanl f b\<cdot>s) = #s"
  unfolding tsynScanl_def
  by auto

lemma tsynscanl_bot [simp]: "tsynScanl f b\<cdot>\<bottom> = \<bottom>"
  unfolding tsynScanl_def
  by auto

lemma tsynscanl_tick [simp]: "tsynScanl f b\<cdot>(\<up>Tick \<bullet> s) = \<up>Tick \<bullet> (tsynScanl f b\<cdot>s)"
  unfolding tsynScanl_def
  using tsynscanla_tick by blast

lemma tsynscanl_msg [simp]: "tsynScanl f b\<cdot>(\<up>(Msg m) \<bullet> s) = \<up>(Msg (f b m)) \<bullet> (tsynScanl f (f b m)\<cdot>s)"
  unfolding tsynScanl_def
  by (simp)

lemma tsynscanl_one [simp]: "tsynScanl f b\<cdot>(\<up>x) = \<up>(eventApply (f b) x)"
  by(simp add: tsynScanl_def)


(* Does not hold for all f *)
lemma tsynscanl_map: "tsynScanl f b\<cdot>(\<up>(Msg m) \<bullet> xs) = \<up>(Msg (f b m)) \<bullet> tsynMap (\<lambda>x. f x m)\<cdot>(tsynScanl f b\<cdot>xs)"
  oops




section \<open>Sum\<close>

definition tsynSum :: "'a::{zero, countable,monoid_add, ab_semigroup_add, plus} event stream \<rightarrow> 'a event stream" where
"tsynSum = tsynScanl plus 0"

lemma tsynsum_bot [simp]: "tsynSum\<cdot>\<bottom> = \<bottom>"
  unfolding tsynSum_def
  by simp

lemma tsynsum_one [simp]: "tsynSum\<cdot>(\<up>x) = \<up>x"
  unfolding tsynSum_def
  apply simp
  apply(cases x)
  by auto

lemma "tsynScanl plus n\<cdot>(\<up>(Msg m) \<bullet> xs) = \<up>(Msg (n+m)) \<bullet> tsynMap (plus m)\<cdot>(tsynScanl plus n\<cdot>xs)"
  apply (induction xs arbitrary: m n rule: ind)
    apply simp
   apply simp
  apply(rename_tac a s m n)
  apply(case_tac a)
  apply auto
  oops

  subsection \<open>Testing\<close>
lemma "tsynSum\<cdot>(\<up> (Msg 0)\<infinity>) = \<up> (Msg 0)\<infinity>"
  by (metis add.right_neutral s2sinftimes sinftimes_unfold tsynSum_def tsynscanl_msg)

lemma "tsynSum\<cdot>(\<up>Tick\<infinity>) = \<up>Tick\<infinity>"
  by (metis s2sinftimes sinftimes_unfold tsynSum_def tsynscanl_tick)
  

end