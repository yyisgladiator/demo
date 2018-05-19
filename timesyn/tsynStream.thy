(*  Title:        tsynStream.thy
    Author:       Sebastian Stüber, Dennis Slotboom
    E-Mail:       sebastian.stueber@rwth-aachen.de, dennis.slotboom@rwth-aachen.de

    Description:  Time-synchronous streams. Each time-interval may at most have one message.
*)

chapter {* Time-Synchronous Streams *}

theory tsynStream
imports "../untimed/Streams" "../inc/Event"

begin

(* ----------------------------------------------------------------------- *)
  section {* Definitions on Time-Synchronous Streams *}
(* ----------------------------------------------------------------------- *)

text {* Introduce symbol @{text -} for empty time-slots called tick. *}
syntax "@Tick" :: "'a event" ("-")
translations "-" == "CONST Tick"

text {* @{term eventApply}: Apply the function direct to the message. *}
fun eventApply :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a event \<Rightarrow> 'b event" where
  "eventApply _ Tick = Tick" |
  "eventApply f (Msg a) = Msg (f a)"

text {* @{term tsynDom}: Obtain the set of all stream messages. *}
definition tsynDom :: "'a event stream \<rightarrow> 'a set" where
  "tsynDom \<equiv> \<Lambda> s. {m | m. (Msg m) \<in> sdom\<cdot>s}"

text {* @{term tsynMap}: Apply a function to all elements of the stream. *}
definition tsynMap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a event stream \<rightarrow> 'b event stream" where
  "tsynMap f = smap (eventApply f)"

(* ----------------------------------------------------------------------- *)
  section {* Lemmata on Time-Synchronous Streams *}
(* ----------------------------------------------------------------------- *)

text {* Induction rule for infinite time-synchronous streams and admissable predicates. *}
lemma tsyn_ind [case_names adm bot msg tick]:
  assumes adm: "adm P"
    and bot: "P \<epsilon>"
    and msg: "\<And>m s. P s \<Longrightarrow> P (\<up>(Msg m) \<bullet> s)"
    and tick: "\<And>s. P s \<Longrightarrow> P (\<up>Tick \<bullet> s)"
  shows "P x"
  using assms 
  apply (induction rule: ind [of _ x])
  apply (simp_all add: adm bot)
  by (metis event.exhaust msg tick)

text {* Cases rule for time-synchronous streams. *}
lemma tsyn_cases [case_names bot msg tick]:
  assumes bot: "P \<epsilon>"
    and msg: "\<And>m s. P (\<up>(Msg m) \<bullet> s)"
    and tick: "\<And> s. P (\<up>Tick \<bullet> s)"
  shows "P x"
  using assms
  apply (cases rule: scases [of x])
  apply (simp add: bot)
  by (metis event.exhaust)

(* ----------------------------------------------------------------------- *)
  section {* tsynDom *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynDom} is a monotonous function. *}
lemma tsyndom_monofun [simp]: "monofun (\<lambda>s. {m | m. (Msg m) \<in> sdom\<cdot>s})"
  apply (rule monofunI)
  apply (simp add: set_cpo_simps(1))
  by (meson Collect_mono sdom_prefix subsetCE)

text {* @{term tsynDom} is a continous function. *}
lemma tsyndom_cont [simp]: "cont (\<lambda>s. {m | m. (Msg m) \<in> sdom\<cdot>s})"
  apply (rule contI2)
  apply (simp only: tsyndom_monofun)
  apply (rule)+
  apply (simp add: set_cpo_simps(1))
  apply (rule subsetI)
  by (simp add: image_iff lub_eq_Union sdom_cont2)

text {* @{term tsynDom} insertion lemma. *}
lemma tsyndom_insert: "tsynDom\<cdot>s = {m | m. (Msg m) \<in> sdom\<cdot>s}"
  by (metis (no_types) Abs_cfun_inverse2 tsynDom_def tsyndom_cont)

text {* If the domain of a stream is subset of another set it is also after removing the first 
        element. *}
lemma tsyndom_sconc_msg_sub: "tsynDom\<cdot>(\<up>(Msg x) \<bullet> xs) \<subseteq> S \<Longrightarrow> tsynDom\<cdot>xs \<subseteq> S"
  by (simp add: subset_eq tsyndom_insert)

text {* If the domain of a stream is subset of another set and it will be concatenated one element 
        of this superset as first element to the stream it is also is a subset. *}
lemma tsyndom_sconc_msg_sub2 [simp]: "tsynDom\<cdot>xs \<subseteq> S \<Longrightarrow> x \<in> S \<Longrightarrow> tsynDom\<cdot>(\<up>(Msg x) \<bullet> xs) \<subseteq> S"
  by (simp add: subset_iff tsyndom_insert)

text {* The empty time-slot is not part of the domain. *}
lemma tsyndom_sconc_tick [simp]: "tsynDom\<cdot>(\<up>Tick \<bullet> s) = tsynDom\<cdot>s"
  by (metis (no_types, lifting) Collect_cong Un_insert_left event.distinct(1) insert_iff sdom2un 
      sup_bot.left_neutral tsyndom_insert)




(* ToDo: adjustments *)

(* Behaves like sscanlA, but on time-syncronus streams *)
(* Ignore all ticks, do not modify the state and output tick *)
definition tsynScanlA :: "('s \<Rightarrow>'a \<Rightarrow> ('b \<times>'s)) \<Rightarrow> 's  \<Rightarrow> 'a event stream \<rightarrow> 'b event stream" where
"tsynScanlA f = sscanlA (\<lambda> s a. case a of (Msg m) \<Rightarrow> (Msg (fst (f s m)), (snd (f s m))) | Tick \<Rightarrow> (Tick, s))"

(* Behaves like sscanlA, but on time-syncronus streams *)
(* Ignore all ticks, do not modify the state and output tick *)
definition tsynScanl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b  \<Rightarrow> 'a event stream \<rightarrow> 'b event stream" where
"tsynScanl f b0 = tsynScanlA (\<lambda>b a. (f b a,f b a)) b0 "





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

lemma tsynsum_even_h: assumes "tsynDom\<cdot>ts \<subseteq> {n. even n}"
      and "even m"
  shows "tsynDom\<cdot>(tsynScanl plus m\<cdot>ts) \<subseteq> {n. even n}"
  using assms apply(induction arbitrary: m rule: tsyn_ind [of _ ts])
     apply(rule adm_imp)
      apply simp
  apply(simp add: adm_def)
     apply auto[1]
  apply (smt Collect_mem_eq Collect_mono_iff ch2ch_Rep_cfunR contlub_cfun_arg subset_cont)
    apply simp
  apply simp
  apply (smt Un_insert_left event.simps(1) insert_iff mem_Collect_eq odd_add sdom2un subset_iff 
         sup_bot.left_neutral tsyndom_insert)
  by simp

lemma tsynsum_even: assumes "tsynDom\<cdot>ts \<subseteq> {n. even n}"
  shows "tsynDom\<cdot>(tsynSum\<cdot>ts) \<subseteq> {n. even n}"
  by (simp add: assms tsynSum_def tsynsum_even_h)

end