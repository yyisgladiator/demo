(*  Title:        tsynStream.thy
    Author:       Sebastian Stüber, Dennis Slotboom
    E-Mail:       sebastian.stueber@rwth-aachen.de, dennis.slotboom@rwth-aachen.de

    Description:  Time-synchronous streams. Each time-interval may at most have one message.
*)

chapter {* Time-Synchronous Streams *}

theory tsynStream
imports "../untimed/Streams"

begin

(* ----------------------------------------------------------------------- *)
  section {* Time-Synchronous Type Definition *}
(* ----------------------------------------------------------------------- *)

text {* Definition of datatype @{text tsyn} that extends with a @{term Null}. *}
datatype 'm tsyn = Msg 'm ( "\<M> _" 65)| Null

text {* Introduce symbol @{text -} for empty time-slots called null. *}
syntax "@Null" :: "'a tsyn" ("-")
translations "-" == "CONST Null"

text {* Inverse of Msg.*}
abbreviation inversMsg ::  "'a tsyn \<Rightarrow> 'a"  ("\<M>\<inverse> _") where 
  "inversMsg e \<equiv> (case e of \<M> m \<Rightarrow> m)"

text {* Prove that datatype tsyn is countable. Needed, since the domain-constructor defined
 to work for countable types .*}
instance tsyn :: (countable) countable
  by countable_datatype

(* ToDo: add descriptions. *)

instantiation tsyn :: (message) message
begin
  definition ctype_tsyn :: "channel \<Rightarrow> 'a tsyn set" where 
    "ctype_tsyn c = {Null} \<union> (Msg ` (ctype c))"
  instance
    by (intro_classes)
end

lemma ctype_tsynI: assumes "a \<in> ctype c"
  shows "Msg a \<in> ctype c"
  by (simp add: assms ctype_tsyn_def)

lemma ctype_tsyn_iff: "a \<in> ctype c \<longleftrightarrow> Msg a \<in> ctype c"
  by (simp add: ctype_tsyn_def image_iff)

(* ----------------------------------------------------------------------- *)
  section {* Definitions on Time-Synchronous Streams *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynDom}: Obtain the set of all stream messages. *}
definition tsynDom :: "'a tsyn stream \<rightarrow> 'a set" where
  "tsynDom \<equiv> \<Lambda> s. {m | m. (Msg m) \<in> sdom\<cdot>s}"

text {* @{term tsynAbsElem}: Return the corresponding non tsyn element. *}
fun tsynAbsElem :: "'a tsyn \<Rightarrow> 'a" where
  "tsynAbsElem Null = undefined " |
  "tsynAbsElem (Msg a) = a"

text {* @{term tsynAbs}: Filter the nulls and return the corresponding stream. *}
definition tsynAbs:: "'a tsyn stream \<rightarrow> 'a stream" where
  "tsynAbs \<equiv> \<Lambda> s. smap tsynAbsElem\<cdot>(sfilter {e. e \<noteq> Null}\<cdot>s)"

(* ToDo: add abbreviation *)

text {* @{term tsynLen}: Return the number of messages. *}
definition tsynLen:: "'a tsyn stream \<rightarrow> lnat" where 
  "tsynLen \<equiv> \<Lambda> s. #(tsynAbs\<cdot>s)"

text {* @{term tsynApplyElem}: Apply the function direct to the message. *}
fun tsynApplyElem :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tsyn \<Rightarrow> 'b tsyn" where
  "tsynApplyElem _ Null = Null" |
  "tsynApplyElem f (Msg a) = Msg (f a)"

text {* @{term tsynMap}: Apply a function to all elements of the stream. *}
definition tsynMap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tsyn stream \<rightarrow> 'b tsyn stream" where
  "tsynMap f = smap (tsynApplyElem f)"

text {* @{term tsynFilterElem}: Replace elements not inside the set with a emtpy time-slot. *}
fun tsynFilterElem :: "('a set) \<Rightarrow> 'a tsyn \<Rightarrow> 'a tsyn" where
  "tsynFilterElem _ Null = Null" |
  "tsynFilterElem A (Msg a) = (if a \<notin> A then Null else (Msg a))"

text {* @{term tsynFilter}: Remove all elements from the stream which are not included in the given
                            set. *}
definition tsynFilter :: "'a set \<Rightarrow> 'a tsyn stream \<rightarrow> 'a tsyn stream" where
  "tsynFilter A = smap (tsynFilterElem A)"

(* ----------------------------------------------------------------------- *)
  section {* Lemmata on Time-Synchronous Streams *}
(* ----------------------------------------------------------------------- *)

text {* Induction rule for infinite time-synchronous streams and admissable predicates. *}
lemma tsyn_ind [case_names adm bot msg null]:
  assumes adm: "adm P"
    and bot: "P \<epsilon>"
    and msg: "\<And>m s. P s \<Longrightarrow> P (\<up>(Msg m) \<bullet> s)"
    and null: "\<And>s. P s \<Longrightarrow> P (\<up>Null \<bullet> s)"
  shows "P x"
  using assms 
  apply (induction rule: ind [of _ x])
  apply (simp_all add: adm bot)
  by (metis tsyn.exhaust msg null)

text {* Cases rule for time-synchronous streams. *}
lemma tsyn_cases [case_names bot msg null]:
  assumes bot: "P \<epsilon>"
    and msg: "\<And>m s. P (\<up>(Msg m) \<bullet> s)"
    and null: "\<And> s. P (\<up>Null \<bullet> s)"
  shows "P x"
  using assms
  apply (cases rule: scases [of x])
  apply (simp add: bot)
  by (metis tsyn.exhaust)

(* ----------------------------------------------------------------------- *)
  subsection {* tsynDom *}
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
lemma tsyndom_sconc_null [simp]: "tsynDom\<cdot>(\<up>Null \<bullet> s) = tsynDom\<cdot>s"
  by (metis (no_types, lifting) Collect_cong Un_insert_left tsyn.distinct(1) insert_iff sdom2un 
      sup_bot.left_neutral tsyndom_insert)

(* ----------------------------------------------------------------------- *)
  subsection {* tsynAbs *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynAbs} insertion lemma. *}
lemma tsynabs_insert: "tsynAbs\<cdot>s = smap tsynAbsElem\<cdot>(sfilter {e. e \<noteq> Null}\<cdot>s)"
  by (simp add: tsynAbs_def)

text {* @{term tsynAbs} test on infinitely many time-slots. *}
lemma tsynabs_test_infnulls: "tsynAbs\<cdot>(\<up>Null\<infinity>) = \<epsilon>"
  by (simp add: tsynabs_insert sfilter_sinftimes_nin)

text {* @{term tsynAbs} test on finite stream. *}
lemma tsynabs_test_finstream: "tsynAbs\<cdot>(<[Msg 1, Msg 2, Null, Null, Msg 1, Null]>) = <[1,2,1]>"
  by (simp add: tsynabs_insert)

text {* @{term tsynAbs} maps the empty stream on the empty stream. *}
lemma tsynabs_strict [simp]: "tsynAbs\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynabs_insert)

text {* @{term tsynAbs} distributes over concatenation. *}
lemma tsynabs_sconc_msg: "tsynAbs\<cdot>(\<up>(Msg a) \<bullet> as) = \<up>a \<bullet> (tsynAbs\<cdot>as)"
  by (simp add: tsynabs_insert)

text {* @{term tsynAbs} ignores empty time-slots. *}
lemma tsynabs_sconc_null: "tsynAbs\<cdot>(\<up>Null \<bullet> s) = tsynAbs\<cdot>s"
  by (simp add: tsynabs_insert)

text {* @{term tsynAbs} of the concatenation of two streams equals the concatenation of 
        @{term tsynAbs} of both streams. *}
lemma tsynabs_sconc: assumes "#as < \<infinity>" shows "tsynAbs\<cdot>(as \<bullet> bs) = tsynAbs\<cdot>as \<bullet> tsynAbs\<cdot>bs"
  by (simp add: add_sfilter2 assms smap_split tsynabs_insert)

text {* Length of @{term tsynAbs} is smaller or equal to the length of the original stream.  *}
lemma tsynabs_slen: "#(tsynAbs\<cdot>s) \<le> #s"
  by (simp add: slen_sfilterl1 tsynabs_insert)

(* ----------------------------------------------------------------------- *)
  subsection {* tsynFilter *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynFilter} test on infinitely many time-slots. *}
lemma tsynFilter_test_infnulls: "(tsynFilter A)\<cdot>(\<up>Null\<infinity>) = \<up>Null\<infinity>"
  by (simp add: tsynFilter_def)

text {* @{term tsynFilter} test on finite nat tsyn-stream. *}
lemma tsynFilter_test_finstream: "(tsynFilter {(1::nat),2})\<cdot>(<[Msg 1, Msg 2, Null, Msg 3, Null, Msg 1, Null, Msg 4]>) =<[Msg 1, Msg 2, Null, Null, Null, Msg 1, Null, Null]>"
  by (simp add: tsynFilter_def)

text {* @{term tsynFilter} maps the empty stream on the empty stream. *}
lemma tsynFilter_strict [simp]: "(tsynFilter A)\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynFilter_def)

text {* @{term tsynFilter} distributes over concatenation, having the first Stream consist of one Msg-element. *}
lemma tsynFilter_sconc_Msg: "(tsynFilter A)\<cdot>(\<up>(Msg m) \<bullet> as) =  \<up>(if m \<notin> A then Null else (Msg m)) \<bullet> (tsynFilter A)\<cdot>as"
  by (simp add: tsynFilter_def)

text {* @{term tsynFilter} distributes over concatenation, having the first Stream consist of one Null-element. *}
lemma tsynFilter_sconc_Null: "(tsynFilter A)\<cdot>(\<up>(Null)\<bullet> as) =  \<up>(Null) \<bullet> (tsynFilter A)\<cdot>as"
  by (simp add: tsynFilter_def)

text {*@{term tsynFilter} of the concatenation of two streams equals the concatenation of 
        @{term tsynFilter} of both streams. *}
lemma tsynFilter_sconc: assumes "#a1 < \<infinity>" shows "(tsynFilter A)\<cdot>(a1 \<bullet> a2) =  (tsynFilter A)\<cdot>a1 \<bullet> (tsynFilter A)\<cdot>a2"
  by (simp add: assms smap_split tsynFilter_def)
  
text {* Length of @{term tsynFilter} is equal to the length of the original stream. *}
lemma tsynFilter_slen: "#((tsynFilter A)\<cdot>s) = #s"
  by (simp add: tsynFilter_def)

(* ----------------------------------------------------------------------- *)
  subsection {* tsynMap *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynMap} insertion lemma. *}
lemma tsynmap_insert: "tsynMap f\<cdot>s = smap (tsynApplyElem f)\<cdot>s"
  by (simp add: tsynMap_def)

text {* @{term tsynMap} is strict. *}
lemma tsynmap_strict [simp]: "tsynMap f\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynmap_insert)

text {* @{term tsynMap} distributes over concatenation. *}
lemma tsynmap_sconc_msg: "tsynMap f\<cdot>(\<up>(Msg m) \<bullet> s) = \<up>(Msg (f m)) \<bullet> tsynMap f\<cdot>s"
  by (simp add: tsynmap_insert)

text {* @{term tsynMap} ignores empty time-slots. *}
lemma tsynmap_sconc_null: "tsynMap f\<cdot>(\<up>Null \<bullet> s) = \<up>Null \<bullet> tsynMap f\<cdot>s"
  by (simp add: tsynmap_insert)

text {* @{term tsynMap} leaves the length of a stream unchanged. *}
lemma tsynmap_slen [simp]: "#(tsynMap f\<cdot>s) = #s"
  by (simp add: tsynmap_insert)



(* ToDo: adjustments. *)

(* Behaves like sscanlA, but on time-syncronus streams *)
(* Ignore all nulls, do not modify the state and output null *)
definition tsynScanlA :: "('s \<Rightarrow>'a \<Rightarrow> ('b \<times>'s)) \<Rightarrow> 's  \<Rightarrow> 'a tsyn stream \<rightarrow> 'b tsyn stream" where
"tsynScanlA f = sscanlA (\<lambda> s a. case a of (Msg m) \<Rightarrow> (Msg (fst (f s m)), (snd (f s m))) | Null \<Rightarrow> (Null, s))"

(* Behaves like sscanlA, but on time-syncronus streams *)
(* Ignore all nulls, do not modify the state and output null *)
definition tsynScanl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b  \<Rightarrow> 'a tsyn stream \<rightarrow> 'b tsyn stream" where
"tsynScanl f b0 = tsynScanlA (\<lambda>b a. (f b a,f b a)) b0 "









subsection \<open>tsynScanlA\<close>

lemma tsynscanla_len [simp]: "#(tsynScanlA f b\<cdot>s) = #s"
  unfolding tsynScanlA_def
  using sscanla_len by blast

lemma tsynscanla_bot [simp]: "tsynScanlA f b\<cdot>\<bottom> = \<bottom>"
  unfolding tsynScanlA_def
  by auto

lemma tsynscanla_null [simp]: "tsynScanlA f b\<cdot>(\<up>Null \<bullet> s) = \<up>Null \<bullet> (tsynScanlA f b\<cdot>s)"
  unfolding tsynScanlA_def
  by auto

lemma tsynscanla_msg [simp]: "tsynScanlA f b\<cdot>(\<up>(Msg m) \<bullet> s) = \<up>(Msg (fst (f b m))) \<bullet> (tsynScanlA f (snd (f b m))\<cdot>s)"
  unfolding tsynScanlA_def
  by auto

lemma tsynscanla_one [simp]: "tsynScanlA f b\<cdot>(\<up>x) = \<up>(tsynApplyElem (\<lambda>a. fst (f b a)) x)"
  apply(simp add: tsynScanlA_def)
  by (metis (mono_tags, lifting) tsyn.exhaust tsyn.simps(4) tsyn.simps(5) tsynApplyElem.simps(1) tsynApplyElem.simps(2) fst_conv)

subsection \<open>tsynScanl\<close>

lemma tsynscanl_len [simp]: "#(tsynScanl f b\<cdot>s) = #s"
  unfolding tsynScanl_def
  by auto

lemma tsynscanl_bot [simp]: "tsynScanl f b\<cdot>\<bottom> = \<bottom>"
  unfolding tsynScanl_def
  by auto

lemma tsynscanl_null [simp]: "tsynScanl f b\<cdot>(\<up>Null \<bullet> s) = \<up>Null \<bullet> (tsynScanl f b\<cdot>s)"
  unfolding tsynScanl_def
  using tsynscanla_null by blast

lemma tsynscanl_msg [simp]: "tsynScanl f b\<cdot>(\<up>(Msg m) \<bullet> s) = \<up>(Msg (f b m)) \<bullet> (tsynScanl f (f b m)\<cdot>s)"
  unfolding tsynScanl_def
  by (simp)

lemma tsynscanl_one [simp]: "tsynScanl f b\<cdot>(\<up>x) = \<up>(tsynApplyElem (f b) x)"
  by(simp add: tsynScanl_def)


(* Does not hold for all f *)
lemma tsynscanl_map: "tsynScanl f b\<cdot>(\<up>(Msg m) \<bullet> xs) = \<up>(Msg (f b m)) \<bullet> tsynMap (\<lambda>x. f x m)\<cdot>(tsynScanl f b\<cdot>xs)"
  oops




section \<open>Sum\<close>

definition tsynSum :: "'a::{zero, countable,monoid_add, ab_semigroup_add, plus} tsyn stream \<rightarrow> 'a tsyn stream" where
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

lemma "tsynSum\<cdot>(\<up>Null\<infinity>) = \<up>Null\<infinity>"
  by (metis s2sinftimes sinftimes_unfold tsynSum_def tsynscanl_null)

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
  apply (smt Un_insert_left tsyn.simps(1) insert_iff mem_Collect_eq odd_add sdom2un subset_iff 
         sup_bot.left_neutral tsyndom_insert)
  by simp

lemma tsynsum_even: assumes "tsynDom\<cdot>ts \<subseteq> {n. even n}"
  shows "tsynDom\<cdot>(tsynSum\<cdot>ts) \<subseteq> {n. even n}"
  by (simp add: assms tsynSum_def tsynsum_even_h)

end