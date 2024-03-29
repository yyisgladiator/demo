(*  Title:        tsynStream.thy
    Author:       Sebastian Stüber, Dennis Slotboom
    E-Mail:       sebastian.stueber@rwth-aachen.de, dennis.slotboom@rwth-aachen.de

    Description:  Time-synchronous streams. Each time-interval may at most have one message.
*)

chapter \<open>Time-Synchronous Streams\<close>

theory tsynStream
imports Streams

begin

(* ----------------------------------------------------------------------- *)
  section \<open>Time-Synchronous Type Definition\<close>
(* ----------------------------------------------------------------------- *)

text \<open>Definition of datatype \<open>tsyn\<close> that extends with a @{term eps}.\<close>
datatype 'm tsyn = Msg 'm ( "\<M> _" 65)| eps

text \<open>Introduce symbol \<open>~\<close> for empty time-slots called eps.\<close>
syntax "@eps" :: "'a tsyn" ("~")
translations "~" == "CONST eps"

text \<open>Inverse of Msg.\<close>
fun inverseMsg :: "'a tsyn \<Rightarrow> 'a" where
  "inverseMsg eps = undefined" |
  "inverseMsg (Msg m) = m"

abbreviation invMsg :: "'a tsyn \<Rightarrow> 'a"  ("\<M>\<inverse> _") where 
  "invMsg \<equiv> inverseMsg"

text \<open>Prove that datatype tsyn is countable. Needed, since the domain-constructor defined
        to work for countable types.\<close>
instance tsyn :: (countable) countable
  by countable_datatype

text \<open>Instantiation of tsyn message.\<close>
instantiation tsyn :: (message) message
begin
  definition ctype_tsyn :: "channel \<Rightarrow> 'a tsyn set" where 
    "ctype_tsyn c = {eps} \<union> (Msg ` (ctype c))"
  instance
    by (intro_classes)
end

text \<open>If element a is of type ctype c, then Msg a is also of type ctype c.\<close>
lemma ctype_tsynI: assumes "a \<in> ctype c"
  shows "Msg a \<in> ctype c"
  by (simp add: assms ctype_tsyn_def)

text \<open>The reverse also holds.\<close>
lemma ctype_tsyn_iff: "a \<in> ctype c \<longleftrightarrow> Msg a \<in> ctype c"
  by (simp add: ctype_tsyn_def image_iff)

(* ----------------------------------------------------------------------- *)
  section \<open>Definitions on Time-Synchronous Streams\<close>
(* ----------------------------------------------------------------------- *)

text \<open>@{term tsynDom}: Obtain the set of all stream messages.\<close>
definition tsynDom :: "'a tsyn stream \<rightarrow> 'a set" where
  "tsynDom \<equiv> \<Lambda> s. {m | m. (Msg m) \<in> sdom\<cdot>s}"

text \<open>@{term tsynAbsElem}: Return the corresponding non tsyn element.\<close>
fun tsynAbsElem :: "'a tsyn \<Rightarrow> 'a" where
  "tsynAbsElem eps = undefined " |
  "tsynAbsElem (Msg a) = a"

text \<open>@{term tsynAbs}: Filter the epss and return the corresponding stream.\<close>
definition tsynAbs:: "'a tsyn stream \<rightarrow> 'a stream" where
  "tsynAbs \<equiv> \<Lambda> s. smap tsynAbsElem\<cdot>(sfilter {e. e \<noteq> eps}\<cdot>s)"

text \<open>@{term tsynEps}: Return the number of epss of in a stream.\<close>
definition tsynEps::"'a::countable tsyn stream \<rightarrow> lnat"where
  "tsynEps \<equiv> \<Lambda> ts. #(sfilter {~}\<cdot>ts)"

text \<open>@{term tsynLen}: Return the number of messages.\<close>
definition tsynLen:: "'a tsyn stream \<rightarrow> lnat" where 
  "tsynLen \<equiv> \<Lambda> s. #(tsynAbs\<cdot>s)"

text \<open>Abbrevation of tsynLen.\<close>
abbreviation tsynLen_abbr :: "'a tsyn stream \<Rightarrow> lnat" ("#\<^sub>-_" [1000] 999) where
  "#\<^sub>-s == tsynLen\<cdot>s"

text \<open>@{term tsynApplyElem}: Apply the function direct to the message.\<close>
fun tsynApplyElem :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tsyn \<Rightarrow> 'b tsyn" where
  "tsynApplyElem _ ~ = ~" |
  "tsynApplyElem f (Msg a) = Msg (f a)"

text \<open>@{term tsynMap}: Apply a function to all elements of the stream.\<close>
definition tsynMap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tsyn stream \<rightarrow> 'b tsyn stream" where
  "tsynMap f = smap (tsynApplyElem f)"

text\<open>@{term tsynFst}: Access the first element of a pair.\<close>
fun tsynFst :: "('a \<times> 'b) tsyn \<Rightarrow> 'a tsyn" where
  "tsynFst eps = eps" |
  "tsynFst (Msg x) = Msg (fst x)"

text\<open>@{term tsynSnd}: Access the second element of a pair .\<close>
fun tsynSnd :: "('a \<times> 'b) tsyn \<Rightarrow> 'b tsyn" where
  "tsynSnd eps = eps" |
  "tsynSnd (Msg x) = Msg (snd x)"

text\<open>@{term tsynProjFst}: Access the first stream of two zipped streams .\<close>
definition tsynProjFst :: "('a \<times> 'b) tsyn stream \<rightarrow> 'a tsyn stream" where
"tsynProjFst = smap tsynFst"

text\<open>@{term tsynProjSnd}: Access the second stream of two zipped streams.\<close>
definition tsynProjSnd :: "('a \<times> 'b) tsyn stream \<rightarrow> 'b tsyn stream" where
"tsynProjSnd = smap tsynSnd"

text \<open>@{term tsynFilterElem}: Replace elements not inside the set with a emtpy time-slot.\<close>
fun tsynFilterElem :: "('a set) \<Rightarrow> 'a tsyn \<Rightarrow> 'a tsyn" where
  "tsynFilterElem _ eps = eps" |
  "tsynFilterElem A (Msg a) = (if a \<notin> A then eps else (Msg a))"

text \<open>@{term tsynFilter}: Remove all elements from the stream which are not included in the given
        set.\<close>
definition tsynFilter :: "'a set \<Rightarrow> 'a tsyn stream \<rightarrow> 'a tsyn stream" where
  "tsynFilter A = smap (tsynFilterElem A)"

text \<open>Abbrevation of tsynFilter.\<close>
abbreviation tsynFilter_abbr :: "'a set \<Rightarrow> 'a tsyn stream \<Rightarrow> 'a tsyn stream" 
  ("(_ \<ominus>\<^sub>- _)" [66, 65] 65) where "F \<ominus>\<^sub>- s \<equiv> tsynFilter F\<cdot>s"

text \<open>Auxiliary function for @{term tsynRemDups}.\<close>
fun tsynRemDups_h :: "'a tsyn \<Rightarrow> 'a tsyn \<Rightarrow> ('a tsyn \<times> 'a tsyn)" where
  "tsynRemDups_h x eps = (eps, x)" |
  "tsynRemDups_h x y = (if x = y then (eps, x) else (y, y))"

text \<open>@{term tsynRemDups}: Remove all duplicates from the stream.\<close>
definition tsynRemDups :: "'a tsyn stream \<rightarrow> 'a tsyn stream" where 
  "tsynRemDups = sscanlA tsynRemDups_h eps"

text \<open>Auxiliary function for @{term tsynScanlExt}.\<close>
fun tsynScanlExt_h :: "('s \<Rightarrow> 'a \<Rightarrow> ('b \<times>'s)) \<Rightarrow> 's \<Rightarrow> 'a tsyn \<Rightarrow> ('b tsyn \<times> 's)" where
  "tsynScanlExt_h f s (Msg m) = (Msg (fst (f s m)), (snd (f s m)))" |
  "tsynScanlExt_h f s eps = (eps, s)"

text \<open>@{term tsynScanlExt}: Apply a function elementwise to the input stream. Behaves like 
        @{term tsynMap}, but also takes a state as additional input to the function. For the first 
        computation an initial state is provided.\<close>
(* tsynScanlExt just ignores empty time-slots; If you want to return empty time-slots lift a
   function from sscanlA. *)
definition tsynScanlExt :: "('s \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's)) \<Rightarrow> 's \<Rightarrow> 'a tsyn stream \<rightarrow> 'b tsyn stream" where
  "tsynScanlExt f = sscanlA (tsynScanlExt_h f)"

text \<open>@{term tsynScanl}: Apply a function elementwise to the input stream. Behaves like 
  @{term tsynMap}, but also takes the previously generated output element as additional input to 
  the function. For the first computation an initial value is provided.\<close>
definition tsynScanl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a tsyn stream \<rightarrow> 'b tsyn stream" where
  "tsynScanl f i = tsynScanlExt (\<lambda>a b. (f a b, f a b)) i"

text \<open>Auxiliary function for @{term tsynDropWhile}.\<close>
fun tsynDropWhile_h :: "('a \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> 'a tsyn \<Rightarrow> ('a tsyn \<times> bool)" where
  "tsynDropWhile_h f x eps = (eps, x)"|
  "tsynDropWhile_h f True (Msg x) = (if f x then (eps, True) else ((Msg x), False))" |
  "tsynDropWhile_h f False (Msg x) = ((Msg x), False)"

text \<open>@{term tsynDropWhile}: Check each element of the stream and remove elements satisfying f.\<close>
definition tsynDropWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a tsyn stream \<rightarrow> 'a tsyn stream" where
  "tsynDropWhile f =  sscanlA (tsynDropWhile_h f) True"

text \<open>@{term tsynZip}: Merge a tysn stream with a stream.\<close>
fixrec tsynZip :: "'a tsyn stream \<rightarrow> 'b stream \<rightarrow> ('a \<times> 'b) tsyn stream" where
  "tsynZip\<cdot>\<epsilon>\<cdot>s = \<epsilon>" |
  "tsynZip\<cdot>s\<cdot>\<epsilon> = \<epsilon>" |
  "tsynZip\<cdot>(up\<cdot>a && as)\<cdot>(up\<cdot>b && bs) = (
     if (undiscr a) = eps then \<up>eps \<bullet> tsynZip\<cdot>as\<cdot>(up\<cdot>b && bs)
     else \<up>(Msg ((invMsg (undiscr a)), (undiscr b))) \<bullet> tsynZip\<cdot>as\<cdot>bs 
  )" 

(* ----------------------------------------------------------------------- *)
  section \<open>Fixrec-Definitions on Time-Synchronous Streams\<close>
(* ----------------------------------------------------------------------- *)

(* Fixrec-Example *)

text \<open>Auxiliary function for @{term tsynRemDups_fix}.\<close>
fixrec tsynRemDups_fix_h :: "'a tsyn stream \<rightarrow> 'a tsyn discr option \<rightarrow> 'a tsyn stream" where
  "tsynRemDups_fix_h\<cdot>\<epsilon>\<cdot>option = \<epsilon>" |
  "tsynRemDups_fix_h\<cdot>(up\<cdot>a && as)\<cdot>None = (
     if (undiscr a) = eps then up\<cdot>a && tsynRemDups_fix_h\<cdot>as\<cdot>None
     else up\<cdot>a && tsynRemDups_fix_h\<cdot>as\<cdot>(Some a)
  )" |
  "tsynRemDups_fix_h\<cdot>(up\<cdot>a && as)\<cdot>(Some b) = (
     if (undiscr a) = eps then up\<cdot>a && tsynRemDups_fix_h\<cdot>as\<cdot>(Some b)
     else (if a = b then up\<cdot>(Discr eps) && tsynRemDups_fix_h\<cdot>as\<cdot>(Some b)
     else up\<cdot>a && tsynRemDups_fix_h\<cdot>as\<cdot>(Some a))
  )"

text \<open>@{term tsynRemDups_fix}: Fixrec definition of @{term tsynRemDups}.\<close>
definition tsynRemDups_fix :: "'a tsyn stream \<rightarrow> 'a tsyn stream" where
  "tsynRemDups_fix \<equiv> \<Lambda> s. tsynRemDups_fix_h\<cdot>s\<cdot>None"

(* ----------------------------------------------------------------------- *)
  subsection \<open>Lemmata on Streams - Streams Extension\<close>
(* ----------------------------------------------------------------------- *)

(* ToDo: add descriptions and move to Streams. *)

lemma len_one_stream: "#s = Fin 1 \<Longrightarrow> \<exists>m. s = \<up>m"
  proof -
    assume a0: "#s = Fin 1"
    show "\<exists>m::'a. s = \<up>m"
      proof -
        have empty_or_long: "\<nexists>m::'a. s = \<up>m \<Longrightarrow> s = \<epsilon> \<or> (\<exists> as a. s = \<up>a \<bullet> as)"
          by (metis surj_scons)
        have not_eq_one: "\<nexists>m::'a. s = \<up>m \<Longrightarrow> #s = Fin 0 \<or> #s > Fin 1" 
          using empty_or_long 
          by (metis Fin_02bot Fin_Suc One_nat_def a0 leI lnzero_def notinfI3 only_empty_has_length_0 
              sconc_snd_empty slen_conc slen_scons)
        have not_eq_one2: "\<exists>m. s = \<up>m" using a0 
          using not_eq_one by auto
        show ?thesis 
          using not_eq_one2 by simp
      qed
  qed

text \<open>Cardinality of the set @{term sdom} is smaller or equal to the length of the original 
        stream.\<close>
lemma sdom_slen: assumes "#s = Fin k" shows "card (sdom\<cdot>s) \<le> k"
  proof -
    have sdom_def_assm: "sdom\<cdot>s = {snth n s | n :: nat. n < k}" 
      by (simp add: assms sdom_def2)
    then have "{snth n s | n :: nat. n < k} \<subseteq> (\<lambda> n. snth n s) ` {i :: nat. i < k}" 
      by blast
    then have "card {snth n s | n :: nat. n < k} \<le> card {i :: nat. i < k}" 
      using surj_card_le by blast
    then show ?thesis 
      by (simp add: sdom_def_assm)
  qed

text \<open>@{term sprojsnd} of @{term szip} equals the second stream if its length is less or equal
        the length of the first stream.\<close>
lemma szip_sprojsnd:
  assumes "#ys \<le> #xs"
  shows "sprojsnd\<cdot>(szip\<cdot>xs\<cdot>ys) = ys"
  using assms
  apply (induction ys arbitrary: xs rule: ind, simp_all)
  apply (rule adm_all, rule adm_imp, simp_all)
  apply (rule admI)
  apply (metis dual_order.antisym inf_chainl4 inf_ub l42)
  apply (rename_tac a as bs)
  by (rule_tac x = bs in scases, simp_all)

text \<open>@{term sdom} of @{term szip} is subset of the Cartesian product of the sets of values of
        the zipped streams.\<close>
lemma szip_sdom: "sdom\<cdot>(szip\<cdot>as\<cdot>bs) \<subseteq> (sdom\<cdot>as \<times> sdom\<cdot>bs)"
  apply (induction as arbitrary: bs rule: ind, simp_all)
  apply (rule adm_all, rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_eq_Union, blast)
  apply (rename_tac a s bs)
  by (rule_tac x = bs in scases, simp_all,  blast)

text \<open>Each element of @{term sdom} of @{term sscanl} is in the range of f\<close>
lemma sscanl_sdom: "sdom\<cdot>(sscanl f i\<cdot>s) \<subseteq> {f i s | i s. True}"
  apply (induction s rule: ind, simp_all)
  apply (rule admI)
  apply (metis (no_types, lifting) ch2ch_Rep_cfunR contlub_cfun_arg l44)
  apply (rename_tac a s)
  apply (rule conjI)
  apply auto
  apply (simp add: sdom_def2)
  apply (erule exE)
  apply (rename_tac n)
  apply (case_tac "n > 0")
  apply (rule_tac x = "snth (n - 1) (sscanl f (f i a)\<cdot>s)" in exI)
  apply (rule_tac x = "snth n s" in exI)
  apply (metis (no_types, lifting) Suc_pred' sscanl_snth)
  apply (rule_tac x = "f i a" in exI)
  apply (rule_tac x = "shd s" in exI)
  by (metis empty_is_shortest gr0I snth_shd sscanl_shd)

text \<open>Each element of @{term sdom} of @{term sscanlA} is in the range of @{term fst} of f\<close>
lemma sscanla_sdom: "sdom\<cdot>(sscanlA f i\<cdot>s) \<subseteq> { fst(f i a) | i a. True }"
  apply (induction s rule: ind, simp_all)
  apply (rule admI)
  apply (metis (no_types, lifting) ch2ch_Rep_cfunR contlub_cfun_arg l44)
  apply (rule conjI, fastforce)
  apply (rule subsetI)
  apply (simp add: sdom_def2 sscanlA_def sprojfst_def)
  apply (erule exE)
  apply (rename_tac n)
  apply (case_tac "n > 0")
  apply (simp add: smap_sdom smap_snth_lemma gr0_conv_Suc)
  apply (erule exE)
  apply (rename_tac a s x n m)
  apply (rule_tac x = "snd (snth m (sscanl (\<lambda>(u::'a, y::'c). f y) (undefined, snd (f i a))\<cdot>s))" 
         in exI)
  apply (rule_tac x = "snth (Suc m) s" in exI)
  apply (simp add: case_prod_beta' sscanl_snth)
  by (simp, metis (no_types, lifting) case_prod_conv fair_sscanl lnsuc_neq_0 shd1 slen_empty_eq 
      smap_hd_rst sscanl_shd)

lemma sdropwhile_sdom: "sdom\<cdot>(sdropwhile f\<cdot>s) \<subseteq> sdom\<cdot>s"
  apply (induction s rule: ind, simp_all)
  apply (rename_tac a s)
  apply (case_tac "f a")
  by (rule subset_insertI2, simp_all)

text\<open>@{term smap} is injective if the mapped function is injective.\<close>
lemma smap_inj: 
  assumes "inj f"
  shows "inj (Rep_cfun (smap f))"
  apply (rule injI, rule snths_eq)
  apply (metis slen_smap)
  by (metis assms inj_eq slen_smap smap_snth_lemma)

(* ----------------------------------------------------------------------- *)
  section \<open>Lemmata on Time-Synchronous Streams\<close>
(* ----------------------------------------------------------------------- *)

text \<open>Induction rule for finite time-synchronous streams.\<close>
lemma tsyn_finind [case_names fin bot msg eps]:
  assumes fin: "#x < \<infinity>"
    and bot: "P \<epsilon>"
    and msg: "\<And>m s. P s \<Longrightarrow> P (\<up>(Msg m) \<bullet> s)"
    and eps: "\<And>s. P s \<Longrightarrow> P (\<up>eps \<bullet> s)"
  shows "P x"
  using assms
  proof (induction x rule: ind)
    case 1
    then show ?case 
      by simp
  next
    case 2
    then show ?case 
      by simp
  next
    case (3 a s)
    then show ?case 
      by (metis fold_inf inf_ub less_le slen_scons tsyn.exhaust)
  qed

text \<open>Induction rule for infinite time-synchronous streams and admissable predicates.\<close>
lemma tsyn_ind [case_names adm bot msg eps]:
  assumes adm: "adm P"
    and bot: "P \<epsilon>"
    and msg: "\<And>m s. P s \<Longrightarrow> P (\<up>(Msg m) \<bullet> s)"
    and eps: "\<And>s. P s \<Longrightarrow> P (\<up>eps \<bullet> s)"
  shows "P x"
  using assms 
  apply (induction rule: ind [of _ x])
  apply (simp_all add: adm bot)
  by (metis tsyn.exhaust msg eps)

text \<open>Cases rule for time-synchronous streams.\<close>
lemma tsyn_cases [case_names bot msg eps]:
  assumes bot: "x = \<epsilon> \<Longrightarrow> P \<epsilon>"
    and msg: "\<And>m s. x = \<up>(Msg m) \<bullet> s \<Longrightarrow> P x"
    and eps: "\<And> s. x = \<up>eps \<bullet> s \<Longrightarrow> P x"
  shows "P x"
  using assms
  apply (cases rule: scases [of x])
  apply (simp add: bot)
  by (metis tsyn.exhaust)

(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynDom\<close>
(* ----------------------------------------------------------------------- *)

text \<open>@{term tsynDom} is a monotonous function.\<close>
lemma tsyndom_monofun [simp]: "monofun (\<lambda>s. {m | m. (Msg m) \<in> sdom\<cdot>s})"
  apply (rule monofunI)
  apply (simp add: set_cpo_simps(1))
  by (meson Collect_mono sdom_prefix subsetCE)

text \<open>@{term tsynDom} is a continous function.\<close>
lemma tsyndom_cont [simp]: "cont (\<lambda>s. {m | m. (Msg m) \<in> sdom\<cdot>s})"
  apply (rule contI2)
  apply (simp only: tsyndom_monofun)
  apply (rule)+
  apply (simp add: set_cpo_simps(1))
  apply (rule subsetI)
  by (simp add: image_iff lub_eq_Union sdom_cont2)

text \<open>@{term tsynDom} insertion lemma.\<close>
lemma tsyndom_insert: "tsynDom\<cdot>s = {m | m. (Msg m) \<in> sdom\<cdot>s}"
  by (metis (no_types) Abs_cfun_inverse2 tsynDom_def tsyndom_cont)

text \<open>@{term tsynDom} maps the empty stream on the empty set.\<close>
lemma tsyndom_strict [simp]: "tsynDom\<cdot>\<epsilon> = {}"
  by (simp add: tsyndom_insert)

text \<open>If the domain of a stream is subset of another set it is also after removing the first 
        element.\<close>
lemma tsyndom_sconc_msg_sub: "tsynDom\<cdot>(\<up>(Msg x) \<bullet> xs) \<subseteq> S \<Longrightarrow> tsynDom\<cdot>xs \<subseteq> S"
  by (simp add: subset_eq tsyndom_insert)

text \<open>If the domain of a stream is subset of another set and one takes an arbitrary element 
        of this superset, then the domain of the stream with this chosen element as first
        element is also a subset of the former superset.\<close>
lemma tsyndom_sconc_msg_sub2: "tsynDom\<cdot>xs \<subseteq> S \<Longrightarrow> x \<in> S \<Longrightarrow> tsynDom\<cdot>(\<up>(Msg x) \<bullet> xs) \<subseteq> S"
  by (simp add: subset_iff tsyndom_insert)

text \<open>@{term tsynDom} of concatenations distributes via union of sets.\<close>
lemma tsyndom_sconc_msg: "tsynDom\<cdot>(\<up>(Msg a) \<bullet> as) = {a} \<union> tsynDom\<cdot>as"
  by (simp add: tsyndom_insert set_eq_iff)

text \<open>The empty time-slot is not part of the domain.\<close>
lemma tsyndom_sconc_eps: "tsynDom\<cdot>(\<up>eps \<bullet> s) = tsynDom\<cdot>s"
  by (metis (no_types, lifting) Collect_cong Un_insert_left tsyn.distinct(1) insert_iff sdom2un 
      sup_bot.left_neutral tsyndom_insert)

text \<open>@{term tsynDom} of the concatenation of two streams is equal to the union of @{term tsynDom} 
        applied to both streams.\<close>
lemma tsyndom_sconc: assumes "#as < \<infinity>" shows "tsynDom\<cdot>(as \<bullet> bs) = tsynDom\<cdot>as \<union> tsynDom\<cdot>bs"
  proof -
    have "sdom\<cdot>(as \<bullet> bs) = sdom\<cdot>(as) \<union> sdom\<cdot>(bs)" 
      by (meson assms ninf2Fin lnat_well_h2 sdom_sconc2un)
    then have "{x. \<M> x \<in> sdom\<cdot>(as \<bullet> bs)} = {x. \<M> x \<in> sdom\<cdot>as \<or> \<M> x \<in> sdom\<cdot>bs}"
      by simp
    then show ?thesis 
      by (metis (no_types, lifting) Abs_cfun_inverse2 Collect_cong Collect_disj_eq tsynDom_def 
          tsyndom_cont)
  qed

text \<open>@{term tsynDom} is only a singleton set if the stream just contains one element.\<close>
lemma tsyndom_singleton_msg: "tsynDom\<cdot>(\<up>(Msg a)) = {a}"
  by (metis insert_is_Un lscons_conv sup'_def tsyndom_sconc_msg tsyndom_strict)

text \<open>@{term tsynDom} is empty if stream is eps.\<close>
lemma tsyndom_singleton_eps: "tsynDom\<cdot>(\<up>eps) = {}"
  using tsyndom_sconc_eps tsyndom_strict by fastforce

text \<open>Cardinality of the set @{term tsynDom} is smaller or equal to the length of the original 
        stream.\<close>
lemma tsyndom_slen: assumes "#s = Fin k" shows "card (tsynDom\<cdot>s) \<le> k"
  proof -
    have inj_message: "inj (\<lambda>x. \<M> x)" 
      by (meson injI tsyn.inject)
    then have image_subset_sdom: "(\<lambda>x. \<M> x) ` {u. \<M> u \<in> sdom\<cdot>s} \<subseteq> sdom\<cdot>s" 
      by (simp add: image_Collect_subsetI)
    then have inj_on_mset: "inj_on (\<lambda>x. \<M> x) {u. \<M> u \<in> sdom\<cdot>s}" 
      using inj_message inj_on_def by blast
    then have sdom_is_image: "sdom\<cdot>s = (\<lambda>n. snth n s) ` {i :: nat. Fin i < #s}"
      by (metis (no_types) sdom_def2 setcompr_eq_image)
    then have "finite (sdom\<cdot>s)"
      using nat_seg_image_imp_finite assms by simp
    then have "card ({u. \<M> u \<in> sdom\<cdot>s}) \<le> card (sdom\<cdot>s)" 
      using inj_on_mset card_inj_on_le image_subset_sdom by blast 
    then have "card {u. \<M> u \<in> sdom\<cdot>s} \<le> k"
      using sdom_slen assms le_trans by blast
    then show ?thesis
      by (simp add: tsyndom_insert)
  qed

lemma tsyndom_subset: "tsynDom\<cdot>(stake n\<cdot>s) \<subseteq> tsynDom\<cdot>s"
  apply(induction s arbitrary: n rule:ind)
  apply auto
  apply (smt monofun_cfun_arg set_cpo_simps(1) triv_admI ub_stake)
  by (metis cont_pref_eq1I contra_subsetD set_cpo_simps(1) stream.take_below)

lemma tsyn_ticks_only: assumes "#s = Fin n" and "tsynDom\<cdot>s = {}"
  shows "s = sntimes n (\<up>~)"
  using assms proof(induction s arbitrary: n rule: finind)
  case 1
  then show "#s = Fin n"
    by (simp add: assms(1))
next
  case 2
  then show ?case
    by simp 
next
  case (3 a s)
  hence "a = ~"
    by (metis insert_is_Un insert_not_empty tsyn.exhaust tsyndom_sconc_msg)
  then show ?case
    by (metis (no_types, lifting) "3.IH" "3.prems"(1) "3.prems"(2) Fin_0 bot_is_0 gr0_implies_Suc inject_lnsuc lnat.con_rews neq0_conv slen_scons sntimes.simps(2) sntimes_len tsyndom_sconc_eps)
qed

lemma tsyn_ticks_only_inf: assumes "#s = \<infinity>" and "tsynDom\<cdot>s = {}"
  shows "s = (\<up>~)\<infinity>"
proof - 
  have "\<And>n. tsynDom\<cdot>(stake n\<cdot>s) = {}"
    using assms(2) tsyndom_subset by fastforce
  hence "\<And>n. stake n\<cdot>s = stake n\<cdot>((\<up>~)\<infinity>)"
    by (metis assms(1) slen_stake_fst_inf sntimes_stake tsyn_ticks_only)
  thus ?thesis
    using stream.take_lemma by blast 
qed

text \<open>@{term tsynDom} inverses the msg, removes eps.\<close>
lemma tsyndom_sdom: "tsynDom\<cdot>s = inverseMsg ` ((sdom\<cdot>s) - {eps})"
  apply (simp add: tsyndom_insert image_def set_eq_iff)
  by (metis DiffE DiffI empty_iff insert_iff inverseMsg.simps(2) tsyn.exhaust tsyn.simps(3))

text \<open>@{term tsynDom} test on finite stream.\<close>
lemma tsyndom_test_finstream: "tsynDom\<cdot>(<[Msg (1 :: nat), Msg 2, eps, eps, Msg 1, eps]>) = {1, 2}"
  apply (simp add: tsyndom_insert set_eq_iff) 
  by blast

text \<open>@{term tsynDom} test on infinite stream.\<close>
lemma tsyndom_test_infstream: "tsynDom\<cdot>((<[Msg (1 :: nat), Msg 2, eps, Msg 3]>)\<infinity>) = {1, 2, 3}"
  apply (simp add:  tsyndom_insert set_eq_iff)
  by blast


(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynAbs\<close>
(* ----------------------------------------------------------------------- *)

text \<open>@{term tsynAbs} insertion lemma.\<close>
lemma tsynabs_insert: "tsynAbs\<cdot>s = smap tsynAbsElem\<cdot>(sfilter {e. e \<noteq> eps}\<cdot>s)"
  by (simp add: tsynAbs_def)                            

text \<open>@{term tsynAbs} maps the empty stream on the empty stream.\<close>
lemma tsynabs_strict [simp]: "tsynAbs\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynabs_insert)

text \<open>@{term tsynAbs} distributes over concatenation.\<close>
lemma tsynabs_sconc_msg[simp]: "tsynAbs\<cdot>(\<up>(Msg a) \<bullet> as) = \<up>a \<bullet> (tsynAbs\<cdot>as)"
  by (simp add: tsynabs_insert)

text \<open>@{term tsynAbs} ignores empty time-slots.\<close>
lemma tsynabs_sconc_eps[simp]: "tsynAbs\<cdot>(\<up>eps \<bullet> s) = tsynAbs\<cdot>s"
  by (simp add: tsynabs_insert)

text \<open>@{term tsynAbs} of the concatenation of two streams equals the concatenation of 
        @{term tsynAbs} of both streams.\<close>
lemma tsynabs_sconc: assumes "#as < \<infinity>" shows "tsynAbs\<cdot>(as \<bullet> bs) = tsynAbs\<cdot>as \<bullet> tsynAbs\<cdot>bs"
  by (simp add: add_sfilter2 assms smap_split tsynabs_insert)

text \<open>@{term tsynAbs} of a singleton stream with a message is the singleton stream with the 
        message.\<close>
lemma tsynabs_singleton_msg[simp]: "tsynAbs\<cdot>(\<up>(Msg a)) = \<up>a"
  by (simp add: tsynabs_insert)

text \<open>@{term tsynAbs} of a singleton stream with eps is the empty stream.\<close>
lemma tsynabs_singleton_eps[simp]: "tsynAbs\<cdot>(\<up>eps) = \<epsilon>"
  by (simp add: tsynabs_insert)

lemma tsynabs_below_lub: "chain Y \<Longrightarrow> #(tsynAbs\<cdot>(Y i )) \<le> #(tsynAbs\<cdot>(\<Squnion>i. Y i))"
  using is_ub_thelub mono_slen monofun_cfun_arg by blast


text \<open>Length of @{term tsynAbs} is smaller or equal to the length of the original stream.\<close>
lemma tsynabs_slen: "#(tsynAbs\<cdot>s) \<le> #s"
  by (simp add: slen_sfilterl1 tsynabs_insert)

lemma tsynabs_sdom_subset_eq: "(sdom\<cdot>s \<subseteq> insert ~ (Msg ` range a)) = (sdom\<cdot>(tsynAbs\<cdot>s) \<subseteq> range a)"
  proof (induction s rule: tsyn_ind)
    case adm
    then show ?case 
      by (rule admI, simp add: contlub_cfun_arg lub_eq_Union UN_subset_iff)
  next
    case bot
    then show ?case 
      by simp
  next
    case (msg m s)
    then show ?case 
      by (simp only: tsynabs_sconc_msg sdom2un, auto)
  next
    case (eps s)
    then show ?case 
      by (simp only: tsynabs_sconc_eps sdom2un, auto)
  qed

(* ToDo: rename or remove as duplicate. *)

text \<open>The set of messages of a stream equals the set of values of @{term tsynAbs} of the 
        stream.\<close>
lemma tsynabs_tsyndom: "tsynDom\<cdot>s = sdom\<cdot>(tsynAbs\<cdot>s)"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (simp add: tsynabs_sconc_msg tsyndom_sconc_msg)
  by (simp add: tsyndom_sconc_eps tsynabs_sconc_eps)

lemma tsyn_fin_msg: assumes "#(tsynAbs\<cdot>s) < \<infinity>" and "#s = \<infinity>"
  shows "\<exists>n. sdrop n\<cdot>s = \<up>~ \<infinity>"
proof - 
  obtain n where "tsynAbs\<cdot>s = tsynAbs\<cdot>(stake n\<cdot>s)"
    by (meson assms(1) fun_approxl2 lnat_well_h2)
  have "tsynAbs\<cdot>s = (tsynAbs\<cdot>(stake n\<cdot>s)) \<bullet> (tsynAbs\<cdot>(sdrop n\<cdot>s))"
    by (metis Fin_neq_inf inf_less_eq not_le split_streaml1 tsynabs_sconc ub_slen_stake)
  hence "tsynAbs\<cdot>(sdrop n\<cdot>s) = \<epsilon>"
    by (metis \<open>tsynAbs\<cdot>s = tsynAbs\<cdot>(stake n\<cdot>s)\<close> assms(1) lnat_well_h2 sconc_snd_empty sdropl6)
  hence "tsynDom\<cdot>(sdrop n\<cdot>s) = {}" using tsynabs_tsyndom by force
  moreover have "#(sdrop n\<cdot>s) = \<infinity>"
    using assms(2) fair_sdrop by blast
  ultimately have "sdrop n\<cdot>s = \<up>~ \<infinity>"
    using tsyn_ticks_only_inf by blast
  thus ?thesis
    by blast 
qed

lemma tsynabs_sdom: "sdom\<cdot>(tsynAbs\<cdot>s) = tsynDom\<cdot>s"
  apply (induction rule: tsyn_ind, simp_all)
  apply (simp add: tsynabs_sconc_msg tsyndom_sconc_msg)
  by (simp add: tsynabs_sconc_eps tsyndom_sconc_eps)

lemma tsynabs_fin_take: assumes "#(tsynAbs\<cdot>s) < \<infinity>"
  shows "\<exists>n. tsynAbs\<cdot>(stake n\<cdot>s) = tsynAbs\<cdot>s"
  by (metis assms fun_approxl2 lnat_well_h2)

lemma tsynabs_fin_drop: assumes "#(tsynAbs\<cdot>s) < \<infinity>"
  shows "\<exists>n. tsynAbs\<cdot>(sdrop n\<cdot>s) = \<bottom>"
  by (metis (no_types, lifting) assms drop_not_all inf_less_eq leI notinfI3 sconc_neq_h sconc_snd_empty sdropostake split_streaml1 tsynabs_fin_take tsynabs_sconc)


text \<open>@{term tsynAbs} test on finite stream.\<close>
lemma tsynabs_test_finstream: "tsynAbs\<cdot>(<[Msg 1, Msg 2, eps, eps, Msg 1, eps]>) = <[1, 2, 1]>"
  by (simp add: tsynabs_insert)

text \<open>@{term tsynAbs} test on infinite stream.\<close>
lemma tsynabs_test_infstream: "tsynAbs\<cdot>((<[Msg 1, Msg 2, eps, Msg 3]>)\<infinity>) = (<[1, 2, 3]>)\<infinity>"
  by (simp add: tsynabs_insert)

text \<open>If a timed stream has a finite prefix of @{term eps}, then applying {@term tsynAbs} gives
        us the same result  whether we drop the prefix before or not.\<close>
lemma tsynabs_remeps[simp]:
  assumes "sdom\<cdot>s= {eps}"
  and "# s < \<infinity>"
  shows "tsynAbs\<cdot>(s\<bullet>s2) = tsynAbs\<cdot>s2"
  using assms apply(induction s rule: tsyn_ind, simp_all add: assms)
  apply (rule admI)
  apply (metis inf_chainl4 l42 neq_iff)
  by (metis le_less_trans less_lnsuc sconc_fst_empty strict_sdom_rev subset_singleton_iff)

text \<open>If a timed stream has a finite prefix of @{term eps}, followed by some message 
        {@term Msg}, then the stream obtained by applying  {@term tsynAbs} to it begins with this
        message.\<close>
lemma tsynabs_remeps_msg:
  assumes "sdom\<cdot>s={~}"
  and "# s < \<infinity>"
  shows "tsynAbs\<cdot>(s \<bullet> \<up>(Msg a) \<bullet> s2) = \<up>a \<bullet>(tsynAbs\<cdot>s2)"
  using assms by simp

lemma tsynabs_ind [case_names adm bot msg]:
  assumes adm: "adm P"
    and bot: "P \<epsilon>"
    and msg: "\<And>m s. P (tsynAbs\<cdot>s) \<Longrightarrow> P (tsynAbs\<cdot>(\<up>(Msg m) \<bullet> s))"
  shows "P (tsynAbs\<cdot>x)"
  apply (induction x rule: tsyn_ind)
  apply (simp add: adm adm_subst)
  apply (simp add: bot) 
  using msg by auto

lemma tsynabs_cases [case_names bot msg]:
  assumes bot: "tsynAbs\<cdot>x = \<epsilon> \<Longrightarrow> P \<epsilon>"
    and msg: "\<And>m s. tsynAbs\<cdot>x = \<up>m \<bullet> s \<Longrightarrow> P (\<up>m \<bullet> s)"
  shows "P (tsynAbs\<cdot>x)"
  apply (rule_tac x = "tsynAbs\<cdot>x" in scases)
  apply (simp add: bot)
  by (simp add: msg)

lemma tsynabs_stakewhile: "tsynAbs\<cdot>(stakewhile (\<lambda>x. x = ~)\<cdot>s) = \<epsilon>"
  apply (induction s rule: tsyn_ind)
  by simp_all

lemma tsynabs_sdropwhile_neps:
  assumes "tsynAbs\<cdot>a \<noteq> \<epsilon>"
  shows "sdropwhile (\<lambda>x. x = ~)\<cdot>a \<noteq> \<epsilon>"
  by (metis assms sconc_snd_empty stakewhileDropwhile tsynabs_stakewhile)

lemma tsynabs_sdropwhile: "tsynAbs\<cdot>(sdropwhile (\<lambda>x. x = ~)\<cdot>ts) = tsynAbs\<cdot>ts"
  apply (induction ts rule: tsyn_ind)
  by simp_all

lemma tsynabs_sdropwhile_srt:
  "tsynAbs\<cdot>(srt\<cdot>(sdropwhile (\<lambda>x. x = ~)\<cdot>port_i)) = srt\<cdot>(tsynAbs\<cdot>port_i)"
  apply (induction port_i rule: tsyn_ind)
  by simp_all

lemma sdropwhile2tsynabs_shd:
  assumes "sdropwhile (\<lambda>x. x = ~)\<cdot>ts = \<up>(\<M> m) \<bullet> s"
  shows "shd (tsynAbs\<cdot>ts) = m"
  by (metis assms shd1 tsynabs_sdropwhile tsynabs_sconc_msg)

lemma sdropwhile_shd2tsynabs_shd:
  assumes "shd (sdropwhile (\<lambda>x. x = ~)\<cdot>ts) = \<M> m"
    and "tsynAbs\<cdot>ts \<noteq> \<epsilon>" (* should not be necessary *)
  shows "shd (tsynAbs\<cdot>ts) = m"
  by (metis assms surj_scons tsynabs_sdropwhile_neps sdropwhile2tsynabs_shd)

(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynLen\<close>
(* ----------------------------------------------------------------------- *)

text \<open>@{term tsynLen} insertion lemma.\<close>
lemma tsynlen_insert: "tsynLen\<cdot>s =  #(tsynAbs\<cdot>s)"
  by (simp add: tsynLen_def)

text \<open>@{term tsynLen} maps the empty stream to zero.\<close>
lemma tsynlen_strict [simp]: "tsynLen\<cdot>\<epsilon> = 0"
  by (simp add: tsynlen_insert)

text \<open>@{term tsynLen} distributes over concatenation.\<close>
lemma tsynlen_sconc_msg: "tsynLen\<cdot>(\<up>(Msg a) \<bullet> as) = lnsuc\<cdot>(tsynLen\<cdot>as)"
  by (simp add: tsynabs_sconc_msg tsynlen_insert)

text \<open>@{term tsynLen} distributes over concatenation.\<close>
lemma tsynlen_sconc_msg2:
  assumes "m \<noteq> ~"
  shows "tsynLen\<cdot>(\<up>m \<bullet> s) = lnsuc\<cdot>(tsynLen\<cdot>s)"
using tsynlen_sconc_msg assms tsynAbsElem.cases by blast

text \<open>@{term tsynLen} ignores empty time slots.\<close>
lemma tsynlen_sconc_eps: "tsynLen\<cdot>(\<up>(eps) \<bullet> as) = tsynLen\<cdot>as"
  by (simp add: tsynabs_sconc_eps tsynlen_insert)

text \<open>@{term tsynLen} of the concatenation of two streams equals the sum of @{term tsynLen} of 
        both streams if the number of messages and the first stream are finite.\<close>
lemma tsynlen_sconc_finite:
  assumes "#as < \<infinity>" and "tsynLen\<cdot>as = Fin k" and "tsynLen\<cdot>bs = Fin n"
  shows "tsynLen\<cdot>(as \<bullet> bs) = Fin (k + n)"
  using assms
  by (simp add: slen_sconc_all_finite tsynabs_sconc tsynlen_insert)

text \<open>@{term tsynLen} of the concatenation of two streams with finite many messages is less or 
        equal to the sum of @{term tsynLen} of both streams\<close>
lemma  tsynlen_sconc_infinite:
  assumes "tsynLen\<cdot>as = Fin n" and "tsynLen\<cdot>bs = Fin  m"
  shows "tsynLen\<cdot>(as \<bullet> bs) \<le> Fin (n + m)"
  using assms leI sconc_fst_inf tsynlen_sconc_finite by fastforce

text \<open>@{term tsynLen} is less or equal to the length of the stream.\<close>
lemma tsynlen_slen: "tsynLen\<cdot>s \<le> slen\<cdot>s"
  by (simp add: tsynabs_slen tsynlen_insert)

text \<open>@{term tsynLen} Non-empty singleton streams have length 1.\<close>
lemma tsynlen_singleton_msg: "tsynLen\<cdot>(\<up>(Msg a)) = Fin 1"
  by (simp add: tsynlen_insert tsynabs_singleton_msg)

text \<open>@{term tsynLen} Empty slots have length zero.\<close>
lemma tsynlen_singleton_eps: "tsynLen\<cdot>(\<up>eps) = 0"
  by (simp add: tsynabs_singleton_eps tsynlen_insert)

text \<open>If the last element of a tsyn stream is a message, tsynLen is greater than 0\<close>
lemma tsynlen_sfoot_msg_geq:
  assumes "#s < \<infinity>"
    and "s \<noteq> \<epsilon>"
    and "sfoot s = (\<M> m)" 
  shows "Fin 1 \<le> tsynLen\<cdot>s"
  using assms
  apply (induction s arbitrary: m rule: tsyn_finind, simp_all)
  apply (metis Fin_02bot One_nat_def gr_0 less2lnleD lnzero_def tsynlen_sconc_msg)
  by (metis Fin_02bot Fin_Suc Fin_neq_inf inf_ub less_le lnzero_def only_empty_has_length_0 
      sconc_snd_empty sfoot_conc sfoot_one slen_sconc_snd_inf slen_scons strict_slen 
      tsyn.distinct(1) tsynlen_sconc_eps)

text \<open>If @{term tsynLen} is infinity the stream cannot be empty.\<close>
lemma tsynlen_inf_nbot: assumes "tsynLen\<cdot>s = \<infinity>"
  shows "s \<noteq> \<epsilon>"
  using assms by fastforce

text \<open>@{term tsynLen} of the infinte concatenation of a finite stream with more than one 
        message is @{term "\<infinity>"}.\<close>
lemma tsynlen_inftimes_finite:
  assumes "#as < \<infinity> " and "0 < tsynLen\<cdot>as" 
  shows "tsynLen\<cdot>as\<infinity> = \<infinity>"
  by (metis (no_types, lifting) assms(1) assms(2) neq_iff rek2sinftimes sinftimes_unfold 
      slen_empty_eq slen_sinftimes tsynabs_sconc tsynlen_insert)

text \<open>@{term tsynLen} test for finite tsyn stream.\<close>
lemma tsynlen_test_finstream: 
  "tsynLen\<cdot>(<[Msg 1, eps, Msg 2, eps, eps, Msg 1]>) = Fin 3"
  by (simp add: tsynlen_insert tsynabs_sconc_msg tsynabs_sconc_eps tsynabs_singleton_msg)

text \<open>@{term tsynLen} test for infinite tsyn stream.\<close>
lemma tsynlen_test_infstream: "tsynLen\<cdot>(<[eps, Msg a]>\<infinity>) = \<infinity>"
  by (metis Fin_neq_inf gr_0 inf_ub less_le list2s_Suc list2streamFin lscons_conv 
      tsynlen_inftimes_finite tsynlen_sconc_msg tsynlen_sconc_eps) 

lemma tsynabs_snths_eq [case_names len nth]:
  assumes len: "tsynLen\<cdot>x = tsynLen\<cdot>y"
      and nth: "\<And>n. Fin n < tsynLen\<cdot>x \<Longrightarrow> snth n (tsynAbs\<cdot>x) =  snth n (tsynAbs\<cdot>y)"
  shows "tsynAbs\<cdot>x = tsynAbs\<cdot>y"
  by (metis len nth snths_eq tsynlen_insert)

lemma tsynabs_snths_eq_ext [case_names len nth]:
  assumes len: "tsynLen\<cdot>x = slen\<cdot>y"
      and nth: "\<And>n. Fin n < tsynLen\<cdot>x \<Longrightarrow> snth n (tsynAbs\<cdot>x) =  snth n y"
  shows "tsynAbs\<cdot>x = y"
  by (metis len nth snths_eq tsynlen_insert)

lemma tsynlen2sdropwhile_neps:
  assumes "0 < tsynLen\<cdot>a"
  shows "sdropwhile (\<lambda>x. x = ~)\<cdot>a \<noteq> \<epsilon>"
  by (metis assms gr_0 lnsuc_neq_0 slen_empty_eq tsynabs_sdropwhile_neps tsynlen_insert)

lemma tsynlen2neps:
  assumes "0 < tsynLen\<cdot>s"
  shows "s \<noteq> \<epsilon>"
  using assms by auto

lemma tsynlen2tsynabs_neps: 
  assumes "0 < tsynLen\<cdot>s"
  shows "tsynAbs\<cdot>s \<noteq> \<epsilon>"
  by (metis assms strict_slen tsynlen_insert tsynlen2neps tsynlen_strict)

lemma tsynlen_inf2tsynabs_neps:
  assumes "tsynLen\<cdot>s = \<infinity>"
  shows "tsynAbs\<cdot>s \<noteq> \<epsilon>"
  by (metis Inf'_neq_0_rev assms strict_slen tsynlen_insert)

(* ----------------------------------------------------------------------- *)
  subsection \<open>Induction variants with Length.\<close>
(* ----------------------------------------------------------------------- *)

text \<open>Cases rule for infinite time-synchronous streams.\<close>
lemma tsyn_cases_inf [case_names inf msg eps]:
  assumes inf: "tsynLen\<cdot>s = \<infinity>"
    and msg: "\<And>a as. s= (\<up>(Msg a) \<bullet> as) \<Longrightarrow> P s"
    and eps: "\<And>as. s=(\<up>eps \<bullet> as) \<Longrightarrow> P s"
  shows "P s"
  using assms
  apply (cases rule: scases [of s], simp_all)
  by (metis tsynAbsElem.cases)

(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynEps\<close>
(* ----------------------------------------------------------------------- *)

lemma tsyneps_insert: "tsynEps\<cdot>ts = #(sfilter {~}\<cdot>ts)"
  by (simp add: tsynEps_def)

lemma tsyneps_strict [simp]:"tsynEps\<cdot>\<epsilon> = 0"
  by (simp add: tsyneps_insert)

lemma tsyneps_sconc_msg:"tsynEps\<cdot>(\<up>(\<M> m) \<bullet> ts) = tsynEps\<cdot>ts"
  by (simp add: tsyneps_insert)

lemma tsyneps_sconc_eps:"tsynEps\<cdot>(\<up>~ \<bullet> ts) = lnsuc\<cdot>(tsynEps\<cdot>ts)"
  by(simp add: tsyneps_insert)

text \<open>@{term tsynEps} of the concatenation of two streams equals the sum of @{term tsynEps} of 
        both streams if the number of epss and the first stream are finite.\<close>
lemma tsyneps_sconc_finite:
  assumes "#as < \<infinity>"
  and "tsynEps\<cdot>as = Fin k"
  and "tsynEps\<cdot>bs = Fin n"
  shows "tsynEps\<cdot>(as \<bullet> bs) = Fin (k + n)"
  using assms
  by (simp add: slen_sconc_all_finite tsyneps_insert add_sfilter2 sconc_slen2)

text \<open>@{term tsynEps} of the concatenation of two streams with finite many epss is less or 
        equal to the sum of @{term tsynEps} of both streams\<close>
lemma  tsyneps_sconc_infinite:
  assumes "tsynEps\<cdot>as = Fin n"
  and "tsynEps\<cdot>bs = Fin m"
  shows "tsynEps\<cdot>(as \<bullet> bs) \<le> Fin (n + m)"
  using assms leI sconc_fst_inf tsyneps_sconc_finite by fastforce

text \<open>@{term tsynEps} is less or equal to the length of the stream.\<close>
lemma tsyneps_slen: "tsynEps\<cdot>s \<le> slen\<cdot>s"
  by (simp add: slen_sfilterl1 tsyneps_insert)

text \<open>@{term tsynEps} Non-empty singleton streams have length 0.\<close>
lemma tsyneps_singleton_msg: "tsynEps\<cdot>(\<up>(Msg a)) = Fin 0"
  by (simp add: tsyneps_insert)

text \<open>@{term tsynEps} Empty slots have length 1.\<close>
lemma tsyneps_singleton_eps: "tsynEps\<cdot>(\<up>eps) = Fin 1"
  by (simp add: tsyneps_insert)

text \<open>If the last element of a tsyn stream is an eps, tsynEps is greater than 0\<close>
lemma tsyneps_sfoot_msg_geq:
  assumes "#s < \<infinity>"
    and "s \<noteq> \<epsilon>"
    and "sfoot s = ~"
  shows "Fin 1 \<le> tsynEps\<cdot>s"
  using assms
  apply (induction s rule: tsyn_finind, simp_all)
  apply (metis fold_inf inf_ub leD neq_iff sconc_fst_inf sconc_snd_empty sfoot_conc sfoot_one tsyn.distinct(1) tsyneps_sconc_msg)
  by (simp add: One_nat_def tsyneps_sconc_eps)

text \<open>If @{term tsynEps} is infinity the stream cannot be empty.\<close>
lemma tsyneps_inf_nbot: assumes "tsynEps\<cdot>s = \<infinity>"
  shows "s \<noteq> \<epsilon>"
  using assms by fastforce

text \<open>@{term tsynEps} of the infinte concatenation of a finite stream with more than one 
        message is @{term "\<infinity>"}.\<close>
lemma tsyneps_inftimes_finite:
  assumes "#as < \<infinity> "
  and "0 < tsynEps\<cdot>as" 
shows "tsynEps\<cdot>as\<infinity> = \<infinity>"
  using assms
  by (metis neq_iff sfilter_sinf slen_sinftimes strict_slen tsyneps_insert)

text \<open>@{term tsynEps} test for finite tsyn stream.\<close>
lemma tsyneps_test_finstream: 
  "tsynEps\<cdot>(<[Msg 1, eps, Msg 2, eps, eps, Msg 1]>) = Fin 3"
  by (simp add: tsyneps_insert)

text \<open>@{term tsynEps} test for infinite tsyn stream.\<close>
lemma tsyneps_test_infstream: "tsynEps\<cdot>(<[eps, Msg a]>\<infinity>) = \<infinity>"
  by (metis Fin_neq_inf gr_0 inf_ub less_le list2s_Suc list2streamFin lscons_conv 
      tsyneps_inftimes_finite tsyneps_sconc_eps) 

(* ----------------------------------------------------------------------- *)
  subsection \<open>Relationship between {@term tsynEps}, {@term tsynLen}  {@term slen}\<close>
(* ----------------------------------------------------------------------- *)

text \<open>The {@term slen} of stream is the sum of its finite  {@term tsynLen} and finite
        {@term tsynEps}. There is also a stronger variant of this lemma, that generalizes
        to the infinite cases: {@term tsynlen_tsyneps2slen\<close>
lemma tsyneps_tsyneps2slen_finite:
  assumes "#as < \<infinity>"
  and "tsynEps\<cdot>as = k"
  and "tsynLen\<cdot>as = n"
  shows "#as = k + n"
  using assms
  apply (induction as arbitrary: n k  rule: tsyn_ind, simp_all)
  apply (simp_all add: tsyneps_sconc_msg tsynlen_sconc_eps)
   apply (metis add.assoc inf_ub less_le lnat_plus_suc sconc_fst_inf slen_lnsuc tsynlen_sconc_msg)
  by (metis (no_types, hide_lams) add.assoc le_less_trans less_lnsuc lnat_plus_lnsuc lnat_plus_suc tsyneps_sconc_eps)

text \<open>If a stream has infinite {@tsynLen} then it has infnite {@term slen}\<close>
lemma  tsyneps_tsyneps2slen_infinite_msg:
  assumes "tsynLen\<cdot>as = \<infinity>"
  shows "#as = \<infinity>"
  using assms
  by (metis inf_less_eq tsynlen_slen) 

text \<open>If a stream has infinite {@tsynEps} then it has infnite {@term slen}\<close>
lemma  tsyneps_tsyneps2slen_infinite_eps:
  assumes "tsynEps\<cdot>as = \<infinity>"
  shows "#as = \<infinity>"
  using assms
  by (metis inf_less_eq tsyneps_slen)  

text \<open>The {@term slen} of stream is the sum of its {@term tsynLen} and {@term tsynEps}.
        Same as {@term tsynlen_tsyneps2slen}, but more verbose.\<close>
lemma  tsyneps_tsyneps2slen_verbose:
  assumes "tsynEps\<cdot>as = n"
  and "tsynLen\<cdot>as = m"
  shows "#as = n + m"
  using assms apply(case_tac "n = \<infinity>")
  apply (simp add: tsyneps_tsyneps2slen_infinite_eps plus_lnatInf_r)
  using assms apply(case_tac "m = \<infinity>")
  apply (simp add: tsyneps_tsyneps2slen_infinite_msg)
  apply (subst tsyneps_tsyneps2slen_finite, simp_all)
  apply (simp add: tsyneps_insert tsynlen_insert tsynabs_insert)
  by (metis Fin_02bot Fin_Suc One_nat_def assms(2) inf_ub less_le ln_less lnle_Fin_0 not_less notinfI3 sfilter_sinftimes_in slen_sfilter_sdrop_ile slen_sinftimes strict_sfilter strict_slen tsyn_fin_msg tsyneps_insert tsyneps_singleton_eps tsynlen_insert)

text \<open>The {@term slen} of stream is the sum of its {@term tsynLen} and {@term tsynEps}.
        Same as {@term tsyneps_tsyneps2slen_verbose}, but less verbose.\<close>
lemma tsynlen_tsyneps2slen:"#\<^sub>-(ts) + (tsynEps\<cdot>ts) = #ts"
  by (simp add: tsyneps_tsyneps2slen_verbose lnat_plus_commu)

text \<open>If two streams have the same {@term slen} and same finite {@term tsynEps}, then they
        also have the same {@term tsynLen}\<close>
lemma tsynlen_eq_tsynLen_verbose:
  assumes "m < \<infinity>"
    and "#s1 = n"
    and "#s2 = n"
    and "tsynEps\<cdot>s1 = m"
    and "tsynEps\<cdot>s2 = m"
  shows"#\<^sub>-s1 = #\<^sub>-s2"
proof -
  have n1: "n = m + #\<^sub>-s1" using assms by (simp add: tsyneps_tsyneps2slen_verbose)
  have n2: "n = m + #\<^sub>-s2" using assms by (simp add: tsyneps_tsyneps2slen_verbose)
  show "#\<^sub>-s1 = #\<^sub>-s2" using assms(1) n1 n2 plus_unique_r
    by blast
qed

text \<open>If two streams have the same {@term slen} and same finite {@term tsynLen}, then they
        also have the same {@term tsynEps}\<close>
lemma tsynlen_eq_tsynEps_verbose:
  assumes "m < \<infinity>"
    and "#s1 = n"
    and "#s2 = n"
    and "tsynLen\<cdot>s1 = m"
    and "tsynLen\<cdot>s2 = m"
  shows "tsynEps\<cdot>s1 = tsynEps\<cdot>s2"
proof -
  have n1: "n = m + tsynEps\<cdot>s1" using assms by (simp add: tsyneps_tsyneps2slen_verbose lnat_plus_commu)
  have n2: "n = m + tsynEps\<cdot>s2" using assms by (simp add: tsyneps_tsyneps2slen_verbose lnat_plus_commu)
  show "tsynEps\<cdot>s1 = tsynEps\<cdot>s2" using assms(1) n1 n2 plus_unique_r
    by blast
qed

text \<open>Same as {@term tsynlen_eq_tsynLen_verbose}, but less verbose.\<close>
lemma tsynlen_eq_tsynLen:
  assumes "#s1 = #s2"
    and "tsynEps\<cdot>s1 < \<infinity>"
    and "tsynEps\<cdot>s1 = tsynEps\<cdot>s2"
  shows"#\<^sub>-s1 = #\<^sub>-s2"
  using assms tsynlen_eq_tsynLen_verbose by auto

text \<open>Same as {@term tsynlen_eq_tsynEps_verbose}, but less verbose.\<close>
lemma tsynlen_eq_tsynEps:
  assumes "#s1 = #s2"
    and "tsynLen\<cdot>s1 < \<infinity>"
    and "tsynLen\<cdot>s1 = tsynLen\<cdot>s2"
  shows "tsynEps\<cdot>s1 = tsynEps\<cdot>s2"
  using assms tsynlen_eq_tsynEps_verbose by auto

text \<open>If a function preserves the {@term slen} and {@term tsynEps} of a stream and a stream
        has only finite many eps, then the function preserves {@term tsynLen}\<close>
lemma tsynlen_f_preserves_tsynLen:
  fixes "s"
  assumes "tsynEps\<cdot>s < \<infinity>"
  and "#(f s) = #s"
  and "tsynEps\<cdot>(f s) = tsynEps\<cdot>s"
  shows "#\<^sub>-(f s) = #\<^sub>-s"
  using assms by (subst tsynlen_eq_tsynLen, simp_all)

text \<open>If a function preserves the {@term slen} and {@term tsynLen} of a stream and a stream
        has only finite many msgs, then the function preserves {@term tsynEps}\<close>
lemma tsynlen_f_preserves_tsynEps:
  fixes "s"
  assumes "tsynLen\<cdot>s < \<infinity>"
  and "#(f s) = #s"
  and "tsynLen\<cdot>(f s) = tsynLen\<cdot>s"
  shows "tsynEps\<cdot>(f s) = tsynEps\<cdot>s"
  using assms by (subst tsynlen_eq_tsynEps, simp_all)

(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynFilter\<close>
(* ----------------------------------------------------------------------- *)

text \<open>@{term tsynFilter} insertion lemma.\<close>
lemma tsynfilter_insert: "(tsynFilter A)\<cdot>s =  smap (tsynFilterElem A)\<cdot>s"
  by (simp add: tsynFilter_def)

text \<open>@{term tsynFilter} maps the empty stream on the empty stream.\<close>
lemma tsynfilter_strict [simp]: "(tsynFilter A)\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynfilter_insert)

text \<open>@{term tsynFilter} distributes over concatenation, having the first Stream consist of 
        one Msg-element included in the given set.\<close>
lemma tsynfilter_sconc_msg_in: assumes "m \<in> A"
   shows "(tsynFilter A)\<cdot>(\<up>(Msg m) \<bullet> as) = \<up>(Msg m) \<bullet> (tsynFilter A)\<cdot>as"
  by (simp add: assms tsynfilter_insert)

text \<open>@{term tsynFilter} distributes over concatenation, having the first Stream consist of one 
        Msg-element not included in the given set.\<close>
lemma tsynfilter_sconc_msg_nin: assumes "m \<notin> A" 
  shows"(tsynFilter A)\<cdot>(\<up>(Msg m) \<bullet> as) = \<up>(eps) \<bullet> (tsynFilter A)\<cdot>as"
  by (simp add: assms tsynfilter_insert)

text \<open>@{term tsynFilter} distributes over concatenation, having the first Stream consist of one 
        eps-element.\<close>
lemma tsynfilter_sconc_eps: "(tsynFilter A)\<cdot>(\<up>(eps)\<bullet> as) = \<up>(eps) \<bullet> (tsynFilter A)\<cdot>as"
  by (simp add: tsynfilter_insert)

text \<open>@{term tsynFilter} of the concatenation of two streams equals the concatenation of 
        @{term tsynFilter} of both streams.\<close>
lemma tsynfilter_sconc: "(tsynFilter A)\<cdot>(a1 \<bullet> a2) = (tsynFilter A)\<cdot>a1 \<bullet> (tsynFilter A)\<cdot>a2"
  by (simp add: smap_split tsynfilter_insert)

text \<open>@{term tsynFilter} If singleton element is in the filter condition, just do nothing.\<close>
lemma tsynfilter_singleton_msg_in: assumes "a \<in> A"
  shows "(tsynFilter A)\<cdot>(\<up>(Msg a)) = (\<up>(Msg a))"
  by (metis assms lscons_conv sup'_def tsynfilter_sconc_msg_in tsynfilter_strict)

text \<open>@{term tsynFilter} If singleton element is not in the filter condition,
      return empty stream.\<close>
lemma tsynfilter_singleton_msg_nin:assumes "a \<notin> A"
  shows "(tsynFilter A)\<cdot>(\<up>(Msg a)) = (\<up>eps)"
  by (simp add: assms tsynFilter_def)

text \<open>@{term tsynFilter} ignores empty time slots.\<close>
lemma tsynfilter_singleton_eps: "(tsynFilter A)\<cdot>(\<up>eps) = \<up>eps"
  by (simp add: tsynFilter_def)

text \<open>Length of @{term tsynFilter} is equal to the length of the original stream.\<close>
lemma tsynfilter_slen: "#((tsynFilter A)\<cdot>s) = #s"
  by (simp add: tsynfilter_insert)

text \<open>Abstraction of @{term tsynFilter} equals sfilter executed on abstracted stream.\<close>
lemma tsynfilter_tsynabs: "tsynAbs\<cdot>(tsynFilter A\<cdot>s) = sfilter A\<cdot>(tsynAbs\<cdot>s)"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (rename_tac x y)
  apply (case_tac "x \<in> A")
  apply (simp add: tsynfilter_sconc_msg_in tsynabs_sconc_msg)
  apply (simp add: tsynfilter_sconc_msg_nin tsynabs_sconc_msg tsynabs_sconc_eps)
  by (simp add: tsynfilter_sconc_eps tsynabs_sconc_eps)

text \<open>@{term tsynFilter} leaves the length of the stream unchanged.\<close>
lemma tsynfilter_tsynlen: "tsynLen\<cdot>(tsynFilter A\<cdot>s) \<le> tsynLen\<cdot>s"
  proof (induction s rule: tsyn_ind)
    case adm
    then show ?case 
      by (simp add: slen_sfilterl1 tsynfilter_tsynabs tsynlen_insert)  
  next
    case bot
    then show ?case 
      by simp
  next
    case (msg m s)
    then show ?case 
      apply (simp add: slen_sfilterl1 tsynfilter_tsynabs tsynlen_insert)
      by (metis slen_scons slen_sfilterl1)
  next
    case (eps s)
    then show ?case 
      by (simp add: tsynabs_sconc_eps tsynfilter_tsynabs tsynlen_insert)
  qed

text \<open>@{term sdom} of @{term tsynFilter} A is subset of @{term image} of 
        @{term tsynFilterElem} of A.\<close>
lemma tsynfilter_sdom: "sdom\<cdot>(tsynFilter A\<cdot>s) \<subseteq> tsynFilterElem A ` sdom\<cdot>s"
  apply (induction s arbitrary: A rule: tsyn_ind, simp_all)
  apply (rule admI)
  by (simp add: smap_sdom tsynfilter_insert)+

text \<open>@{term tsynDom} of @{term tsynFilter} is subset of @{term tsynDom} of 
        the original stream.\<close>
lemma tsynfilter_tsyndom: "tsynDom\<cdot>(tsynFilter A\<cdot>s) \<subseteq> tsynDom\<cdot>s"
  by (simp add: tsynabs_tsyndom tsynfilter_tsynabs)

text \<open>@{term tsynFilter} test on finite nat tsyn-stream.\<close>
lemma tsynfilter_test_finstream: 
  "(tsynFilter {(1::nat),2})\<cdot>(<[Msg 1, Msg 2, eps, Msg 3, eps, Msg 1, eps, Msg 4]>) 
     = <[Msg 1, Msg 2, eps, eps, eps, Msg 1, eps, eps]>"
  by (simp add: tsynfilter_insert)

text \<open>@{term tsynFilter} test on infinitely many time-slots.\<close>
lemma tsynfilter_test_infstream: assumes "c \<noteq> a \<and> c \<noteq> b"
  shows "(tsynFilter {a,b})\<cdot>((<[Msg a, Msg c, eps, Msg b]>)\<infinity>) = (<[Msg a, eps, eps, Msg b]>)\<infinity>"
  by (simp add: assms tsynfilter_insert)

(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynApplyElem\<close>
(* ----------------------------------------------------------------------- *)

lemma tsynApplyElem_inv_id[simp]: "inv Msg tsyn \<in> range (F) \<Longrightarrow> tsynApplyElem (F \<circ> (inv F)) tsyn = tsyn"
  apply (induction tsyn)
  apply simp_all
  by (metis UNIV_I f_inv_into_f image_iff tsynAbsElem.simps(2))

lemma tsymApply_applyF_in[simp]:"tsynApplyElem F1 (tsynApplyElem F2 tsyn) = tsynApplyElem (F1 \<circ> F2) tsyn"
  by (smt comp_apply tsynApplyElem.elims tsynApplyElem.simps(1) tsynApplyElem.simps(2))


(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynMap\<close>
(* ----------------------------------------------------------------------- *)

text \<open>@{term tsynMap} insertion lemma.\<close>
lemma tsynmap_insert: "tsynMap f\<cdot>s = smap (tsynApplyElem f)\<cdot>s"
  by (simp add: tsynMap_def)

text \<open>@{term tsynMap} is strict.\<close>
lemma tsynmap_strict [simp]: "tsynMap f\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynmap_insert)

text \<open>@{term tsynMap} distributes over concatenation.\<close>
lemma tsynmap_sconc_msg: "tsynMap f\<cdot>(\<up>(Msg m) \<bullet> s) = \<up>(Msg (f m)) \<bullet> tsynMap f\<cdot>s"
  by (simp add: tsynmap_insert)

text \<open>@{term tsynMap} ignores empty time-slots.\<close>
lemma tsynmap_sconc_eps: "tsynMap f\<cdot>(\<up>eps \<bullet> s) = \<up>eps \<bullet> tsynMap f\<cdot>s"
  by (simp add: tsynmap_insert)

text \<open>@{term tsynMap} of the concatenation of two streams equals the concatenation of 
        @{term tsynMap} of both streams.\<close>
lemma tsynmap_sconc: "tsynMap f\<cdot>(a1 \<bullet> a2) = tsynMap f\<cdot>a1 \<bullet> tsynMap f\<cdot>a2"
  by (simp add: smap_split tsynmap_insert)

text \<open>@{term tsynMap} of a stream containing only one element, is just the stream 
          with the function applied to that element.\<close>
lemma tsynmap_singleton_msg: "tsynMap f\<cdot>(\<up>(Msg a)) = (\<up>(Msg (f a)))"
  by (simp add: tsynMap_def)

text \<open>@{term tsynMap} is eps-stream if stream was eps.\<close>
lemma tsynmap_singleton_eps: "tsynMap f\<cdot>(\<up>eps) = \<up>eps"
  by (simp add: tsynMap_def)

text \<open>@{term tsynMap} leaves the length of a stream unchanged.\<close>
lemma tsynmap_slen: "#(tsynMap f\<cdot>s) = #s"
  by (simp add: tsynmap_insert)

text \<open>@{term tsynMap} leaves the length of a tsyn stream unchanged.\<close>
lemma tsynmap_tsynlen: "tsynLen\<cdot>(tsynMap f\<cdot>ts) = tsynLen\<cdot>ts"
proof (induction ts rule: tsyn_ind)
  case adm
  then show ?case by simp
next
  case bot
  then show ?case by simp
next
  case (eps s)
  then show ?case by (simp add: tsynlen_sconc_eps tsynmap_sconc_eps)
next
  case (msg m s)
  then show ?case by (simp add: tsynlen_sconc_msg tsynmap_sconc_msg)
qed

text \<open>Abstraction of @{term tsynMap} equals sMap executed on abstracted stream.\<close>
lemma tsynmap_tsynabs: "tsynAbs\<cdot>(tsynMap f\<cdot>s) = smap f\<cdot>(tsynAbs\<cdot>s)"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (simp add: tsynmap_sconc_msg tsynabs_sconc_msg)
  by (simp add: tsynmap_sconc_eps tsynabs_sconc_eps)

text \<open>Every value produced by @{term tsynMap} of the function f is in @{term image} of @{term tsynApplyElem} f\<close>
lemma tsynmap_sdom: "sdom\<cdot>(tsynMap f\<cdot>s) = tsynApplyElem f ` sdom\<cdot>s"
  apply (induction s arbitrary: f rule: tsyn_ind, simp_all)
  apply (rule admI)
  by (simp add: smap_sdom tsynmap_insert)+

text \<open>Every message produced by @{term tsynMap} of the function f is in @{term image} of f\<close>
lemma tsynmap_tsyndom: "tsynDom\<cdot>(tsynMap f\<cdot>s) = f ` tsynDom\<cdot>s"
  by (simp add: tsynmap_tsynabs tsynabs_tsyndom smap_sdom)

text \<open>Every message produced by @{term tsynMap} of the function f is in @{term range} of f\<close>
lemma tsynmap_tsyndom_range: "tsynDom\<cdot>(tsynMap f\<cdot>s) \<subseteq> range f"
  by (simp add: tsynabs_tsyndom tsynmap_tsynabs)

text \<open>@{term tsynMap} of the function f on @{term tsynMap} of the function g is 
        the function composition of f and g\<close>
lemma tsynmap_tsynmap: "tsynMap f\<cdot>(tsynMap g\<cdot>s) = tsynMap (\<lambda> x. f (g x))\<cdot>s"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (simp add: tsynmap_sconc_msg)
  by (simp add: tsynmap_sconc_eps)

text \<open>@{term tsynMap} of the identity function leaves the stream unchanged.\<close>
lemma tsynmap_id: "tsynMap (\<lambda>x. x)\<cdot>s = s"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (simp add: tsynmap_sconc_msg)
  by (simp add: tsynmap_sconc_eps)

lemma tsynmap_tsynmap2[simp]: "tsynMap f\<cdot>(tsynMap g\<cdot>s) = tsynMap (f\<circ>g)\<cdot>s"
  apply(induction s rule: tsyn_ind)
     apply simp_all
  by(simp add: tsynmap_sconc_eps tsynmap_sconc_msg)+

lemma tsynmap_id2 [simp]: "tsynMap id\<cdot>s = s"
  apply(induction s rule: tsyn_ind)
  apply simp_all
  by(simp add: tsynmap_sconc_eps tsynmap_sconc_msg)+

lemma tsynmap_funcomp_id:
  assumes "\<forall>a. f (f a) = a"
  shows "tsynMap f\<cdot>(tsynMap f\<cdot>s) = s"
  apply (induction s rule: tsyn_ind)
  apply (rule admI)
  apply (simp add: ch2ch_Rep_cfunR contlub_cfun_arg op_the_lub op_the_chain)+
  apply (simp add: assms tsynmap_sconc_msg)
  by (simp add: tsynmap_sconc_eps)

lemma tsynmap_inv_id[simp]: "tsynDom\<cdot>tsyn \<subseteq> range F \<Longrightarrow> tsynMap (F \<circ> (inv F))\<cdot>tsyn = tsyn"
  apply (induction tsyn rule: ind)
  apply simp_all
  apply (rename_tac x xs)
  apply (case_tac x)
  apply (auto simp add: tsynmap_sconc_msg tsynmap_sconc_eps)
  by (auto simp add: tsyndom_sconc_msg tsyndom_sconc_eps f_inv_into_f)

lemma tsynmap_inv_eq: 
  assumes "surj f"
    and "tsynMap (inv f)\<cdot>s1 = tsynMap (inv f)\<cdot>s2"
  shows "s1 = s2"
  by (metis (no_types, lifting) UNIV_I assms subsetI tsynmap_inv_id tsynmap_tsynmap2)

text \<open>@{term tsynMap} test on finite stream.\<close>
lemma tsynMap_test_finstream: "tsynMap (plus 1)\<cdot>(<[Msg 1, Msg 2, Msg 1, eps]>) 
  = <[Msg 2, Msg 3, Msg 2, eps]>"
  by (simp add: tsynmap_insert)

text \<open>@{term tsynMap} test on infinite stream.\<close>
lemma tsynMap_test_infstream: "tsynMap (plus 1)\<cdot>((<[Msg 3, Msg 4, Msg 3]>)\<infinity>) 
  = (<[Msg 4, Msg 5, Msg 4]>)\<infinity>"
  by (simp add: tsynmap_insert)

lemma tsynmap_tick [simp]: "x \<in> sdom\<cdot>(tsynMap F\<cdot>stream) \<Longrightarrow> x \<notin> Msg ` range F \<Longrightarrow> x = ~"
  by (metis (no_types, lifting) insert_iff subsetCE tsynabs_sdom_subset_eq tsynabs_tsyndom tsynmap_tsyndom_range)

lemma tsynmap_msg [simp]: "tsynMap f\<cdot>(\<up>tsyn) = \<up>(tsynApplyElem f tsyn)"
  apply(cases tsyn)
  by(auto simp add: tsynMap_def)

text\<open>@{term tsynApplyElem} is injective if the applied function is injective.\<close>
lemma tsynapplyelem_inj: 
  assumes "inj f"
  shows "inj (tsynApplyElem f)"
  apply (rule injI)
  apply (case_tac x)
  apply (case_tac y)
  apply (simp add: assms inj_eq)+
  by (metis tsyn.distinct(1) tsynApplyElem.elims)

text\<open>@{term tsynMap} is injective if the mapped function is injective.\<close>
lemma tsynmap_inj:
  assumes "inj f"
  shows "inj (Rep_cfun(tsynMap f))"
  apply (rule injI)
  by (simp add: assms tsynMap_def inj_eq smap_inj tsynapplyelem_inj)

text\<open>If the result of @{term tsynMap} with an injective function is equal the stream is equal.\<close>
lemma tsynmap_inj_eq:
  assumes "inj f"
    and "tsynMap f\<cdot>s = tsynMap f\<cdot>t"
  shows "s = t"
  apply (rule injD)
  using assms tsynmap_inj by blast+

lemma tsynmap_rt: "tsynMap f\<cdot>(srt\<cdot>s) = srt\<cdot>(tsynMap f\<cdot>s)"
  apply(induction s rule:tsyn_ind)
  apply auto
  apply (simp add: tsynmap_sconc_msg)
  by (simp add: tsynmap_sconc_eps)


(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynProjFst\<close>
(* ----------------------------------------------------------------------- *)

text \<open>@{term tsynProjFst} insertion lemma.\<close>
lemma tsynprojfst_insert: "tsynProjFst\<cdot>s = smap tsynFst\<cdot>s"
  by (simp add: tsynProjFst_def)

text \<open>@{term tsynProjFst} maps the empty stream on the empty stream.\<close>
lemma tsynprojfst_strict [simp]: "tsynProjFst\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynprojfst_insert)

text \<open>@{term tsynProjFst} distributes over concatenation.\<close>
lemma tsynprojfst_sconc_msg: "tsynProjFst\<cdot>(\<up>(Msg (a, b)) \<bullet> as) = \<up>(Msg a) \<bullet> (tsynProjFst\<cdot>as)"
  by (simp add: tsynprojfst_insert)
 
text \<open>@{term tsynProjFst} ignores empty time-slots.\<close>
lemma tsynprojfst_sconc_eps: "tsynProjFst\<cdot>(\<up>eps \<bullet> s) = \<up>eps \<bullet> tsynProjFst\<cdot>s"
  by (simp add: tsynprojfst_insert)

text \<open>@{term tsynProjFst} of the concatenation of two streams equals the concatenation of 
        @{term tsynProjFst} of both streams.\<close>
lemma tsynprojfst_sconc: "tsynProjFst\<cdot>(a1 \<bullet> a2) = tsynProjFst\<cdot>a1 \<bullet> tsynProjFst\<cdot>a2"
  by (simp add: smap_split tsynprojfst_insert)

text \<open>@{term tsynProjFst} creates a new one element stream where only the first message component
        is used.\<close>
lemma tsynprojfst_singleton_msg: "tsynProjFst\<cdot>(\<up>(Msg a)) = \<up>(Msg (fst a))"
  by (metis lscons_conv smap_scons strict_smap sup'_def tsynFst.simps(2) tsynProjFst_def)

text \<open>@{term tsynProjFst} does nothing on empty time slots.\<close>
lemma tsynprojfst_singleton_eps: "tsynProjFst\<cdot>(\<up>eps) = \<up>eps"
  by (simp add: tsynProjFst_def)

text \<open>@{term tsynProjFst} leaves the length of a stream unchanged.\<close>
lemma tsynprojfst_slen: "#(tsynProjFst\<cdot>s) = #s"
  by (simp add: tsynprojfst_insert)

text \<open>Abstraction of @{term tsynProjFst} equals sprojfst executed on abstracted stream.\<close>
lemma tsynprojfst_tsynabs: "tsynAbs\<cdot>(tsynProjFst\<cdot>s) = sprojfst\<cdot>(tsynAbs\<cdot>s)"
  proof (induction s rule: tsyn_ind)
    case adm
    then show ?case 
      by simp
  next
    case bot
    then show ?case 
      by simp
  next
    case (msg m s)
    obtain a where pair_def: "\<exists>b. m = (a, b)"
      by (meson surj_pair)
    obtain b where m_def: "m = (a, b)"
      using pair_def by blast
    then show ?case
      by (simp add: m_def tsynprojfst_sconc_msg tsynabs_sconc_msg msg.IH)
  next
    case (eps s)
    then show ?case
      by (simp add: tsynprojfst_sconc_eps tsynabs_sconc_eps)
  qed

text \<open>@{term tsynProjFst} leaves the length of a time abstracted stream unchanged.\<close>
lemma tsynprojfst_tsynlen: "tsynLen\<cdot>(tsynProjFst\<cdot>ts) = tsynLen\<cdot>ts"
proof (induction ts rule: tsyn_ind)
  case adm
  then show ?case by simp
next
  case bot
  then show ?case by simp
next
  case (msg m s)
  obtain a  where b_def: "\<exists>b. m = (a, b)" 
    by fastforce
  obtain b where m_def: "m = (a, b)"
    using b_def by auto
  then show ?case 
    by (simp add: m_def tsynprojfst_sconc_msg tsynlen_sconc_msg msg.IH)
next
  case (eps s)
  then show ?case by (simp add: tsynlen_sconc_eps tsynprojfst_sconc_eps)
qed

text \<open>Every value produced by @{term tsynProjFst} is in the image of @{term tsynFst}\<close>
lemma tsynprojfst_sdom: "sdom\<cdot>(tsynProjFst\<cdot>s) = tsynFst ` sdom\<cdot>s"
  apply (induction rule: tsyn_ind, simp_all)
  apply (rule admI)
  by (simp add: smap_sdom tsynprojfst_insert)+

text \<open>Every message produced by @{term tsynProjFst} is in the image of @{term fst}\<close>
lemma tsynprojfst_tsyndom: "tsynDom\<cdot>(tsynProjFst\<cdot>s) = fst ` tsynDom\<cdot>s"
  by (simp add: tsynabs_tsyndom tsynprojfst_tsynabs sprojfst_def smap_sdom)

text \<open>@{term tsynProjFst} test on finite stream.\<close>
lemma tsynprojfst_test_finstream:
  "tsynProjFst\<cdot>(<[Msg (1, 2), Msg (3, 2), eps, eps, Msg (2, 1), eps]>) 
     = (<[Msg 1, Msg 3, eps, eps, Msg 2, eps]>)"
  by (simp add: tsynprojfst_insert)

text \<open>@{term tsynProjFst} test on infinitely many time-slots.\<close>
lemma tsynprojfst_test_infstream: 
  "tsynProjFst\<cdot>((<[ Msg (1, 2), eps]>)\<infinity>) = (<[Msg 1, eps]>)\<infinity>"
  by(simp add: tsynprojfst_insert)

(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynProjSnd\<close>
(* ----------------------------------------------------------------------- *)

text \<open>@{term tsynProjSnd} insertion lemma.\<close>
lemma tsynprojsnd_insert: "tsynProjSnd\<cdot>s = smap tsynSnd\<cdot>s"
  by (simp add: tsynProjSnd_def)

text \<open>@{term tsynProjSnd} maps the empty stream on the empty stream.\<close>
lemma tsynprojsnd_strict [simp]: "tsynProjSnd\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynprojsnd_insert)

text \<open>@{term tsynProjSnd} distributes over concatenation.\<close>
lemma tsynprojsnd_sconc_msg: 
   "tsynProjSnd\<cdot>(\<up>(Msg (a, b)) \<bullet> as) = \<up>(Msg b) \<bullet> (tsynProjSnd\<cdot>as)"
  by (simp add: tsynprojsnd_insert)
 
text \<open>@{term tsynProjSnd} ignores empty time-slots.\<close>
lemma tsynprojsnd_sconc_eps: "tsynProjSnd\<cdot>(\<up>eps \<bullet> s) = \<up>eps \<bullet> tsynProjSnd\<cdot>s"
  by (simp add: tsynprojsnd_insert)

text \<open>@{term tsynProjSnd} of the concatenation of two streams equals the concatenation of 
        @{term tsynProjSnd} of both streams.\<close>
lemma tsynprojsnd_sconc: "tsynProjSnd\<cdot>(a1 \<bullet> a2) = tsynProjSnd\<cdot>a1 \<bullet> tsynProjSnd\<cdot>a2"
  by (simp add: smap_split tsynprojsnd_insert)

text \<open>@{term tsynProjSnd} creates a new one element stream where only the first message component
        is used.\<close>
lemma tsynprojsnd_singleton_msg: "tsynProjSnd\<cdot>(\<up>(Msg a)) = \<up>(Msg (snd a))"
  by (metis lscons_conv smap_scons strict_smap sup'_def tsynSnd.simps(2) tsynProjSnd_def)

text \<open>@{term tsynProjSnd} ignores empty time slots.\<close>
lemma tsynprojsnd_singleton_eps: "tsynProjSnd\<cdot>(\<up>eps) = \<up>eps"
  by (simp add: tsynProjSnd_def)

text \<open>@{term tsynProjSnd} leaves the length of a stream unchanged.\<close>
lemma tsynprojsnd_slen: "#(tsynProjSnd\<cdot>s) = #s"
  by (simp add: tsynprojsnd_insert)

lemma tsynprojsnd_tsynlen: "tsynLen\<cdot>(tsynProjSnd\<cdot>ts) = tsynLen\<cdot>ts"
proof (induction ts rule: tsyn_ind)
  case adm
  then show ?case by simp
next
  case bot
  then show ?case by simp
next
  case (msg m s)
  obtain b  where b_def: "\<exists>a. m = (a, b)" 
    by (meson surj_pair)
  obtain a where m_def: "m = (a, b)"
    using b_def by auto
  then show ?case 
    by (simp add: m_def tsynprojsnd_sconc_msg tsynlen_sconc_msg msg.IH)
next
  case (eps s)
  then show ?case by (simp add: tsynlen_sconc_eps tsynprojsnd_sconc_eps)
qed

text \<open>Abstraction of @{term tsynProjSnd} equals sprojsnd executed on abstracted stream.\<close>
lemma tsynprojsnd_tsynabs: "tsynAbs\<cdot>(tsynProjSnd\<cdot>s) = sprojsnd\<cdot>(tsynAbs\<cdot>s)"
  proof (induction s rule: tsyn_ind)
    case adm
    then show ?case 
      by simp
  next
    case bot
    then show ?case 
      by simp
  next
    case (msg m s)
    obtain a where pair_def: "\<exists>b. m = (a, b)"
      by (meson surj_pair)
    obtain b where m_def: "m = (a, b)"
      using pair_def by blast
    then show ?case
      by (simp add: m_def tsynprojsnd_sconc_msg tsynabs_sconc_msg msg.IH)
  next
    case (eps s)
    then show ?case
      by (simp add: tsynprojsnd_sconc_eps tsynabs_sconc_eps)
  qed

text \<open>Every value produced by @{term tsynProjSnd} is in the image of @{term tsynSnd}\<close>
lemma tsynprojsnd_sdom: "sdom\<cdot>(tsynProjSnd\<cdot>s) = tsynSnd ` sdom\<cdot>s"
  apply (induction rule: tsyn_ind, simp_all)
  apply (rule admI)
  by (simp add: smap_sdom tsynprojsnd_insert)+

text \<open>Every message produced by @{term tsynProjSnd} is in the image of @{term snd}\<close>
lemma tsynprojsnd_tsyndom: "tsynDom\<cdot>(tsynProjSnd\<cdot>s) = snd ` tsynDom\<cdot>s"
  by (simp add: tsynabs_tsyndom tsynprojsnd_tsynabs sprojsnd_def smap_sdom)

text \<open>@{term tsynProjSnd} test on finite stream.\<close>
lemma tsynprojsnd_test_finstream: 
  "tsynProjSnd\<cdot>(<[Msg (1, 2), Msg (3, 2), eps, eps, Msg (2, 1), eps]>) 
     = (<[Msg 2, Msg 2, eps, eps, Msg 1, eps]>)"
  by (simp add: tsynprojsnd_insert)

text \<open>@{term tsynProjSnd} test on infinitely many time-slots.\<close>
lemma tsynprojsnd_test_infstream: 
  "tsynProjSnd\<cdot>((<[ Msg (1, 2), eps]>)\<infinity>) = (<[Msg 2, eps]>)\<infinity>"
  by (simp add: tsynprojsnd_insert)

(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynZip\<close>
(* ----------------------------------------------------------------------- *)

declare tsynZip.simps [simp del]

text \<open>@{term tsynZip} is strict.\<close>
lemma tsynzip_strict [simp]: 
  "tsynZip\<cdot>\<epsilon>\<cdot>\<epsilon> = \<epsilon>"
  "tsynZip\<cdot>\<epsilon>\<cdot>x = \<epsilon>"
  "tsynZip\<cdot>y\<cdot>\<epsilon> = \<epsilon>"
  by (fixrec_simp)+

text \<open>@{term tsynZip} distributes over concatenation.\<close>
lemma tsynzip_sconc_msg:
  "tsynZip\<cdot>(\<up>(Msg x) \<bullet> xs)\<cdot>(\<up>y \<bullet> ys) = \<up>(Msg (x,y)) \<bullet> tsynZip\<cdot>xs\<cdot>ys"
  by (metis (no_types, lifting) tsynZip.simps(3) inverseMsg.simps(2) lscons_conv tsyn.distinct(1) 
      undiscr_Discr)

text \<open>@{term tsynZip} distributes over concatenation, having the first Stream consist of one
        eps-element and the second stream is non-empty.\<close>
lemma tsynzip_sconc_eps:
  assumes "ys \<noteq> \<epsilon>"
  shows "tsynZip\<cdot>(\<up>eps \<bullet> xs)\<cdot>ys = \<up>eps \<bullet> tsynZip\<cdot>xs\<cdot>ys"
  by (metis (no_types, hide_lams) assms tsynZip.simps(3) lscons_conv scases undiscr_Discr)

text \<open>@{term tsynZip} of the concatenation of two streams equals the concatenation of 
       @{term tsynZip} of both streams.\<close>
lemma tsynzip_sconc:
  assumes "#as < \<infinity>"
    and "as \<noteq> \<epsilon>"
    and "sfoot as = (\<M> a)"
    and "tsynLen\<cdot>as = #bs"
  shows "tsynZip\<cdot>(as \<bullet> xs)\<cdot>(bs \<bullet> ys) = tsynZip\<cdot>as\<cdot>bs \<bullet> tsynZip\<cdot>xs\<cdot>ys"
  using assms 
  proof (induction as arbitrary: a bs xs ys rule: tsyn_finind)
    case fin
    then show ?case
      by (simp add: assms)
  next
    case bot
    then show ?case 
      by (simp add: assms)
  next
    case (msg m s)
    hence s_fin: "#s < \<infinity>"
      using leI msg.prems(1) by fastforce
    have s_nempty_sfoot: "s \<noteq> \<epsilon> \<Longrightarrow> sfoot s = sfoot (\<up>(\<M> m) \<bullet> s)"
      by (metis Zero_lnless_infty inf_ub less_lnsuc linorder_not_le lnat.injects msg.prems(1) 
          order_eq_iff sconc_snd_empty sfoot_conc slen_scons strict_slen)
    then show ?case 
      proof (cases rule: scases [of bs])
        case bottom
        then show ?thesis 
          by (metis lnat.con_rews lnzero_def msg.prems(4) only_empty_has_length_0 tsynlen_sconc_msg)
      next
        case (scons a t)
        have tsynlen_slen_eq: "#\<^sub>-s = #t"
          by (metis lnat.sel_rews(2) msg.prems(4) scons slen_scons tsynlen_sconc_msg)
        hence "tsynZip\<cdot>(s \<bullet> xs)\<cdot>(t \<bullet> ys) = tsynZip\<cdot>s\<cdot>t \<bullet> tsynZip\<cdot>xs\<cdot>ys"
          using s_fin msg.IH msg.prems(3) s_nempty_sfoot by fastforce
        then show ?thesis
          by (simp add: scons tsynzip_sconc_msg)
      qed
  next
    case (eps s)
    hence s_fin: "#s < \<infinity>"
      using leI eps.prems(1) by fastforce
    have s_nempty_sfoot: "s \<noteq> \<epsilon> \<Longrightarrow> sfoot s = sfoot (\<up>eps \<bullet> s)"
      by (metis Zero_lnless_infty inf_ub less_lnsuc linorder_not_le lnat.injects eps.prems(1) 
          order_eq_iff sconc_snd_empty sfoot_conc slen_scons strict_slen)
    then show ?case 
      proof (cases rule: scases [of bs])
        case bottom
        then show ?thesis 
          using eps.prems(1) eps.prems(3) eps.prems(4) tsynlen_sfoot_msg_geq by force
      next
        case (scons a t)
        have tsynlen_slen_eq: "#\<^sub>-s = #bs"
          by (metis eps.prems(4) tsynlen_sconc_eps)
        hence "tsynZip\<cdot>(s \<bullet> xs)\<cdot>(bs \<bullet> ys) = tsynZip\<cdot>s\<cdot>bs \<bullet> tsynZip\<cdot>xs\<cdot>ys" 
          using eps.IH eps.prems(3) s_nempty_sfoot s_fin by fastforce
        then show ?thesis 
          by (simp add: scons tsynzip_sconc_eps)
      qed
  qed

text \<open>@{term tsynZip} zips a non-empty singleton stream to a pair with the first element
        of the second stream.\<close>
lemma tsynzip_singleton_msg_first: "tsynZip\<cdot>(\<up>(Msg a))\<cdot>(\<up>b \<bullet> bs) = \<up>(Msg (a, b))"
  by (metis lscons_conv sup'_def tsynZip.simps(1) tsynzip_sconc_msg)

text\<open>@{term tsynZip} zips a non-empty tsyn stream to a pair with the element of the second
       singleton stream.\<close>
lemma tsynzip_singleton_msg_second: "tsynZip\<cdot>(\<up>(Msg a) \<bullet> as)\<cdot>(\<up>b) = \<up>(Msg (a, b))"
  by (metis lscons_conv sup'_def tsynzip_sconc_msg tsynzip_strict(3))

text \<open>@{term tsynZip} Empty singleton streams are zipping to eps.\<close>
lemma tsynzip_singleton_eps_first: 
  assumes "s \<noteq> \<epsilon>"
  shows "tsynZip\<cdot>(\<up>~)\<cdot>s = \<up>~"
  by (metis (no_types, lifting) assms lscons_conv sup'_def tsynZip.simps(1) tsynzip_sconc_eps)

text\<open>@{term tsynZip} zips a tsyn stream beginning with eps to a pair of eps concatenated with
       the zipping of rest of the tsyn stream and the singleton stream\<close>
lemma tsynzip_singleton_eps_second: "tsynZip\<cdot>(\<up>~ \<bullet> as)\<cdot>(\<up>b) = \<up>~ \<bullet> tsynZip\<cdot>as\<cdot>(\<up>b)"
  by (simp add: tsynzip_sconc_eps)

text \<open>@{term tsynZip} keeps the length of the finite stream.\<close>
lemma tsynzip_slen: "#bs = \<infinity> \<Longrightarrow> #(tsynZip\<cdot>as\<cdot>bs) = #as"
  proof (induction as arbitrary: bs rule: tsyn_ind)
    case adm 
    then show ?case 
      apply (rule admI)
      by (simp add: contlub_cfun_fun contlub_cfun_arg)
  next
    case bot
    then show ?case by simp
  next
    case (eps s)
    then show ?case 
      by (simp add: only_empty_has_length_0 tsynzip_sconc_eps)
  next
    case (msg m s)
    then show ?case
      by (metis (no_types, lifting) inf_scase slen_scons tsynzip_sconc_msg)
  qed 

text \<open>Abstraction of @{term tsynZip} equals szip executed on abstracted stream.\<close>
lemma tsynzip_tsynabs: "tsynAbs\<cdot>(tsynZip\<cdot>as\<cdot>bs) = szip\<cdot>(tsynAbs\<cdot>as)\<cdot>bs"
  apply (induction as arbitrary: bs rule: tsyn_ind, simp_all)
  apply (rename_tac x y z)
  apply (rule_tac x = z in scases, simp_all)
  apply (simp add: tsynzip_sconc_msg tsynabs_sconc_msg)
  apply (rename_tac x y)
  apply (case_tac "y = \<epsilon>", simp_all)
  by (simp add: tsynzip_sconc_eps tsynabs_sconc_eps)

text \<open>@{term tsynZip} keeps the length of the finite stream.\<close>
lemma tsynzip_tsynlen: "#bs = \<infinity> \<Longrightarrow> tsynLen\<cdot>(tsynZip\<cdot>as\<cdot>bs) = tsynLen\<cdot>as"
  by (simp add: tsynLen_def tsynzip_tsynabs)

text \<open>@{term tsynProjFst} of @{term tsynZip} equals the first stream, if the length of it is
        less than or equal to the length of the second stream.\<close>
lemma tsynzip_tsynprojfst: 
  assumes "#as \<le> #bs"
  shows "tsynProjFst\<cdot>(tsynZip\<cdot>as\<cdot>bs) = as"
  using assms
  apply (induction as arbitrary: bs rule: tsyn_ind, simp_all)
  apply (rule adm_all)
  apply (rule adm_imp, simp_all)
  apply (rule admI)
  apply (metis dual_order.antisym inf_chainl4 inf_ub l42)
  apply (rename_tac xs ys)
  apply (case_tac "ys = \<epsilon>", simp_all)
  apply (metis lnsuc_lnle_emb srt_decrements_length surj_scons tsynprojfst_sconc_msg 
         tsynzip_sconc_msg)
  apply (rename_tac xs ys)
  apply (case_tac "ys = \<epsilon>", simp_all)
  by (metis (no_types, lifting) less_lnsuc trans_lnle tsynprojfst_sconc_eps tsynzip_sconc_eps)

text \<open>Abstraction of @{term tsynProjFst} of @{term tsynZip} equals the abstraction of the first 
        stream if the number of messages of the first stream is less than or equal to the length of 
        the second stream.\<close>
lemma tsynzip_tsynprojfst_tsynabs:
  assumes "tsynLen\<cdot>as \<le> #bs"
  shows "tsynAbs\<cdot>(tsynProjFst\<cdot>(tsynZip\<cdot>as\<cdot>bs)) = tsynAbs\<cdot>as"
  using assms
  apply (induction as arbitrary: bs rule: tsyn_ind, simp_all)
  apply (rule adm_all, rule adm_imp, simp_all)
  apply (rule admI)
  apply (meson dual_order.trans is_ub_thelub lnle_def monofun_cfun_arg)
  apply (rename_tac xs ys)
  apply (rule_tac x = ys in scases, simp_all)
  apply (simp add: tsynlen_insert)
  apply (simp add: tsynabs_sconc_msg tsynlen_sconc_msg tsynprojfst_sconc_msg tsynzip_sconc_msg)
  apply (rename_tac xs ys)
  apply (case_tac "ys = \<epsilon>")
  apply (simp add: tsynlen_insert)
  by (simp add: tsynabs_sconc_eps tsynlen_sconc_eps tsynprojfst_tsynabs tsynzip_tsynabs)

text \<open>Abstraction of @{term tsynProjSnd} of @{term tsynZip} equals the second stream if its length
        is less than or equal to the number of messages in the second stream.\<close> 
lemma tsynzip_tsynprojsnd_tsynabs:
  assumes "#bs \<le> tsynLen\<cdot>as"
  shows "tsynAbs\<cdot>(tsynProjSnd\<cdot>(tsynZip\<cdot>as\<cdot>bs)) = bs"
  using assms
  apply (induction bs arbitrary: as rule: ind, simp_all)
  apply (rule adm_all, rule adm_imp, simp_all)
  apply (rule admI)
  apply (metis dual_order.antisym inf_chainl4 inf_ub l42)
  by (simp add: szip_sprojsnd tsynlen_insert tsynprojsnd_tsynabs tsynzip_tsynabs)

text \<open>@{term sdom} of @{term tsynZip} is subset of the @{term image} of @{term Msg} 
        on the Cartesian product of @{term tsynDom} of the first stream 
        and @{term sdom} of the second stream @{term union} eps.\<close>
lemma tsynzip_sdom: "sdom\<cdot>(tsynZip\<cdot>as\<cdot>bs) \<subseteq> (Msg ` (tsynDom\<cdot>as \<times> sdom\<cdot>bs)) \<union> {eps}"  
  apply (induction as arbitrary: bs rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_eq_Union, blast)
  apply (rule_tac x = bs in scases, simp_all)
  apply (simp add: tsynzip_sconc_msg tsyndom_sconc_msg, blast)
  by (metis (no_types) insert_absorb2 insert_is_Un insert_mono sdom2un tsynZip.simps(2) tsynzip_sconc_eps tsyndom_sconc_eps)

text \<open>@{term tsynDom} of @{term tsynZip} is subset of the Cartesian product of @{term tsynDom} 
        of the first stream and @{term sdom} of the second stream.\<close>
lemma tsynzip_tsyndom: "tsynDom\<cdot>(tsynZip\<cdot>as\<cdot>bs) \<subseteq> (tsynDom\<cdot>as \<times> sdom\<cdot>bs)"
  by (simp add: szip_sdom tsynabs_tsyndom tsynzip_tsynabs)

text \<open>@{term tsynZip} test on finite streams.\<close>
lemma tsynzip_test_finstream: 
  "tsynZip\<cdot>(<[Msg 1, eps, Msg 2, Msg 3, eps]>)\<cdot>(<[4, 2, 3]>) 
     = <[Msg (1,4), eps, Msg (2,2), Msg (3,3)]>"
  apply (simp add: tsynzip_sconc_msg tsynzip_sconc_eps)
  by (metis lscons_conv sup'_def tsynZip.simps(2) tsynzip_sconc_msg)

text \<open>@{term tsynZip} test on infinite streams.\<close>
lemma tsynzip_test_infstream: 
  "tsynZip\<cdot>(<[Msg 1, eps]>\<infinity>)\<cdot>(\<up>2\<infinity>) = <[Msg (1,2),eps]>\<infinity>"
  apply (subst rek2sinftimes [of "tsynZip\<cdot>(<[Msg 1, eps]>\<infinity>)\<cdot>(\<up>2\<infinity>)" "<[Msg (1,2), eps]>"])
  apply (simp_all)
  apply (subst sinftimes_unfold, simp)
  apply (subst sinftimes_unfold [of "\<up>2"])
  by (simp add: tsynzip_sconc_msg tsynzip_sconc_eps)

(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynRemDups\<close>
(* ----------------------------------------------------------------------- *)

text \<open>@{term tsynRemDups} insertion lemma.\<close>
lemma tsynremdups_insert: "tsynRemDups\<cdot>s = sscanlA tsynRemDups_h eps\<cdot>s"
  by (simp add: tsynRemDups_def)

text \<open>@{term tsynRemDups} is strict.\<close>
lemma tsynremdups_strict [simp]: "tsynRemDups\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynremdups_insert)

text \<open>@{term tsynRemDups} distributes over concatenation.\<close>
lemma tsynremdups_sconc_msg:
  "tsynRemDups\<cdot>(\<up>(Msg a) \<bullet> as) = \<up>(Msg a) \<bullet> sscanlA tsynRemDups_h (Msg a)\<cdot>as"
  by (simp add: tsynremdups_insert)
 
text \<open>@{term tsynRemDups} ignores empty time-slots.\<close>
lemma tsynremdups_sconc_eps: "tsynRemDups\<cdot>(\<up>eps \<bullet> s) = \<up>eps \<bullet> tsynRemDups\<cdot>s"
  by (simp add: tsynremdups_insert)

text \<open>@{term tsynRemDups} does nothing on a singleton stream as there can't be a duplicate.\<close>
lemma tsynremdups_singleton_msg: "tsynRemDups\<cdot>(\<up>(Msg a)) = \<up>(Msg a)"
  by (metis sconc_snd_empty sscanla_bot tsynremdups_sconc_msg)

text \<open>@{term tsynRemDups} ignores empty time-slots.\<close>
lemma tsynremdups_singleton_eps: "tsynRemDups\<cdot>(\<up>eps) = \<up>eps"
  by (simp add: tsynRemDups_def)

text \<open>@{term tsynRemDups} leaves the length of a stream unchanged.\<close>
lemma tsynremdups_slen: "#(tsynRemDups\<cdot>s) = #s"
  by (simp add: tsynremdups_insert)

lemma tsynremdups_h_tsynlen: "tsynLen\<cdot>(sscanlA tsynRemDups_h a\<cdot>s) \<le> tsynLen\<cdot>s"
proof (induction s arbitrary: a rule: tsyn_ind)
  case adm
  then show ?case
    by (simp add: admI contlub_cfun_arg lub_mono2)
next
  case bot
  then show ?case by simp
next
  case (msg m s)
  then show ?case 
    apply (simp add: sscanla_step)
    apply (auto)
    apply (simp add: tsynlen_sconc_eps tsynlen_sconc_msg)
    using dual_order.trans less_lnsuc apply blast
    by (simp add: tsynlen_sconc_msg)
next
  case (eps s)
  then show ?case by (simp add: tsynremdups_sconc_eps tsynlen_sconc_eps)
qed

text \<open>@{term tsynRemDups} leaves the length of a tsyn-stream unchanged.\<close>
lemma tsynremdups_tsynlen: "tsynLen \<cdot> (tsynRemDups\<cdot>ts) <= tsynLen \<cdot>ts"
proof (induction ts rule: tsyn_ind)
  case adm
  then show ?case by (simp add: admI contlub_cfun_arg lub_mono2)
next
  case bot
  then show ?case by simp
next
  case (eps s)
  then show ?case by (simp add: tsynlen_sconc_eps tsynremdups_sconc_eps)
next
  case (msg m s)
  then show ?case 
    apply (simp add: tsynremdups_sconc_msg)
    apply (simp add: tsynlen_sconc_msg)
    apply (rule tsynremdups_h_tsynlen)
    done
qed

text \<open>Abstraction of @{term sscanlA} execution on @{term tsynRemDups_h} on the state (\<M> m) 
        equals srcdups executed on abstracted stream stepping with m.\<close>
lemma tsynremdups_h_tsynabs:
  "tsynAbs\<cdot>(sscanlA tsynRemDups_h (\<M> m)\<cdot>s) = srcdups\<cdot>(sdropwhile (\<lambda>x. x = m)\<cdot>(tsynAbs\<cdot>s))"
  apply (induction s arbitrary: m rule: tsyn_ind, simp_all)
  by (simp_all add: tsynabs_sconc_eps tsynremdups_sconc_eps tsynabs_sconc_msg 
                    tsynremdups_sconc_msg srcdups_step)

text \<open>Abstraction of @{term tsynRemDups} equals srcdups executed on abstracted stream.\<close>
lemma tsynremdups_tsynabs: "tsynAbs\<cdot>(tsynRemDups\<cdot>s) = srcdups\<cdot>(tsynAbs\<cdot>s)"
  apply (induction s rule: tsyn_ind, simp_all)
  by (simp_all add: tsynabs_sconc_eps tsynremdups_sconc_eps tsynabs_sconc_msg 
      tsynremdups_sconc_msg srcdups_step tsynremdups_h_tsynabs)

text \<open>@{term tsynRemDups_h} is subset of @{term sdom} of a stream @{term union} eps\<close>
lemma tsynremdups_h_sdom: "sdom\<cdot>(sscanlA tsynRemDups_h (\<M> m)\<cdot>s) \<subseteq> sdom\<cdot>s \<union> {eps}"
  apply (induction s arbitrary: m rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg lub_eq_Union)
  by blast+

text \<open>@{term tsynRemDups} is subset of @{term sdom} of a stream @{term union} eps\<close>
lemma tsynremdups_sdom: "sdom\<cdot>(tsynRemDups\<cdot>s) \<subseteq> sdom\<cdot>s \<union> {eps}"
  apply (induction rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg lub_eq_Union, blast)
  apply (metis (no_types, hide_lams) Un_commute Un_insert_left insert_mono sdom2un 
         sup_bot.left_neutral tsynremdups_sconc_msg tsynremdups_h_sdom)
  by (simp add: tsynremdups_sconc_eps)

text \<open>@{term tsynRemDups} doesn't change the @{term tsynDom} of a stream\<close>
lemma tsynremdups_tsyndom: "tsynDom\<cdot>(tsynRemDups\<cdot>s) = tsynDom\<cdot>s"
  by (simp add: tsynabs_tsyndom tsynremdups_tsynabs)

text \<open>@{term tsynRemDups} test on finite stream.\<close>
lemma tsynremdups_test_finstream:
  "tsynRemDups\<cdot>(<[eps, Msg (1 :: nat), Msg (1 :: nat), eps, eps, Msg (1 :: nat), Msg (2 :: nat),
   eps, Msg (2 :: nat)]>) = 
   <[eps, Msg (1 :: nat), eps, eps, eps, eps, Msg (2 :: nat), eps, eps]>"
  by (simp add: tsynremdups_insert)


text \<open>@{term tsynRemDups} test on infinitely many time-slots.\<close>
lemma tsynremdups_test_infstream:  "tsynRemDups\<cdot>(<[Msg (1 :: nat), Msg (1 :: nat)]> \<bullet> ((<[eps]>)\<infinity>)) 
  = <[Msg (1 :: nat), eps]> \<bullet> ((<[eps]>)\<infinity>)"
  apply (simp add: tsynremdups_insert)
  apply (subst rek2sinftimes [of "sscanlA tsynRemDups_h (\<M> 1::nat)\<cdot>\<up>~\<infinity>" "\<up>~\<infinity>"], simp_all)
  apply(subst s2sinftimes, simp_all)
  apply(subst sinftimes_unfold)
  by (simp add: tsynremdups_sconc_eps)
  
  
   
(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynRemDups_fix_h\<close>
(* ----------------------------------------------------------------------- *)

declare tsynRemDups_fix_h.simps [simp del]

text \<open>@{term tsynRemDups_fix} is strict.\<close>
lemma tsynremdups_fix_h_strict [simp]: "tsynRemDups_fix_h\<cdot>\<epsilon>\<cdot>option = \<epsilon>"
  by (fixrec_simp)

text \<open>@{term tsynRemDups_fix} without option ignores message.\<close>
lemma tsynremdups_fix_h_sconc_msg_none:
  "tsynRemDups_fix_h\<cdot>(\<up>(Msg a) \<bullet> as)\<cdot>None = \<up>(Msg a) \<bullet> tsynRemDups_fix_h\<cdot>as\<cdot>(Some (Discr (Msg a)))"
  by (fold lscons_conv, fixrec_simp)

text \<open>@{term tsynRemDups_fix} removes message if it is equal to the given option.\<close>
lemma tsynremdups_fix_h_sconc_msg_some_eq:
  "tsynRemDups_fix_h\<cdot>(\<up>(Msg a) \<bullet> as)\<cdot>(Some (Discr (Msg a))) 
     = \<up>eps \<bullet> tsynRemDups_fix_h\<cdot>as\<cdot>(Some (Discr (Msg a)))"
  by (fold lscons_conv, fixrec_simp)

text \<open>@{term tsynRemDups_fix} ignores message if it is not equal to the given option.\<close>
lemma tsynremdups_fix_h_sconc_msg_some_neq:
  assumes "a \<noteq> b"
  shows "tsynRemDups_fix_h\<cdot>(\<up>(Msg a) \<bullet> as)\<cdot>(Some (Discr (Msg b))) 
           = \<up>(Msg a) \<bullet> tsynRemDups_fix_h\<cdot>as\<cdot>(Some (Discr (Msg a)))"
  using assms
  by (fold lscons_conv, fixrec_simp)

text \<open>@{term tsynRemDups_fix_h} ignores empty time-slots.\<close>
lemma tsynremdups_fix_h_sconc_eps_none:
  "tsynRemDups_fix_h\<cdot>(\<up>eps \<bullet> as)\<cdot>None = \<up>eps \<bullet> tsynRemDups_fix_h\<cdot>as\<cdot>None"
  by (fold lscons_conv, fixrec_simp)

text \<open>@{term tsynRemDups_fix_h} ignores empty time-slots even with a given option.\<close>
lemma tsynremdups_fix_h_sconc_eps_some:
  "tsynRemDups_fix_h\<cdot>(\<up>eps \<bullet> as)\<cdot>(Some (Discr (Msg a))) 
    = \<up>eps \<bullet> tsynRemDups_fix_h\<cdot>as\<cdot>(Some (Discr (Msg a)))"
  by (fold lscons_conv, fixrec_simp)

text \<open>@{term tsynRemDups_fix_h} leaves the length of the stream unchanged.\<close>
lemma tsynremdups_fix_h_slen_some: "#(tsynRemDups_fix_h\<cdot>s\<cdot>(Some (Discr (\<M> m)))) = #s"
  apply (induction s arbitrary: m rule: tsyn_ind, simp_all)
  apply (rename_tac x y z)
  apply (case_tac "x = z")
  apply (simp add: tsynremdups_fix_h_sconc_msg_some_eq)
  apply (simp add: tsynremdups_fix_h_sconc_msg_some_neq)
  by (simp add: tsynremdups_fix_h_sconc_eps_some)

text \<open>@{term tsynRemDups_fix_h} leaves the length of the stream unchanged.\<close>
lemma tsynremdups_fix_h_slen_none: "#(tsynRemDups_fix_h\<cdot>s\<cdot>None) = #s"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (simp add: tsynremdups_fix_h_sconc_msg_none tsynremdups_fix_h_slen_some)
  by (simp add: tsynremdups_fix_h_sconc_eps_none)

lemma tsynremdups_fix_h_tsynlen_some: "tsynLen\<cdot>(tsynRemDups_fix_h\<cdot>s\<cdot>(Some (Discr (\<M> m)))) <= tsynLen\<cdot>s"
proof(induction s arbitrary: m rule: tsyn_ind)
case adm
  then show ?case 
    apply (rule admI)
    by (simp add: contlub_cfun_fun contlub_cfun_arg lub_mono2)
next
  case bot
  then show ?case by simp
next
  case (msg m s)
  then show ?case by (metis (no_types, lifting) dual_order.strict_implies_order inf_ub le2lnle
 lnsuc_lnle_emb order.not_eq_order_implies_strict tsynlen_sconc_msg tsynlen_sconc_eps
           tsynremdups_fix_h_sconc_msg_some_eq tsynremdups_fix_h_sconc_msg_some_neq)
next
case (eps s)
  then show ?case by (simp add: tsynlen_sconc_eps tsynremdups_fix_h_sconc_eps_some)
qed

lemma tsynremdups_fix_h_tsynlen_none: "tsynLen\<cdot>(tsynRemDups_fix_h\<cdot>s\<cdot>None) <= tsynLen\<cdot>s"
proof (induction s rule: tsyn_ind)
  case adm
  then show ?case 
    apply (rule admI)
    by (simp add: contlub_cfun_fun contlub_cfun_arg lub_mono2)
next
  case bot
  then show ?case by simp
next
  case (msg m s)
  then show ?case by (simp add: tsynlen_sconc_msg tsynremdups_fix_h_sconc_msg_none
                      tsynremdups_fix_h_tsynlen_some)
next
  case (eps s)
  then show ?case by (simp add: tsynlen_sconc_eps tsynremdups_fix_h_sconc_eps_none)
qed
  
text \<open>@{term tsynRemDups_fix_h} test on finite stream.\<close>
lemma tsynremdups_fix_h_test_finstream:
  "tsynRemDups_fix_h\<cdot>(<[eps, Msg (1 :: nat), eps, Msg (1 :: nat)]>)\<cdot>None = 
   <[eps, Msg (1 :: nat), eps, eps]>"
  by (metis (no_types, lifting) list2s_0 list2s_Suc lscons_conv sup'_def 
      tsynremdups_fix_h_sconc_msg_none tsynremdups_fix_h_sconc_msg_some_eq 
      tsynremdups_fix_h_sconc_eps_none tsynremdups_fix_h_sconc_eps_some tsynremdups_fix_h_strict)

text \<open>@{term tsynRemDups_fix_h} test on infinite stream.\<close>
lemma tsynremdups_fix_h_test_infinstream:
  "tsynRemDups_fix_h\<cdot>(<[eps, Msg (1 :: nat), eps, Msg (1 :: nat)]>\<infinity>)\<cdot>None = 
   <[eps, Msg (1 :: nat)]> \<bullet> (<[eps]>\<infinity>)"
  apply (subst sinftimes_unfold)
  apply (simp add: tsynremdups_fix_h_sconc_eps_none tsynremdups_fix_h_sconc_msg_none
                   tsynremdups_fix_h_sconc_eps_some tsynremdups_fix_h_sconc_msg_some_eq)
  apply (subst rek2sinftimes [of "tsynRemDups_fix_h\<cdot>\<up>~ \<bullet> \<up>(\<M> 1::nat) \<bullet> \<up>~ \<bullet> \<up>(\<M> 1::nat)\<infinity>\<cdot>(Some (Discr (\<M> 1::nat)))" "\<up>~\<infinity>"], simp_all)
  apply (subst sinftimes_unfold)
  oops

(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynRemDups_fix\<close>
(* ----------------------------------------------------------------------- *)

text \<open>@{term tsynRemDups_fix} insertion lemma.\<close>
lemma tsynremdups_fix_insert: "tsynRemDups_fix\<cdot>s = tsynRemDups_fix_h\<cdot>s\<cdot>None"
  by (simp add: tsynRemDups_fix_def)

text \<open>@{term tsynRemDups_fix} is strict.\<close>
lemma tsynremdups_fix_strict [simp]: "tsynRemDups_fix\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynremdups_fix_insert)

text \<open>@{term tsynRemDups_fix} distributes over concatenation.\<close>
lemma tsynremdups_fix_sconc_msg:
  "tsynRemDups_fix\<cdot>(\<up>(Msg a) \<bullet> as) = \<up>(Msg a) \<bullet> tsynRemDups_fix_h\<cdot>as\<cdot>(Some (Discr (Msg a)))"
  by (simp add: tsynremdups_fix_insert tsynremdups_fix_h_sconc_msg_none)

text \<open>@{term tsynRemDups_fix} ignores empty time-slots.\<close>
lemma tsynremdups_fix_sconc_eps: "tsynRemDups_fix\<cdot>(\<up>eps \<bullet> s) = \<up>eps \<bullet> tsynRemDups_fix_h\<cdot>s\<cdot>None"
  by (simp add: tsynremdups_fix_insert tsynremdups_fix_h_sconc_eps_none)

text \<open>@{term tsynRemDups_fix} leaves the length of a stream unchanged.\<close>
lemma tsynremdups_fix_slen: "#(tsynRemDups_fix\<cdot>s) = #s"
  by (simp add: tsynremdups_fix_insert tsynremdups_fix_h_slen_none)

lemma tsynremdups_fix_tsynlen: "tsynLen\<cdot>(tsynRemDups_fix\<cdot>s) \<le> tsynLen\<cdot>s"
proof (induction s rule: tsyn_ind)
  case adm
  then show ?case 
    apply (rule admI)
    by (simp add: contlub_cfun_fun contlub_cfun_arg lub_mono2)
next
  case bot
  then show ?case by simp
next
  case (msg m s)
  then show ?case 
    apply (simp add: tsynremdups_fix_sconc_msg tsynlen_sconc_msg)
    by (simp add: tsynremdups_fix_insert tsynremdups_fix_h_tsynlen_none tsynremdups_fix_h_tsynlen_some)
next
  case (eps s)
  then show ?case 
    apply (simp add : tsynremdups_fix_sconc_eps tsynlen_sconc_eps)
    by (simp add: tsynremdups_fix_h_tsynlen_none)
qed

text \<open>Abstraction of @{term tsynRemDups_fix} equals srcdups executed on abstracted stream.\<close>
lemma tsynremdups_fix_tsynabs: "tsynAbs\<cdot>(tsynRemDups_fix\<cdot>s) = srcdups\<cdot>(tsynAbs\<cdot>s)" 
  oops

text \<open>@{term tsynRemDups_fix} test on finite stream.\<close>
lemma tsynremdups_fix_test_finstream:
  "tsynRemDups_fix\<cdot>(<[eps, Msg (1 :: nat), eps, Msg (1 :: nat)]>) 
     = <[eps, Msg (1 :: nat), eps, eps]>"
  by (metis tsynremdups_fix_h_test_finstream tsynremdups_fix_insert)

text \<open>@{term tsynRemDups_fix} test on infinite stream.\<close>
lemma tsynremdups_fix_test_infinstream:
  "tsynRemDups_fix\<cdot>(<[eps, Msg (1 :: nat), eps, Msg (1 :: nat)]>\<infinity>) 
     = <[eps, Msg (1 :: nat)]> \<bullet> (<[eps]>\<infinity>)"
  oops
(*
  by (metis tsynremdups_fix_h_test_infinstream tsynremdups_fix_insert)
*)

text \<open>Abstraction of @{term tsynRemDups_fix} equals srcdups executed on abstracted stream.\<close>
lemma tsynremdups_fix_tsynabs: "tsynAbs\<cdot>(tsynRemDups_fix\<cdot>s) = srcdups\<cdot>(tsynAbs\<cdot>s)" 
  oops
  
(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynScanlExt\<close>
(* ----------------------------------------------------------------------- *)

text \<open>@{term tsynScanlExt} insertion lemma.\<close>
lemma tsynscanlext_insert: "tsynScanlExt f i\<cdot>s = sscanlA (tsynScanlExt_h f) i\<cdot>s"
  by (simp add: tsynScanlExt_def)

text \<open>@{term tsynScanlExt} maps the empty stream on the empty stream.\<close>
lemma tsynscanlext_strict [simp]: "tsynScanlExt f i\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynscanlext_insert)

text \<open>@{term tsynScanlExt} distributes over concatenation.\<close>
lemma tsynscanlext_sconc_msg: 
  "tsynScanlExt f i\<cdot>(\<up>(Msg a) \<bullet> as) = \<up>(Msg (fst (f i a))) \<bullet> (tsynScanlExt f (snd (f i a))\<cdot>as)"
  by (simp add: tsynscanlext_insert)

text \<open>@{term tsynScanlExt} ignores empty time-slots.\<close>
lemma tsynscanlext_sconc_eps: "tsynScanlExt f i\<cdot>(\<up>eps \<bullet> s) = \<up>eps \<bullet> (tsynScanlExt f i\<cdot>s)"
  by (simp add: tsynscanlext_insert)

text \<open>@{term tsynScanlExt} maps the singleton stream containing a message a to the
        singleton stream containing the message received by applying f to the message.\<close>
lemma tsynscanlext_singleton: "tsynScanlExt f i\<cdot>(\<up>a) = \<up>(tsynApplyElem (\<lambda>x. fst (f i x)) a)"
  by (cases a, simp_all add: tsynscanlext_insert)

text \<open>@{term tsynScanlExt} leaves the length of a stream unchanged.\<close>
lemma tsynscanlext_slen: "#(tsynScanlExt f i\<cdot>s) = #s"
  by (simp add: tsynscanlext_insert)

lemma tsynscanlext_tsynlen: "tsynLen\<cdot>(tsynScanlExt f i\<cdot>s) \<le> tsynLen\<cdot>s"
proof (induction s arbitrary: i rule: tsyn_ind)          
  case adm
  then show ?case 
    apply (rule admI)
    apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
    done
next
  case bot
  then show ?case by simp
next
  case (msg m s)
  then show ?case by (simp add: tsynscanlext_sconc_msg tsynlen_sconc_msg)
next
  case (eps s)
then show ?case  by (simp add: tsynlen_sconc_eps tsynscanlext_sconc_eps)
qed

text \<open>Abstraction of @{term tsynScanlExt} equals sscanlA executed on abstracted stream.\<close>
lemma tsynscanlext_tsynabs: "tsynAbs\<cdot>(tsynScanlExt f i\<cdot>s) = sscanlA f i\<cdot>(tsynAbs\<cdot>s)"
  apply (induction s arbitrary: i rule: tsyn_ind, simp_all)
  apply (simp add: tsynscanlext_sconc_msg tsynabs_sconc_msg)
  by (simp add: tsynscanlext_sconc_eps tsynabs_sconc_eps)

text \<open>@{term ifEqualThenZero} Auxiliary function for tsynScanlExt finite test. Checks whether
 both input nats x and y are equal and if so returns tuple of 0, otherwise returns tuple of y\<close>
fun ifEqualThenZero :: "(nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat)" where
  "ifEqualThenZero x y = (if x = y then (0, 0) else (y, y))"

text \<open>@{term tsynScanlExt} test on finite nat tsyn-stream.\<close>
lemma tsynscanlext_test_finstream:
  "tsynScanlExt ifEqualThenZero 0\<cdot>(<[Msg 5, Msg 3, Msg 3, eps]>) = <[Msg 5, Msg 3, Msg 0, eps]>"
  by (simp add: tsynscanlext_insert)


(* ----------------------------------------------------------------------- *)
  subsection \<open>sscanlA2\<close>
(* ----------------------------------------------------------------------- *)

text \<open>This lemma makes it possible to filter eps-elements from the input before applying a
        {@term sscanlA2}\<close>
lemma sscanlA2_epsfilter_input: assumes "\<And> x. (f x ~) = (x,~)" 
  shows "tsynAbs\<cdot>(sscanlAsnd f a\<cdot>s) = tsynAbs\<cdot>(sscanlAsnd f a\<cdot>(sfilter {e. e \<noteq> eps}\<cdot>s))"
  apply(induction s arbitrary: a rule: tsyn_ind)
  apply(rule admI)
  by (simp_all add: tsynabs_sconc assms contlub_cfun_arg contlub_cfun_fun lub_mono2)

(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynScanl\<close>
(* ----------------------------------------------------------------------- *)

text \<open>@{term tsynScanl} insertion lemma.\<close>
lemma tsynscanl_insert: "tsynScanl f i\<cdot>s = tsynScanlExt (\<lambda>a b. (f a b, f a b)) i\<cdot>s"
  by (simp add: tsynScanl_def)

text \<open>@{term tsynScanl} maps the empty stream on the empty stream.\<close>
lemma tsynscanl_strict [simp]: "tsynScanl f i\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynscanl_insert)

text \<open>@{term tsynScanl} maps the singleton stream containing message a to the singleton stream
containing the message received by applying f to a.\<close>
lemma tsynscanl_singleton: "tsynScanl f i\<cdot>(\<up>a) = \<up>(tsynApplyElem (f i) a)"
  by (simp add: tsynscanl_insert tsynscanlext_singleton)

text \<open>@{term tsynScanl} distributes over concatenation.\<close>
lemma tsynscanl_sconc_msg: 
  "tsynScanl f i\<cdot>(\<up>(Msg a) \<bullet> as) = \<up>(Msg (f i a)) \<bullet> (tsynScanl f (f i a)\<cdot>as)"
  by (simp add: tsynscanl_insert tsynscanlext_sconc_msg)

text \<open>@{term tsynScanl} ignores empty time-slots.\<close>
lemma tsynscanl_sconc_eps: "tsynScanl f i\<cdot>(\<up>eps \<bullet> s) = \<up>eps \<bullet> (tsynScanl f i\<cdot>s)"
  by (simp add: tsynscanl_insert tsynscanlext_sconc_eps)

text \<open>@{term tsynScanl} leaves the length of a stream unchanged.\<close>
lemma tsynscanl_slen: "#(tsynScanl f i\<cdot>s) = #s"
  by (simp add: tsynscanl_insert tsynscanlext_slen)

text \<open>@{term tsynScanl} test on finite nat tsyn-stream.\<close>
lemma tsynscanl_test_finstream: 
  "tsynScanl plus 2 \<cdot>(<[Msg 1, Msg 4]>) = <[Msg 3, Msg 7]>"
  by (simp add: tsynscanl_insert tsynscanlext_sconc_msg tsynscanlext_singleton)

text \<open>@{term tsynScanl} test on infinite nat tsyn-stream.\<close>
lemma tsynscanl_test_infinstream: 
  "tsynScanl plus 2 \<cdot>(<[Msg 1, Msg 4]> \<bullet> ((<[eps]>)\<infinity>)) = <[Msg 3, Msg 7]> \<bullet> ((<[eps]>)\<infinity>)"
  apply (simp add: tsynscanl_sconc_msg)
  apply (subst rek2sinftimes [of "tsynScanl (+) (7::'a)\<cdot>\<up>~\<infinity>" "\<up>~\<infinity>"], simp_all)
  by (metis s2sinftimes sinftimes_unfold tsynscanl_sconc_eps)

(* ----------------------------------------------------------------------- *)
  subsection \<open>sscanlA2\<close>
(* ----------------------------------------------------------------------- *)

text \<open>The length of @{term sscanlA2} without @{term ~} of input and output is the same, if the
function f does not introduce or eliminate @{term ~} from the stream.\<close>
lemma sccanla2_tsynlen:
  assumes "\<And> a. snd (f a ~) = ~"
      and "\<And> a. \<forall>m. snd (f a (\<M> m)) \<noteq> ~"
    shows "tsynLen\<cdot>(sscanlAsnd f a\<cdot>s) = tsynLen\<cdot>s"
  apply (induction s arbitrary: a rule: tsyn_ind)
  apply (rule admI)
  apply (simp_all add: assms contlub_cfun_arg contlub_cfun_fun lub_mono2)
  apply (subst (1 2) tsynlen_sconc_msg2)
  by (simp_all add: assms tsynlen_sconc_eps)

text \<open>Same as @{term sccanla2_tsynlen}, but with another formulation of the second assumption..\<close>
lemma sccanla2_tsynlen2:
  assumes "\<And> a. snd (f a ~) = ~"
      and "\<And> a m. m \<noteq> ~ ==> snd (f a m) \<noteq> ~"
    shows "tsynLen\<cdot>(sscanlAsnd f a\<cdot>s) = tsynLen\<cdot>s "
  apply (induction s arbitrary: a rule: tsyn_ind)
  apply (rule admI)
  apply (simp_all add: assms contlub_cfun_arg contlub_cfun_fun lub_mono2)
  apply (subst (1 2) tsynlen_sconc_msg2)
  by (simp_all add: assms tsynlen_sconc_eps)

(* ----------------------------------------------------------------------- *)
  subsection \<open>tsynDropWhile\<close>
(* ----------------------------------------------------------------------- *)

text \<open>@{term tsynDropWhile} insertion lemma.\<close>
lemma tsyndropwhile_insert: "tsynDropWhile f\<cdot>s = sscanlA (tsynDropWhile_h f) True\<cdot>s "
  by(simp add: tsynDropWhile_def)
    
text \<open>@{term tsynDropWhile} is strict.\<close>
lemma tsyndropwhile_strict [simp]: "tsynDropWhile f\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsyndropwhile_insert)

text \<open>If the head passes the predicate f, then the head of the result of @{term tsynDropWhile} 
        will be eps.\<close>
lemma tsyndropwhile_sconc_msg_t:
  assumes "f a"
  shows "tsynDropWhile f\<cdot>(\<up>(Msg a) \<bullet> s) = \<up>eps \<bullet> tsynDropWhile f\<cdot>s"
  using assms
  by (simp add: tsyndropwhile_insert)

text \<open>If the head fails the predicate f and is not eps, then the head of the result of 
        @{term tsynDropWhile} will start with the head of the input.\<close>
lemma tsyndropwhile_sconc_msg_f:
  assumes "\<not>f a"
  shows "tsynDropWhile f\<cdot>(\<up>(Msg a) \<bullet> s) = \<up>(Msg a) \<bullet> s"
  using assms
  apply (simp add: tsyndropwhile_insert)
  apply (induction s arbitrary: f a rule: tsyn_ind, simp_all)
  using inject_scons by fastforce+

text \<open>If the head is eps, then the head of the result of @{term tsynDropWhile} will be eps.\<close>    
lemma tsyndropwhile_sconc_eps: "tsynDropWhile f\<cdot>(\<up>eps \<bullet> s) = \<up>eps \<bullet> tsynDropWhile f\<cdot>s"
  by (simp add: tsyndropwhile_insert)
    
text \<open>If the only element in a singleton stream passes the predicate f, then @{term tsynDropWhile} 
        will produce the singleton stream with eps.\<close>
lemma tsyndropwhile_singleton_msg_t: 
  assumes "f a" shows "tsynDropWhile f\<cdot>(\<up>(Msg a)) = \<up>eps"
  using assms
  by (simp add: tsyndropwhile_insert)

text \<open>If the only element in a singleton stream fails the predicate f, then @{term tsynDropWhile} 
        does not change the stream.\<close>    
lemma tsyndropwhile_singleton_msg_f:
  assumes "\<not>f a" shows "tsynDropWhile f\<cdot>(\<up>(Msg a)) = \<up>(Msg a)"
  using assms
  by (simp add: tsyndropwhile_insert)

text \<open>If the only element in a singleton stream passes is eps, then @{term tsynDropWhile} 
        will produce the singleton stream with eps.\<close>
lemma tsyndropwhile_singleton_eps: "tsynDropWhile f\<cdot>(\<up>eps) = \<up>eps"
  by (simp add: tsyndropwhile_insert)
  
text \<open>@{term tsynDropWhile} does not change the length of a stream.\<close>
lemma tsyndropwhile_slen: "#(tsynDropWhile f\<cdot>s) = #s "
  by (simp add: tsyndropwhile_insert)

lemma tsyndropwhile_tsynlen: "tsynLen\<cdot>(tsynDropWhile f\<cdot>s) \<le> tsynLen\<cdot>s"
  proof(induction s rule: tsyn_ind)
    case adm
    then show ?case 
      apply (rule admI)
      by (simp add: contlub_cfun_fun contlub_cfun_arg lub_mono2)
  next
    case bot
    then show ?case by simp
  next
    case (msg m s)
    then show ?case 
      apply (case_tac "f m = True")
      apply (simp add: tsyndropwhile_sconc_msg_t tsynlen_sconc_eps tsynlen_sconc_msg)
      using dual_order.trans less_lnsuc apply blast
      by (simp add: tsyndropwhile_sconc_msg_f)
  next
    case (eps s)
    then show ?case by (simp add: tsyndropwhile_sconc_eps tsynlen_sconc_eps)
  qed

text \<open>Abstraction of @{term tsynDropWhile} equals sdropwhile executed on abstracted stream.\<close>
lemma tsyndropwhile_tsynabs: "tsynAbs\<cdot>(tsynDropWhile f\<cdot>s) = sdropwhile f\<cdot>(tsynAbs\<cdot>s)"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (rename_tac x y)
  apply (case_tac "f x")
  apply (simp add: tsyndropwhile_sconc_msg_t tsynabs_sconc_msg tsynabs_sconc_eps)
  apply (simp add: tsyndropwhile_sconc_msg_f tsynabs_sconc_msg)
  by (simp add: tsyndropwhile_sconc_eps tsynabs_sconc_eps)

text \<open>@{term tsynDropWhile} is idempotent.\<close>    
lemma tsyndropwhile_idem: "tsynDropWhile f\<cdot>(tsynDropWhile f\<cdot>s) = tsynDropWhile f\<cdot>s"
  apply (induction s arbitrary: f rule: tsyn_ind, simp_all)
  apply (metis tsyndropwhile_sconc_msg_f tsyndropwhile_sconc_msg_t tsyndropwhile_sconc_eps)
  by (simp add: tsyndropwhile_sconc_eps)

<<<<<<< HEAD
(* sdropwhile *)

lemma sdropwhile_neps: "sdropwhile (\<lambda>x. x = ~)\<cdot>s \<noteq> \<up>~ \<bullet> sa"
  using sdropwhile_resup by auto

lemma sdropwhile_eps_cases [case_names bot msg]:
  assumes bot: "sdropwhile (\<lambda>x. x = ~)\<cdot>x = \<epsilon> \<Longrightarrow> P \<epsilon>"
    and msg: "\<And>m s. sdropwhile (\<lambda>x. x = ~)\<cdot>x = \<up>(Msg m) \<bullet> s \<Longrightarrow> P (\<up>(Msg m) \<bullet> s)"
  shows "P (sdropwhile (\<lambda>x. x = ~)\<cdot>x)"
  using assms
  apply (rule_tac x = "sdropwhile (\<lambda>x. x = ~)\<cdot>x" in tsyn_cases)
  apply simp_all
  by (simp add: sdropwhile_neps)

lemma sdropwhile_shd_ex:
  assumes "tsynAbs\<cdot>s \<noteq> \<epsilon>"
  obtains m where "shd (sdropwhile (\<lambda>x. x = ~)\<cdot>s) = Msg m"
  by (metis assms sdropwhile_neps surj_scons tsyn.exhaust tsynabs_sdropwhile_neps)

text \<open>@{term sdom} of @{term tsynDropWhile} is subset of @{term sdom} of 
        the original stream @{term union} eps.\<close>

lemma tsyndropwhile_sdom: "sdom\<cdot>(tsynDropWhile f\<cdot>s) \<subseteq> sdom\<cdot>s \<union> {eps}"
  apply (induction s arbitrary: f rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg lub_eq_Union, blast)
  apply (metis (no_types, hide_lams) insert_commute insert_is_Un insert_subset sdom2un 
         subset_insertI2 subset_refl tsyndropwhile_sconc_msg_f tsyndropwhile_sconc_msg_t)
  by (simp add: tsyndropwhile_sconc_eps)

text \<open>@{term tsynDom} of @{term tsynDropWhile} is subset of @{term tsynDom} of 
        the original stream.\<close>
lemma tsyndropwhile_tsyndom: "tsynDom\<cdot>(tsynDropWhile f\<cdot>s) \<subseteq> tsynDom\<cdot>s" 
  by (simp add: sdropwhile_sdom tsynabs_tsyndom tsyndropwhile_tsynabs)

text \<open>@{term tsynDropWhile} test on finite stream.\<close>    
lemma tsyndropwhile_test_finstream: 
  "tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>(<[Msg 1, Msg 1, ~, Msg 1, Msg 2, Msg 1]>) 
     = <[~, ~, ~, ~, Msg 2, Msg 1]>"
  by (simp add: tsyndropwhile_insert)

text \<open>@{term tsynDropWhile} test on infinite stream.\<close>
lemma tsyndropwhile_test_infstream: 
  "tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>((<[Msg 1, ~, Msg 2]>)\<infinity>) = 
     <[~, ~, Msg 2]> \<bullet> ((<[Msg 1, ~, Msg 2]>)\<infinity>)"
proof -
  have split_stream: "(<[Msg 1, ~, Msg 2]>)\<infinity> = \<up>(Msg 1) \<bullet> \<up>~ \<bullet> \<up>(Msg 2) \<bullet> (<[Msg 1, ~, Msg 2]>\<infinity>)"
    by (metis (no_types, lifting) list2s_0 list2s_Suc lscons_conv sconc_scons' 
        sinftimes_unfold sup'_def)
  have first_elem_t: "(\<lambda> a. a \<noteq> (2 :: nat)) 1"
    by simp
  from split_stream first_elem_t have drop_first: 
      "tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>((<[Msg 1, ~, Msg 2]>)\<infinity>) =
         \<up>~ \<bullet> (tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>(\<up>~ \<bullet> \<up>(Msg 2) \<bullet> (<[Msg 1, ~, Msg 2]>\<infinity>)))"
    by (metis (mono_tags, lifting) inverseMsg.simps(2) tsyndropwhile_sconc_msg_t)      
  then have drop_second:
      "\<up>~ \<bullet> (tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>(\<up>~ \<bullet> \<up>(Msg 2) \<bullet> (<[Msg 1, ~, Msg 2]>\<infinity>))) =
         \<up>~ \<bullet> \<up>~ \<bullet>(tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>(\<up>(Msg 2) \<bullet> (<[Msg 1, ~, Msg 2]>\<infinity>)))"
    by (simp add: tsyndropwhile_sconc_eps)
  then have drop_third:
      " \<up>~ \<bullet> \<up>~ \<bullet>(tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>(\<up>(Msg 2) \<bullet> (<[Msg 1, ~, Msg 2]>\<infinity>))) = 
          \<up>~ \<bullet> \<up>~ \<bullet> \<up>(Msg 2) \<bullet> (<[Msg 1, ~, Msg 2]>\<infinity>)"
    by (simp add: tsyndropwhile_sconc_msg_f)
  from drop_first drop_second drop_third show ?thesis 
    by simp
qed

(* ----------------------------------------------------------------------- *)
  section \<open>tsynSum - CaseStudy\<close>
(* ----------------------------------------------------------------------- *)

(* ToDo: add descriptions. *)

text \<open>@{term tsynSum} maps a stream to a stream containing the sum of read messages.\<close>
definition tsynSum :: 
  "'a :: {zero, countable, monoid_add, ab_semigroup_add, plus} tsyn stream \<rightarrow> 'a tsyn stream" where
  "tsynSum = tsynScanl plus 0"

text \<open>@{term tsynSum} insertion lemma.\<close>
lemma tsynsum_insert: "tsynSum\<cdot>s = tsynScanl plus 0\<cdot>s"
  by (simp add: tsynSum_def)

text \<open>@{term tsynSum} is strict.\<close>
lemma tsynsum_strict [simp]: "tsynSum\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynsum_insert)

text \<open>@{term tsynSum} maps the stream containing only a singleton to the singleton.\<close>
lemma tsynsum_singleton: "tsynSum\<cdot>(\<up>a) = \<up>a"
  by (cases a, simp_all add: tsynsum_insert tsynscanl_singleton)

lemma "tsynScanl plus n\<cdot>(\<up>(Msg a) \<bullet> as) = \<up>(Msg (n + a)) \<bullet> tsynMap (plus a)\<cdot>(tsynScanl plus n\<cdot>as)"
  apply (induction as arbitrary: a n rule: tsyn_ind, simp_all)
  apply (simp add: tsynscanl_singleton)         
  oops

text \<open>@{term tsynSum} test on infinite stream.\<close>
lemma tsynsum_test_infmsg: "tsynSum\<cdot>(\<up>(Msg 0)\<infinity>) = \<up>(Msg 0)\<infinity>"
  by (metis add.left_neutral s2sinftimes sinftimes_unfold tsynSum_def tsynscanl_sconc_msg)

text \<open>@{term tsynSum} test on infinite stream containing no messages.\<close>
lemma tsynsum_test_infeps: "tsynSum\<cdot>(\<up>eps\<infinity>) = \<up>eps\<infinity>"
  by (metis s2sinftimes sinftimes_unfold tsynSum_def tsynscanl_sconc_eps)

text \<open>Auxiliary function for @{term tsynsum_even}.\<close>
lemma tsynsum_even_h:
  assumes "tsynDom\<cdot>s \<subseteq> {n. even n}"
    and "even m"
  shows "tsynDom\<cdot>(tsynScanl plus m\<cdot>s) \<subseteq> {n. even n}"
  using assms
  apply (induction s arbitrary: m rule: tsyn_ind)
  apply (rule adm_imp, simp_all)
  apply (rule admI)
  apply (metis ch2ch_Rep_cfunR contlub_cfun_arg subset_cont)
  apply (simp add: tsynscanl_sconc_msg tsyndom_sconc_msg)
  by (simp add: tsynscanl_sconc_eps tsyndom_sconc_eps)

text \<open>@{term tsynSum} leaves the domain unchanged if the stream contains only even messages.\<close>
lemma tsynsum_even: assumes "tsynDom\<cdot>s \<subseteq> {n. even n}"
  shows "tsynDom\<cdot>(tsynSum\<cdot>s) \<subseteq> {n. even n}"
  by (simp add: assms tsynsum_insert tsynsum_even_h)

end