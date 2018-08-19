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

text {* Definition of datatype @{text tsyn} that extends with a @{term null}. *}
datatype 'm tsyn = Msg 'm ( "\<M> _" 65)| null

text {* Introduce symbol @{text -} for empty time-slots called null. *}
syntax "@null" :: "'a tsyn" ("-")
translations "-" == "CONST null"

text {* Inverse of Msg. *}
fun inverseMsg :: "'a tsyn \<Rightarrow> 'a" where
  "inverseMsg null = undefined" |
  "inverseMsg (Msg m) = m"

abbreviation invMsg :: "'a tsyn \<Rightarrow> 'a"  ("\<M>\<inverse> _") where 
  "invMsg \<equiv> inverseMsg"

text {* Prove that datatype tsyn is countable. Needed, since the domain-constructor defined
        to work for countable types .*}
instance tsyn :: (countable) countable
  by countable_datatype

(* ToDo: add descriptions. *)

instantiation tsyn :: (message) message
begin
  definition ctype_tsyn :: "channel \<Rightarrow> 'a tsyn set" where 
    "ctype_tsyn c = {null} \<union> (Msg ` (ctype c))"
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
  "tsynAbsElem null = undefined " |
  "tsynAbsElem (Msg a) = a"

text {* @{term tsynAbs}: Filter the nulls and return the corresponding stream. *}
definition tsynAbs:: "'a tsyn stream \<rightarrow> 'a stream" where
  "tsynAbs \<equiv> \<Lambda> s. smap tsynAbsElem\<cdot>(sfilter {e. e \<noteq> null}\<cdot>s)"

text {* @{term tsynLen}: Return the number of messages. *}
definition tsynLen:: "'a tsyn stream \<rightarrow> lnat" where 
  "tsynLen \<equiv> \<Lambda> s. #(tsynAbs\<cdot>s)"

abbreviation tsynLen_abbr :: "'a tsyn stream \<Rightarrow> lnat" ("#\<^sub>-_" [1000] 999) where
  "#\<^sub>-s == tsynLen\<cdot>s"

text {* @{term tsynApplyElem}: Apply the function direct to the message. *}
fun tsynApplyElem :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tsyn \<Rightarrow> 'b tsyn" where
  "tsynApplyElem _ null = null" |
  "tsynApplyElem f (Msg a) = Msg (f a)"

text {* @{term tsynMap}: Apply a function to all elements of the stream. *}
definition tsynMap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tsyn stream \<rightarrow> 'b tsyn stream" where
  "tsynMap f = smap (tsynApplyElem f)"

text{* @{term tsynFst}: Access the first element of a pair. *}
fun tsynFst :: "('a \<times> 'b) tsyn \<Rightarrow> 'a tsyn" where
  "tsynFst null = null" |
  "tsynFst (Msg x) = Msg (fst x)"

text{* @{term tsynSnd}: Access the second element of a pair .*}
fun tsynSnd :: "('a \<times> 'b) tsyn \<Rightarrow> 'b tsyn" where
  "tsynSnd null = null" |
  "tsynSnd (Msg x) = Msg (snd x)"

text{* @{term tsynProjFst}: Access the first stream of two zipped streams .*}
definition tsynProjFst :: "('a \<times> 'b) tsyn stream \<rightarrow> 'a tsyn stream" where
"tsynProjFst = smap tsynFst"

text{* @{term tsynProjSnd}: Access the second stream of two zipped streams. *}
definition tsynProjSnd :: "('a \<times> 'b) tsyn stream \<rightarrow> 'b tsyn stream" where
"tsynProjSnd = smap tsynSnd"

text {* @{term tsynFilterElem}: Replace elements not inside the set with a emtpy time-slot. *}
fun tsynFilterElem :: "('a set) \<Rightarrow> 'a tsyn \<Rightarrow> 'a tsyn" where
  "tsynFilterElem _ null = null" |
  "tsynFilterElem A (Msg a) = (if a \<notin> A then null else (Msg a))"

text {* @{term tsynFilter}: Remove all elements from the stream which are not included in the given
        set. *}
definition tsynFilter :: "'a set \<Rightarrow> 'a tsyn stream \<rightarrow> 'a tsyn stream" where
  "tsynFilter A = smap (tsynFilterElem A)"

abbreviation tsynFilter_abbr :: "'a set \<Rightarrow> 'a tsyn stream \<Rightarrow> 'a tsyn stream" 
  ("(_ \<ominus>\<^sub>- _)" [66, 65] 65) where "F \<ominus>\<^sub>- s \<equiv> tsynFilter F\<cdot>s"

(* ToDo: add descriptions. *)

fun tsynRemDups_h :: "'a tsyn \<Rightarrow> 'a tsyn \<Rightarrow> ('a tsyn \<times> 'a tsyn)" where
  "tsynRemDups_h x null = (null, x)" |
  "tsynRemDups_h x y = (if x = y then (null, x) else (y, y))"

definition tsynRemDups :: "'a tsyn stream \<rightarrow> 'a tsyn stream" where 
  "tsynRemDups = sscanlA tsynRemDups_h null"

(* ToDo: add description. *)

fun tsynScanlExt_h :: "('s \<Rightarrow> 'a \<Rightarrow> ('b \<times>'s)) \<Rightarrow> 's \<Rightarrow> 'a tsyn \<Rightarrow> ('b tsyn \<times> 's)" where
  "tsynScanlExt_h f s (Msg m) = (Msg (fst (f s m)), (snd (f s m)))" |
  "tsynScanlExt_h f s null = (null, s)"

text {* @{term tsynScanlExt}: Apply a function elementwise to the input stream. Behaves like 
        @{term tsynMap}, but also takes a state as additional input to the function. For the first 
        computation an initial state is provided. *}
(* tsynScanlExt just ignores empty time-slots; If you want to return empty time-slots lift a
   function from sscanlA. *)
definition tsynScanlExt :: "('s \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's)) \<Rightarrow> 's \<Rightarrow> 'a tsyn stream \<rightarrow> 'b tsyn stream" where
  "tsynScanlExt f = sscanlA (tsynScanlExt_h f)"

text {* @{term tsynScanl}: Apply a function elementwise to the input stream. Behaves like 
  @{term tsynMap}, but also takes the previously generated output element as additional input to 
  the function. For the first computation an initial value is provided. *}
definition tsynScanl :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a tsyn stream \<rightarrow> 'b tsyn stream" where
  "tsynScanl f i = tsynScanlExt (\<lambda>a b. (f a b, f a b)) i"

(* ToDo: add description. *)

fun tsynDropWhile_h :: "('a \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> 'a tsyn \<Rightarrow> ('a tsyn \<times> bool)" where
  "tsynDropWhile_h f x null = (null, x)"|
  "tsynDropWhile_h f True (Msg x) = (if f x then (null, True) else ((Msg x), False))" |
  "tsynDropWhile_h f False (Msg x) = ((Msg x), False)"
  
definition tsynDropWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a tsyn stream \<rightarrow> 'a tsyn stream" where
  "tsynDropWhile f =  sscanlA (tsynDropWhile_h f) True"

text {* @{term tsynZip}: Merge a tysn stream with a stream. *}
fixrec tsynZip :: "'a tsyn stream \<rightarrow> 'b stream \<rightarrow> ('a \<times> 'b) tsyn stream" where
  "tsynZip\<cdot>\<epsilon>\<cdot>s = \<epsilon>" |
  "tsynZip\<cdot>s\<cdot>\<epsilon> = \<epsilon>" |
  "tsynZip\<cdot>(up\<cdot>a && as)\<cdot>(up\<cdot>b && bs) = (
     if (undiscr a) = null then \<up>null \<bullet> tsynZip\<cdot>as\<cdot>(up\<cdot>b && bs)
     else \<up>(Msg ((invMsg (undiscr a)), (undiscr b))) \<bullet> tsynZip\<cdot>as\<cdot>bs 
  )" 

(* ----------------------------------------------------------------------- *)
  section {* Fixrec-Definitions on Time-Synchronous Streams *}
(* ----------------------------------------------------------------------- *)

(* Fixrec-Example *)

(* ToDo: add description. *)

fixrec tsynRemDups_fix_h :: "'a tsyn stream \<rightarrow> 'a tsyn discr option \<rightarrow> 'a tsyn stream" where
  "tsynRemDups_fix_h\<cdot>\<epsilon>\<cdot>option = \<epsilon>" |
  "tsynRemDups_fix_h\<cdot>(up\<cdot>a && as)\<cdot>None = (
     if (undiscr a) = null then up\<cdot>a && tsynRemDups_fix_h\<cdot>as\<cdot>None
     else up\<cdot>a && tsynRemDups_fix_h\<cdot>as\<cdot>(Some a)
  )" |
  "tsynRemDups_fix_h\<cdot>(up\<cdot>a && as)\<cdot>(Some b) = (
     if (undiscr a) = null then up\<cdot>a && tsynRemDups_fix_h\<cdot>as\<cdot>(Some b)
     else (if a = b then up\<cdot>(Discr null) && tsynRemDups_fix_h\<cdot>as\<cdot>(Some b)
     else up\<cdot>a && tsynRemDups_fix_h\<cdot>as\<cdot>(Some a))
  )"

definition tsynRemDups_fix :: "'a tsyn stream \<rightarrow> 'a tsyn stream" where
  "tsynRemDups_fix \<equiv> \<Lambda> s. tsynRemDups_fix_h\<cdot>s\<cdot>None"

(* ----------------------------------------------------------------------- *)
  section {* Lemmata on Time-Synchronous Streams *}
(* ----------------------------------------------------------------------- *)

text {* Induction rule for finite time-synchronous streams. *}
lemma tsyn_finind [case_names fin bot msg null]:
  assumes fin: "#x = Fin n"
    and bot: "P \<epsilon>"
    and msg: "\<And>m s. P s \<Longrightarrow> P (\<up>(Msg m) \<bullet> s)"
    and null: "\<And>s. P s \<Longrightarrow> P (\<up>null \<bullet> s)"
  shows "P x"
  using assms
  apply (induction x rule: finind)
  apply (simp_all add: bot fin)
  by (metis bot finind slen_scons tsynAbsElem.cases)

text {* Induction rule for infinite time-synchronous streams and admissable predicates. *}
lemma tsyn_ind [case_names adm bot msg null]:
  assumes adm: "adm P"
    and bot: "P \<epsilon>"
    and msg: "\<And>m s. P s \<Longrightarrow> P (\<up>(Msg m) \<bullet> s)"
    and null: "\<And>s. P s \<Longrightarrow> P (\<up>null \<bullet> s)"
  shows "P x"
  using assms 
  apply (induction rule: ind [of _ x])
  apply (simp_all add: adm bot)
  by (metis tsyn.exhaust msg null)

text {* Cases rule for time-synchronous streams. *}
lemma tsyn_cases [case_names bot msg null]:
  assumes bot: "P \<epsilon>"
    and msg: "\<And>m s. P (\<up>(Msg m) \<bullet> s)"
    and null: "\<And> s. P (\<up>null \<bullet> s)"
  shows "P x"
  using assms
  apply (cases rule: scases [of x])
  apply (simp add: bot)
  by (metis tsyn.exhaust)

(* ----------------------------------------------------------------------- *)
  subsection {* Lemmata on Streams - Streams Extension *}
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

text {* Cardinality of the set @{term sdom} is smaller or equal to the length of the original 
        stream. *}
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

text {* If the domain of a stream is subset of another set and one takes an arbitrary element 
        of this superset, then the domain of the stream with this chosen element as first
        element is also a subset of the former superset. *}
lemma tsyndom_sconc_msg_sub2: "tsynDom\<cdot>xs \<subseteq> S \<Longrightarrow> x \<in> S \<Longrightarrow> tsynDom\<cdot>(\<up>(Msg x) \<bullet> xs) \<subseteq> S"
  by (simp add: subset_iff tsyndom_insert)

text {* @{term tsynDom} maps the empty stream on the empty set. *}
lemma tsyndom_strict: "tsynDom\<cdot>\<epsilon> = {}"
  by (simp add: tsyndom_insert)

text {* @{term tsynDom} of concatenations distributes via union of sets. *}
lemma tsyndom_sconc_msg: "tsynDom\<cdot>(\<up>(Msg a) \<bullet> as) = {a} \<union> tsynDom\<cdot>as"
  by (simp add: tsyndom_insert set_eq_iff)

text {* The empty time-slot is not part of the domain. *}
lemma tsyndom_sconc_null: "tsynDom\<cdot>(\<up>null \<bullet> s) = tsynDom\<cdot>s"
  by (metis (no_types, lifting) Collect_cong Un_insert_left tsyn.distinct(1) insert_iff sdom2un 
      sup_bot.left_neutral tsyndom_insert)

text {* @{term tsynDom} of the concatenation of two streams is equal to the union of @{term tsynDom} 
        applied to both streams. *}
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

text {* @{term tsynDom} is only a singleton set if the stream just contains one element. *}
lemma tsyndom_singleton_msg: "tsynDom\<cdot>(\<up>(Msg a)) = {a}"
  by (metis insert_is_Un lscons_conv sup'_def tsyndom_sconc_msg tsyndom_strict)

text {* @{term tsynDom} is empty if stream is null. *}
lemma tsyndom_singleton_null: "tsynDom\<cdot>(\<up>null) = {}"
  using tsyndom_sconc_null tsyndom_strict by fastforce

text {* Cardinality of the set @{term tsynDom} is smaller or equal to the length of the original 
        stream. *}
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

text {* @{term tsynDom} test on finite stream. *}
lemma tsyndom_test_finstream: "tsynDom\<cdot>(<[Msg (1 :: nat), Msg 2, null, null, Msg 1, null]>) = {1, 2}"
  apply (simp add: tsyndom_insert set_eq_iff) 
  by blast

text {* @{term tsynDom} test on infinite stream. *}
lemma tsyndom_test_infstream: "tsynDom\<cdot>((<[Msg (1 :: nat), Msg 2, null, Msg 3]>)\<infinity>) = {1, 2, 3}"
  apply (simp add:  tsyndom_insert set_eq_iff)
  by blast

(* ----------------------------------------------------------------------- *)
  subsection {* tsynAbs *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynAbs} insertion lemma. *}
lemma tsynabs_insert: "tsynAbs\<cdot>s = smap tsynAbsElem\<cdot>(sfilter {e. e \<noteq> null}\<cdot>s)"
  by (simp add: tsynAbs_def)                            

text {* @{term tsynAbs} test on infinite stream. *}
lemma tsynabs_test_infstream: "tsynAbs\<cdot>((<[Msg 1, Msg 2, null, Msg 3]>)\<infinity>) = (<[1, 2, 3]>)\<infinity>"
  by (simp add: tsynabs_insert)

text {* @{term tsynAbs} test on finite stream. *}
lemma tsynabs_test_finstream: "tsynAbs\<cdot>(<[Msg 1, Msg 2, null, null, Msg 1, null]>) = <[1, 2, 1]>"
  by (simp add: tsynabs_insert)

text {* @{term tsynAbs} maps the empty stream on the empty stream. *}
lemma tsynabs_strict [simp]: "tsynAbs\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynabs_insert)

text {* @{term tsynAbs} distributes over concatenation. *}
lemma tsynabs_sconc_msg: "tsynAbs\<cdot>(\<up>(Msg a) \<bullet> as) = \<up>a \<bullet> (tsynAbs\<cdot>as)"
  by (simp add: tsynabs_insert)

text {* @{term tsynAbs} ignores empty time-slots. *}
lemma tsynabs_sconc_null: "tsynAbs\<cdot>(\<up>null \<bullet> s) = tsynAbs\<cdot>s"
  by (simp add: tsynabs_insert)

text {* @{term tsynAbs} of the concatenation of two streams equals the concatenation of 
        @{term tsynAbs} of both streams. *}
lemma tsynabs_sconc: assumes "#as < \<infinity>" shows "tsynAbs\<cdot>(as \<bullet> bs) = tsynAbs\<cdot>as \<bullet> tsynAbs\<cdot>bs"
  by (simp add: add_sfilter2 assms smap_split tsynabs_insert)

text {* @{term tsynAbs} of a singleton stream with a message is the singleton stream with the 
        message. *}
lemma tsynabs_singleton_msg: "tsynAbs\<cdot>(\<up>(Msg a)) = \<up>a"
  by (simp add: tsynabs_insert)

text {* @{term tsynAbs} of a singleton stream with null is the empty stream. *}
lemma tsynabs_singleton_null: "tsynAbs\<cdot>(\<up>null) = \<epsilon>"
  by (simp add: tsynabs_insert)

text {* Length of @{term tsynAbs} is smaller or equal to the length of the original stream. *}
lemma tsynabs_slen: "#(tsynAbs\<cdot>s) \<le> #s"
  by (simp add: slen_sfilterl1 tsynabs_insert)

lemma tsynabs_sdom_subset_eq: "(sdom\<cdot>s \<subseteq> insert - (Msg ` range a)) = (sdom\<cdot>(tsynAbs\<cdot>s) \<subseteq> range a)"
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
    case (null s)
    then show ?case 
      by (simp only: tsynabs_sconc_null sdom2un, auto)
  qed

(* ----------------------------------------------------------------------- *)
  subsection {* tsynLen *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynLen} insertion lemma. *}
lemma tsynlen_insert: "tsynLen\<cdot>s =  #(tsynAbs\<cdot>s)"
  by (simp add: tsynLen_def)

text {* @{term tsynLen} maps the empty stream to zero. *}
lemma tsynlen_strict [simp]: "tsynLen\<cdot>\<epsilon> = 0"
  by (simp add: tsynlen_insert)

text {* If @{term tsynLen} is infinity the stream cannot be empty. *}
lemma tsynlen_inf_nbot: assumes "tsynLen\<cdot>s = \<infinity>"
  shows "s \<noteq> \<epsilon>"
  using assms by fastforce

text {* @{term tsynLen} distributes over concatenation. *}
lemma tsynlen_sconc_msg: "tsynLen\<cdot>(\<up>(Msg a) \<bullet> as) = lnsuc\<cdot>(tsynLen\<cdot>as)"
  by (simp add: tsynabs_sconc_msg tsynlen_insert)

text {* @{term tsynLen} ignores empty time slots. *}
lemma tsynlen_sconc_null: "tsynLen\<cdot>(\<up>(null) \<bullet> as) = tsynLen\<cdot>as"
  by (simp add: tsynabs_sconc_null tsynlen_insert)

text {* @{term tsynLen} of the concatenation of two streams equals the sum of @{term tsynLen} of 
        both streams if the number of messages and the first stream are finite. *}
lemma tsynlen_sconc_finite:
  assumes "#as < \<infinity>" and "tsynLen\<cdot>as = Fin k" and "tsynLen\<cdot>bs = Fin n"
  shows "tsynLen\<cdot>(as \<bullet> bs) = Fin (k + n)"
  using assms
  by (simp add: slen_sconc_all_finite tsynabs_sconc tsynlen_insert)

text {* @{term tsynLen} of the concatenation of two streams with finite many messages is less or 
        equal to the sum of @{term tsynLen} of both streams *}
lemma  tsynlen_sconc_infinite:
  assumes "tsynLen\<cdot>as = Fin n" and "tsynLen\<cdot>bs = Fin  m"
  shows "tsynLen\<cdot>(as \<bullet> bs) \<le> Fin (n + m)"
  using assms leI sconc_fst_inf tsynlen_sconc_finite by fastforce

text {* @{term tsynLen} is less or equal to the length of the stream. *}
lemma tsynlen_slen: "tsynLen\<cdot>s \<le> slen\<cdot>s"
  by (simp add: tsynabs_slen tsynlen_insert)

text {* @{term tsynLen} of the infinte concatenation of a finite stream with more than one 
        message is @{term "\<infinity>"}. *}
lemma tsynlen_inftimes_finite:
  assumes "#as < \<infinity> " and "0 < tsynLen\<cdot>as" 
  shows "tsynLen\<cdot>as\<infinity> = \<infinity>"
  by (metis (no_types, lifting) assms(1) assms(2) neq_iff rek2sinftimes sinftimes_unfold 
      slen_empty_eq slen_sinftimes tsynabs_sconc tsynlen_insert)

text {* @{term tsynLen} Non-empty singleton streams have length 1. *}
lemma tsynlen_singleton_msg: "tsynLen\<cdot>(\<up>(Msg a)) = Fin 1"
  by (simp add: tsynlen_insert tsynabs_singleton_msg)

text {* @{term tsynLen} Empty slots have length zero. *}
lemma tsynlen_singleton_null: "tsynLen\<cdot>(\<up>null) = 0"
  by (simp add: tsynabs_singleton_null tsynlen_insert)

text {* @{term tsynLen} test for finite tsyn stream. *}
lemma tsynlen_test_finstream: 
  "tsynLen\<cdot>(<[Msg 1, null, Msg 2, null, null, Msg 1]>) = Fin 3"
  by (simp add: tsynlen_insert tsynabs_sconc_msg tsynabs_sconc_null tsynabs_singleton_msg)

text {* @{term tsynLen} test for infinite tsyn stream. *}
lemma tsynlen_test_infstream: "tsynLen\<cdot>(<[null, Msg a]>\<infinity>) = \<infinity>"
  by (metis Fin_neq_inf gr_0 inf_ub less_le list2s_Suc list2streamFin lscons_conv 
      tsynlen_inftimes_finite tsynlen_sconc_msg tsynlen_sconc_null) 

(* ----------------------------------------------------------------------- *)
  subsection {* Induction variants with Length. *}
(* ----------------------------------------------------------------------- *)

text {* Cases rule for infinite time-synchronous streams. *}
lemma tsyn_cases_inf [case_names inf msg null]:
  assumes inf: "tsynLen\<cdot>s = \<infinity>"
    and msg: "\<And>a as. s= (\<up>(Msg a) \<bullet> as) \<Longrightarrow> P s"
    and null: "\<And>as. s=(\<up>null \<bullet> as) \<Longrightarrow> P s"
  shows "P s"
  using assms
  apply (cases rule: scases [of s], simp_all)
  by (metis tsynAbsElem.cases)

(* ----------------------------------------------------------------------- *)
  subsection {* tsynMap *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynMap} insertion lemma. *}
lemma tsynmap_insert: "tsynMap f\<cdot>s = smap (tsynApplyElem f)\<cdot>s"
  by (simp add: tsynMap_def)

text {* @{term tsynMap} test on infinite stream. *}
lemma tsynMap_test_infstream: "tsynMap (plus 1)\<cdot>((<[Msg 3, Msg 4, Msg 3]>)\<infinity>) 
  = (<[Msg 4, Msg 5, Msg 4]>)\<infinity>"
  by (simp add: tsynmap_insert)

text {* @{term tsynMap} test on finite stream. *}
lemma tsynMap_test_finstream: "tsynMap (plus 1)\<cdot>(<[Msg 1, Msg 2, Msg 1, null]>) 
  = <[Msg 2, Msg 3, Msg 2, null]>"
  by (simp add: tsynmap_insert)

text {* @{term tsynMap} is strict. *}
lemma tsynmap_strict [simp]: "tsynMap f\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynmap_insert)

text {* @{term tsynMap} distributes over concatenation. *}
lemma tsynmap_sconc_msg: "tsynMap f\<cdot>(\<up>(Msg m) \<bullet> s) = \<up>(Msg (f m)) \<bullet> tsynMap f\<cdot>s"
  by (simp add: tsynmap_insert)

text {* @{term tsynMap} ignores empty time-slots. *}
lemma tsynmap_sconc_null: "tsynMap f\<cdot>(\<up>null \<bullet> s) = \<up>null \<bullet> tsynMap f\<cdot>s"
  by (simp add: tsynmap_insert)

text {* @{term tsynMap} of the concatenation of two streams equals the concatenation of 
        @{term tsynMap} of both streams. *}
lemma tsynmap_sconc: "tsynMap f\<cdot>(a1 \<bullet> a2) = tsynMap f\<cdot>a1 \<bullet> tsynMap f\<cdot>a2"
  by (simp add: smap_split tsynmap_insert)

text {* @{term tsynMap} of a stream containing only one element, is just the stream 
          with the function applied to that element. *}
lemma tsynmap_singleton_msg: "tsynMap f\<cdot>(\<up>(Msg a)) = (\<up>(Msg (f a)))"
  by (simp add: tsynMap_def)

text {* @{term tsynMap} is null-stream if stream was null. *}
lemma tsynmap_singleton_null: "tsynMap f\<cdot>(\<up>null) = \<up>null"
  by (simp add: tsynMap_def)

text {* @{term tsynMap} leaves the length of a stream unchanged. *}
lemma tsynmap_slen: "#(tsynMap f\<cdot>s) = #s"
  by (simp add: tsynmap_insert)

text {* Abstraction of @{term tsynMap} equals sMap executed on abstracted stream. *}
lemma tsynmap_tsynabs: "tsynAbs\<cdot>(tsynMap f\<cdot>s) = smap f\<cdot>(tsynAbs\<cdot>s)"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (simp add: tsynmap_sconc_msg tsynabs_sconc_msg)
  by (simp add: tsynmap_sconc_null tsynabs_sconc_null)
  
(* ----------------------------------------------------------------------- *)
  subsection {* tsynProjFst *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynProjFst} insertion lemma. *}
lemma tsynprojfst_insert: "tsynProjFst\<cdot>s = smap tsynFst\<cdot>s"
  by (simp add: tsynProjFst_def)

text {* @{term tsynProjFst} test on infinitely many time-slots. *}
lemma tsynprojfst_test_infstream: 
  "tsynProjFst\<cdot>((<[ Msg (1, 2), null]>)\<infinity>) = (<[Msg 1, null]>)\<infinity>"
  by(simp add: tsynprojfst_insert)

text {* @{term tsynProjFst} test on finite stream. *}
lemma tsynprojfst_test_finstream:
  "tsynProjFst\<cdot>(<[Msg (1, 2), Msg (3, 2), null, null, Msg (2, 1), null]>) 
     = (<[Msg 1, Msg 3, null, null, Msg 2, null]>)"
  by (simp add: tsynprojfst_insert)

text {* @{term tsynProjFst} maps the empty stream on the empty stream. *}
lemma tsynprojfst_strict [simp]: "tsynProjFst\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynprojfst_insert)

text {* @{term tsynProjFst} distributes over concatenation. *}
lemma tsynprojfst_sconc_msg: "tsynProjFst\<cdot>(\<up>(Msg (a, b)) \<bullet> as) = \<up>(Msg a) \<bullet> (tsynProjFst\<cdot>as)"
  by (simp add: tsynprojfst_insert)
 
text {* @{term tsynProjFst} ignores empty time-slots. *}
lemma tsynprojfst_sconc_null: "tsynProjFst\<cdot>(\<up>null \<bullet> s) = \<up>null \<bullet> tsynProjFst\<cdot>s"
  by (simp add: tsynprojfst_insert)

text {* @{term tsynProjFst} of the concatenation of two streams equals the concatenation of 
        @{term tsynProjFst} of both streams. *}
lemma tsynprojfst_sconc: "tsynProjFst\<cdot>(a1 \<bullet> a2) = tsynProjFst\<cdot>a1 \<bullet> tsynProjFst\<cdot>a2"
  by (simp add: smap_split tsynprojfst_insert)

text {* @{term tsynProjFst} creates a new one element stream where only the first message component
        is used. *}
lemma tsynprojfst_singleton_msg: "tsynProjFst\<cdot>(\<up>(Msg a)) = \<up>(Msg (fst a))"
  by (metis lscons_conv smap_scons strict_smap sup'_def tsynFst.simps(2) tsynProjFst_def)

text {* @{term tsynProjFst} does nothing on empty time slots. *}
lemma tsynprojfst_singleton_null: "tsynProjFst\<cdot>(\<up>null) = \<up>null"
  by (simp add: tsynProjFst_def)

text {* @{term tsynProjFst} leaves the length of a stream unchanged. *}
lemma tsynprojfst_slen: "#(tsynProjFst\<cdot>s) = #s"
  by (simp add: tsynprojfst_insert)

text {* @{term tsynProjFst} leaves the length of a time abstracted stream unchanged. *}
lemma tsynprojfst_tsynlen: "tsynLen\<cdot>(tsynProjFst\<cdot>ts) = tsynLen\<cdot>ts"
  sorry

text {* Abstraction of @{term tsynProjFst} equals sprojfst executed on abstracted stream. *}
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
    case (null s)
    then show ?case
      by (simp add: tsynprojfst_sconc_null tsynabs_sconc_null)
  qed

(* ----------------------------------------------------------------------- *)
  subsection {* tsynProjSnd *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynProjSnd} insertion lemma. *}
lemma tsynprojsnd_insert: "tsynProjSnd\<cdot>s = smap tsynSnd\<cdot>s"
  by (simp add: tsynProjSnd_def)

text {* @{term tsynProjSnd} test on infinitely many time-slots. *}
lemma tsynprojsnd_test_infstream: 
  "tsynProjSnd\<cdot>((<[ Msg (1, 2), null]>)\<infinity>) = (<[Msg 2, null]>)\<infinity>"
  by (simp add: tsynprojsnd_insert)

text {* @{term tsynProjSnd} test on finite stream. *}
lemma tsynprojsnd_test_finstream: 
  "tsynProjSnd\<cdot>(<[Msg (1, 2), Msg (3, 2), null, null, Msg (2, 1), null]>) 
     = (<[Msg 2, Msg 2, null, null, Msg 1, null]>)"
  by (simp add: tsynprojsnd_insert)

text {* @{term tsynProjSnd} maps the empty stream on the empty stream. *}
lemma tsynprojsnd_strict [simp]: "tsynProjSnd\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynprojsnd_insert)

text {* @{term tsynProjSnd} distributes over concatenation. *}
lemma tsynprojsnd_sconc_msg: 
  shows "tsynProjSnd\<cdot>(\<up>(Msg (a, b)) \<bullet> as) = \<up>(Msg b) \<bullet> (tsynProjSnd\<cdot>as)"
  by (simp add: tsynprojsnd_insert)
 
text {* @{term tsynProjSnd} ignores empty time-slots. *}
lemma tsynprojsnd_sconc_null: "tsynProjSnd\<cdot>(\<up>null \<bullet> s) = \<up>null \<bullet> tsynProjSnd\<cdot>s"
  by (simp add: tsynprojsnd_insert)

text {* @{term tsynProjSnd} of the concatenation of two streams equals the concatenation of 
        @{term tsynProjSnd} of both streams. *}
lemma tsynprojsnd_sconc: "tsynProjSnd\<cdot>(a1 \<bullet> a2) = tsynProjSnd\<cdot>a1 \<bullet> tsynProjSnd\<cdot>a2"
  by (simp add: smap_split tsynprojsnd_insert)

text {* @{term tsynProjFst} creates a new one element stream where only the first message component
        is used. *}
lemma tsynprojsnd_singleton_msg: "tsynProjSnd\<cdot>(\<up>(Msg a)) = \<up>(Msg (snd a))"
  by (metis lscons_conv smap_scons strict_smap sup'_def tsynSnd.simps(2) tsynProjSnd_def)

text {* @{term tsynProjFst} ignores empty time slots. *}
lemma tsynprojsnd_singleton_null: "tsynProjSnd\<cdot>(\<up>null) = \<up>null"
  by (simp add: tsynProjSnd_def)

text {* @{term tsynProjSnd} leaves the length of a stream unchanged. *}
lemma tsynprojsnd_slen: "#(tsynProjSnd\<cdot>s) = #s"
  by (simp add: tsynprojsnd_insert)

text {* Abstraction of @{term tsynProjSnd} equals sprojsnd executed on abstracted stream. *}
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
    case (null s)
    then show ?case
      by (simp add: tsynprojsnd_sconc_null tsynabs_sconc_null)
  qed

(* ----------------------------------------------------------------------- *)
  subsection {* tsynRemDups *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynRemDups} insertion lemma. *}
lemma tsynremdups_insert: "tsynRemDups\<cdot>s = sscanlA tsynRemDups_h null\<cdot>s"
  by (simp add: tsynRemDups_def)

text {* @{term tsynRemDups} is strict. *}
lemma tsynremdups_strict [simp]: "tsynRemDups\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynremdups_insert)

text {* @{term tsynRemDups} distributes over concatenation. *}
lemma tsynremdups_sconc_msg:
  "tsynRemDups\<cdot>(\<up>(Msg a) \<bullet> as) = \<up>(Msg a) \<bullet> sscanlA tsynRemDups_h (Msg a)\<cdot>as"
  by (simp add: tsynremdups_insert)
 
text {* @{term tsynRemDups} ignores empty time-slots. *}
lemma tsynremdups_sconc_null: "tsynRemDups\<cdot>(\<up>null \<bullet> s) = \<up>null \<bullet> tsynRemDups\<cdot>s"
  by (simp add: tsynremdups_insert)

text {* @{term tsynRemDups} does nothing on a singleton stream as there can't be a duplicate. *}
lemma tsynremdups_singleton_msg: "tsynRemDups\<cdot>(\<up>(Msg a)) = \<up>(Msg a)"
  by (metis sconc_snd_empty sscanla_bot tsynremdups_sconc_msg)

text {* @{term tsynRemDups} ignores empty time-slots. *}
lemma tsynremdups_singleton_null: "tsynRemDups\<cdot>(\<up>null) = \<up>null"
  by (simp add: tsynRemDups_def)

text {* @{term tsynRemDups} leaves the length of a stream unchanged. *}
lemma tsynremdups_slen: "#(tsynRemDups\<cdot>s) = #s"
  by (simp add: tsynremdups_insert)

text {* @{term tsynRemDups} test on finite stream. *}
lemma tsynremdups_test_finstream:
  "tsynRemDups\<cdot>(<[null, Msg (1 :: nat), Msg (1 :: nat), null, null, Msg (1 :: nat), Msg (2 :: nat),
   null, Msg (2 :: nat)]>) = 
   <[null, Msg (1 :: nat), null, null, null, null, Msg (2 :: nat), null, null]>"
  by (simp add: tsynremdups_insert)

text {* @{term tsynRemDups} test on infinitely many time-slots. *}
lemma tsynremdups_test_infstream:  "tsynRemDups\<cdot>(<[Msg (1 :: nat), Msg (1 :: nat)]> \<bullet> ((<[null]>)\<infinity>)) 
  = <[Msg (1 :: nat), null]> \<bullet> ((<[null]>)\<infinity>)"
  apply (simp add: tsynremdups_insert)
  oops

text {* Abstraction of @{term sscanlA} execution on @{term tsynRemDups_h} on the state (\<M> m) 
        equals srcdups executed on abstracted stream stepping with m. *}
lemma tsynremdups_h_tsynabs:
  "tsynAbs\<cdot>(sscanlA tsynRemDups_h (\<M> m)\<cdot>s) = srcdups\<cdot>(sdropwhile (\<lambda>x. x = m)\<cdot>(tsynAbs\<cdot>s))"
  apply (induction s arbitrary: m rule: tsyn_ind, simp_all)
  by (simp_all add: tsynabs_sconc_null tsynremdups_sconc_null tsynabs_sconc_msg 
                    tsynremdups_sconc_msg srcdups_step)

text {* Abstraction of @{term tsynRemDups} equals srcdups executed on abstracted stream. *}
lemma tsynremdups_tsynabs: "tsynAbs\<cdot>(tsynRemDups\<cdot>s) = srcdups\<cdot>(tsynAbs\<cdot>s)"
  apply (induction s rule: tsyn_ind, simp_all)
  by (simp_all add: tsynabs_sconc_null tsynremdups_sconc_null tsynabs_sconc_msg 
      tsynremdups_sconc_msg srcdups_step tsynremdups_h_tsynabs)
   
(* ----------------------------------------------------------------------- *)
  subsection {* tsynRemDups_fix_h *}
(* ----------------------------------------------------------------------- *)

declare tsynRemDups_fix_h.simps [simp del]

text {* @{term tsynRemDups} is strict. *}
lemma tsynremdups_fix_h_strict [simp]: "tsynRemDups_fix_h\<cdot>\<epsilon>\<cdot>option = \<epsilon>"
  by (fixrec_simp)

(* ToDo: add descriptions *)

lemma tsynremdups_fix_h_sconc_msg_none:
  "tsynRemDups_fix_h\<cdot>(\<up>(Msg a) \<bullet> as)\<cdot>None = \<up>(Msg a) \<bullet> tsynRemDups_fix_h\<cdot>as\<cdot>(Some (Discr (Msg a)))"
  by (fold lscons_conv, fixrec_simp)

lemma tsynremdups_fix_h_sconc_msg_some_eq:
  "tsynRemDups_fix_h\<cdot>(\<up>(Msg a) \<bullet> as)\<cdot>(Some (Discr (Msg a))) 
     = \<up>null \<bullet> tsynRemDups_fix_h\<cdot>as\<cdot>(Some (Discr (Msg a)))"
  by (fold lscons_conv, fixrec_simp)

lemma tsynremdups_fix_h_sconc_msg_some_neq:
  assumes "a \<noteq> b"
  shows "tsynRemDups_fix_h\<cdot>(\<up>(Msg a) \<bullet> as)\<cdot>(Some (Discr (Msg b))) 
           = \<up>(Msg a) \<bullet> tsynRemDups_fix_h\<cdot>as\<cdot>(Some (Discr (Msg a)))"
  using assms
  by (fold lscons_conv, fixrec_simp)

text {* @{term tsynRemDups_fix_h} ignores empty time-slots. *}
lemma tsynremdups_fix_h_sconc_null_none:
  "tsynRemDups_fix_h\<cdot>(\<up>null \<bullet> as)\<cdot>None = \<up>null \<bullet> tsynRemDups_fix_h\<cdot>as\<cdot>None"
  by (fold lscons_conv, fixrec_simp)

lemma tsynremdups_fix_h_sconc_null_some:
  "tsynRemDups_fix_h\<cdot>(\<up>null \<bullet> as)\<cdot>(Some (Discr (Msg a))) 
    = \<up>null \<bullet> tsynRemDups_fix_h\<cdot>as\<cdot>(Some (Discr (Msg a)))"
  by (fold lscons_conv, fixrec_simp)

lemma tsynremdups_fix_h_slen_some: "#(tsynRemDups_fix_h\<cdot>s\<cdot>(Some (Discr (\<M> m)))) = #s"
  apply (induction s arbitrary: m rule: tsyn_ind, simp_all)
  apply (rename_tac x y z)
  apply (case_tac "x = z")
  apply (simp add: tsynremdups_fix_h_sconc_msg_some_eq)
  apply (simp add: tsynremdups_fix_h_sconc_msg_some_neq)
  by (simp add: tsynremdups_fix_h_sconc_null_some)

lemma tsynremdups_fix_h_slen_none: "#(tsynRemDups_fix_h\<cdot>s\<cdot>None) = #s"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (simp add: tsynremdups_fix_h_sconc_msg_none tsynremdups_fix_h_slen_some)
  by (simp add: tsynremdups_fix_h_sconc_null_none)

text {* @{term tsynRemDups_fix_h} test on finite stream. *}
lemma tsynremdups_fix_h_test_finstream:
  "tsynRemDups_fix_h\<cdot>(<[null, Msg (1 :: nat), null, Msg (1 :: nat)]>)\<cdot>None = 
   <[null, Msg (1 :: nat), null, null]>"
  by (metis (no_types, lifting) list2s_0 list2s_Suc lscons_conv sup'_def 
      tsynremdups_fix_h_sconc_msg_none tsynremdups_fix_h_sconc_msg_some_eq 
      tsynremdups_fix_h_sconc_null_none tsynremdups_fix_h_sconc_null_some tsynremdups_fix_h_strict)

text {* @{term tsynRemDups_fix_h} test on infinite stream. *}
lemma tsynremdups_fix_h_test_infinstream:
  "tsynRemDups_fix_h\<cdot>(<[null, Msg (1 :: nat), null, Msg (1 :: nat)]>\<infinity>)\<cdot>None = 
   <[null, Msg (1 :: nat)]> \<bullet> (<[null]>\<infinity>)"
  oops

(* ----------------------------------------------------------------------- *)
  subsection {* tsynRemDups_fix *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynRemDups_fix} insertion lemma. *}
lemma tsynremdups_fix_insert: "tsynRemDups_fix\<cdot>s = tsynRemDups_fix_h\<cdot>s\<cdot>None"
  by (simp add: tsynRemDups_fix_def)

text {* @{term tsynRemDups_fix} is strict. *}
lemma tsynremdups_fix_strict [simp]: "tsynRemDups_fix\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynremdups_fix_insert)

text {* @{term tsynRemDups_fix} distributes over concatenation. *}
lemma tsynremdups_fix_sconc_msg:
  "tsynRemDups_fix\<cdot>(\<up>(Msg a) \<bullet> as) = \<up>(Msg a) \<bullet> tsynRemDups_fix_h\<cdot>as\<cdot>(Some (Discr (Msg a)))"
  by (simp add: tsynremdups_fix_insert tsynremdups_fix_h_sconc_msg_none)

text {* @{term tsynRemDups_fix} ignores empty time-slots. *}
lemma tsynremdups_fix_sconc_null: "tsynRemDups_fix\<cdot>(\<up>null \<bullet> s) = \<up>null \<bullet> tsynRemDups_fix_h\<cdot>s\<cdot>None"
  by (simp add: tsynremdups_fix_insert tsynremdups_fix_h_sconc_null_none)

text {* @{term tsynRemDups_fix} leaves the length of a stream unchanged. *}
lemma tsynremdups_fix_slen: "#(tsynRemDups_fix\<cdot>s) = #s"
  by (simp add: tsynremdups_fix_insert tsynremdups_fix_h_slen_none)

text {* @{term tsynRemDups_fix} test on finite stream. *}
lemma tsynremdups_fix_test_finstream:
  "tsynRemDups_fix\<cdot>(<[null, Msg (1 :: nat), null, Msg (1 :: nat)]>) 
     = <[null, Msg (1 :: nat), null, null]>"
  by (metis tsynremdups_fix_h_test_finstream tsynremdups_fix_insert)

text {* @{term tsynRemDups_fix} test on infinite stream. *}
lemma tsynremdups_fix_test_infinstream:
  "tsynRemDups_fix\<cdot>(<[null, Msg (1 :: nat), null, Msg (1 :: nat)]>\<infinity>) 
     = <[null, Msg (1 :: nat)]> \<bullet> (<[null]>\<infinity>)"
  oops
  (*
  by (metis tsynremdups_fix_h_test_infinstream tsynremdups_fix_insert)
  *)

text {* Abstraction of @{term tsynRemDups_fix} equals srcdups executed on abstracted stream. *}
lemma tsynremdups_fix_tsynabs: "tsynAbs\<cdot>(tsynRemDups_fix\<cdot>s) = srcdups\<cdot>(tsynAbs\<cdot>s)" 
  oops

(* ----------------------------------------------------------------------- *)
  subsection {* tsynFilter *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynAbs} insertion lemma. *}
lemma tsynfilter_insert: "(tsynFilter A)\<cdot>s =  smap (tsynFilterElem A)\<cdot>s"
  by (simp add: tsynFilter_def)

text {* @{term tsynFilter} test on infinitely many time-slots.*}
lemma tsynfilter_test_infstream: assumes "c \<noteq> a \<and> c \<noteq> b"
  shows "(tsynFilter {a,b})\<cdot>((<[Msg a, Msg c, null, Msg b]>)\<infinity>) = (<[Msg a, null, null, Msg b]>)\<infinity>"
  by (simp add: assms tsynfilter_insert)

text {* @{term tsynFilter} test on finite nat tsyn-stream. *}
lemma tsynfilter_test_finstream: 
  "(tsynFilter {(1::nat),2})\<cdot>(<[Msg 1, Msg 2, null, Msg 3, null, Msg 1, null, Msg 4]>) 
     = <[Msg 1, Msg 2, null, null, null, Msg 1, null, null]>"
  by (simp add: tsynfilter_insert)

text {* @{term tsynFilter} maps the empty stream on the empty stream. *}
lemma tsynfilter_strict [simp]: "(tsynFilter A)\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynfilter_insert)

text {* @{term tsynFilter} distributes over concatenation, having the first Stream consist of 
        one Msg-element included in the given set. *}
lemma tsynfilter_sconc_msg_in: assumes "m \<in> A"
   shows "(tsynFilter A)\<cdot>(\<up>(Msg m) \<bullet> as) = \<up>(Msg m) \<bullet> (tsynFilter A)\<cdot>as"
  by (simp add: assms tsynfilter_insert)

text {* @{term tsynFilter} distributes over concatenation, having the first Stream consist of one 
        Msg-element not included in the given set. *}
lemma tsynfilter_sconc_msg_nin: assumes "m \<notin> A" 
  shows"(tsynFilter A)\<cdot>(\<up>(Msg m) \<bullet> as) = \<up>(null) \<bullet> (tsynFilter A)\<cdot>as"
  by (simp add: assms tsynfilter_insert)

text {* @{term tsynFilter} distributes over concatenation, having the first Stream consist of one 
        null-element. *}
lemma tsynfilter_sconc_null: "(tsynFilter A)\<cdot>(\<up>(null)\<bullet> as) = \<up>(null) \<bullet> (tsynFilter A)\<cdot>as"
  by (simp add: tsynfilter_insert)

text {*@{term tsynFilter} of the concatenation of two streams equals the concatenation of 
        @{term tsynFilter} of both streams. *}
lemma tsynfilter_sconc: "(tsynFilter A)\<cdot>(a1 \<bullet> a2) = (tsynFilter A)\<cdot>a1 \<bullet> (tsynFilter A)\<cdot>a2"
  by (simp add: smap_split tsynfilter_insert)

text {* @{term tsynFilter} If singleton element is in the filter condition, just do nothing. *}
lemma tsynfilter_singleton_msg_in: assumes "a \<in> A"
  shows "(tsynFilter A)\<cdot>(\<up>(Msg a)) = (\<up>(Msg a))"
  by (metis assms lscons_conv sup'_def tsynfilter_sconc_msg_in tsynfilter_strict)

text {* @{term tsynFilter} If singleton element is not in the filter condition,
      return empty stream. *}
lemma tsynfilter_singleton_msg_nin:assumes "a \<notin> A"
  shows "(tsynFilter A)\<cdot>(\<up>(Msg a)) = (\<up>null)"
  by (simp add: assms tsynFilter_def)

text {* @{term tsynFilter} ignores empty time slots. *}
lemma tsynfilter_singleton_null: "(tsynFilter A)\<cdot>(\<up>null) = \<up>null"
  by (simp add: tsynFilter_def)

text {* Length of @{term tsynFilter} is equal to the length of the original stream. *}
lemma tsynfilter_slen: "#((tsynFilter A)\<cdot>s) = #s"
  by (simp add: tsynfilter_insert)

lemma tsynfilter_tsynlen: "tsynLen\<cdot>(tsynFilter A\<cdot>s) \<le> tsynLen\<cdot>s"
  sorry

text {* Abstraction of @{term tsynFilter} equals sfilter executed on abstracted stream. *}
lemma tsynfilter_tsynabs: "tsynAbs\<cdot>(tsynFilter A\<cdot>s) = sfilter A\<cdot>(tsynAbs\<cdot>s)"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (rename_tac x y)
  apply (case_tac "x \<in> A")
  apply (simp add: tsynfilter_sconc_msg_in tsynabs_sconc_msg)
  apply (simp add: tsynfilter_sconc_msg_nin tsynabs_sconc_msg tsynabs_sconc_null)
  by (simp add: tsynfilter_sconc_null tsynabs_sconc_null)

(* ----------------------------------------------------------------------- *)
  subsection {* tsynScanlExt *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynScanlExt} insertion lemma. *}
lemma tsynscanlext_insert: "tsynScanlExt f i\<cdot>s = sscanlA (tsynScanlExt_h f) i\<cdot>s"
  by (simp add: tsynScanlExt_def)

text {* @{term tsynScanlExt} maps the empty stream on the empty stream. *}
lemma tsynscanlext_strict [simp]: "tsynScanlExt f i\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynscanlext_insert)

text {* @{term tsynScanlExt} distributes over concatenation. *}
lemma tsynscanlext_sconc_msg: 
  "tsynScanlExt f i\<cdot>(\<up>(Msg a) \<bullet> as) = \<up>(Msg (fst (f i a))) \<bullet> (tsynScanlExt f (snd (f i a))\<cdot>as)"
  by (simp add: tsynscanlext_insert)

text {* @{term tsynScanlExt} ignores empty time-slots. *}
lemma tsynscanlext_sconc_null: "tsynScanlExt f i\<cdot>(\<up>null \<bullet> s) = \<up>null \<bullet> (tsynScanlExt f i\<cdot>s)"
  by (simp add: tsynscanlext_insert)

text {* @{term tsynScanlExt} maps the singleton stream containing a message a to the
        singleton stream containing the message received by applying f to the message. *}
lemma tsynscanlext_singleton: "tsynScanlExt f i\<cdot>(\<up>a) = \<up>(tsynApplyElem (\<lambda>x. fst (f i x)) a)"
  by (cases a, simp_all add: tsynscanlext_insert)

text {* @{term tsynScanlExt} leaves the length of a stream unchanged. *}
lemma tsynscanlext_slen: "#(tsynScanlExt f i\<cdot>s) = #s"
  by (simp add: tsynscanlext_insert)

text {* @{term ifEqualThenZero} Auxiliary function for tsynScanlExt finite test. Checks whether
 both input nats x and y are equal and if so returns tuple of 0, otherwise returns tuple of y*}
fun ifEqualThenZero :: "(nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat)" where
  "ifEqualThenZero x y = (if x = y then (0, 0) else (y, y))"

text {* @{term tsynScanlExt} test on finite nat tsyn-stream. *}
lemma tsynscanlext_test_finstream:
  "tsynScanlExt ifEqualThenZero 0\<cdot>(<[Msg 5, Msg 3, Msg 3, null]>) = <[Msg 5, Msg 3, Msg 0, null]>"
  by (simp add: tsynscanlext_insert)

text {* Abstraction of @{term tsynScanlExt} equals sscanlA executed on abstracted stream. *}
lemma tsynscanlext_tsynabs: "tsynAbs\<cdot>(tsynScanlExt f i\<cdot>s) = sscanlA f i\<cdot>(tsynAbs\<cdot>s)"
  apply (induction s arbitrary: i rule: tsyn_ind, simp_all)
  apply (simp add: tsynscanlext_sconc_msg tsynabs_sconc_msg)
  by (simp add: tsynscanlext_sconc_null tsynabs_sconc_null)

(* ----------------------------------------------------------------------- *)
  subsection {* tsynScanl *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynScanl} insertion lemma. *}
lemma tsynscanl_insert: "tsynScanl f i\<cdot>s = tsynScanlExt (\<lambda>a b. (f a b, f a b)) i\<cdot>s"
  by (simp add: tsynScanl_def)

text {* @{term tsynScanl} maps the empty stream on the empty stream. *}
lemma tsynscanl_strict [simp]: "tsynScanl f i\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynscanl_insert)

text {* @{term tsynScanl} maps the singleton stream containing message a to the singleton stream
containing the message received by applying f to a. *}
lemma tsynscanl_singleton: "tsynScanl f i\<cdot>(\<up>a) = \<up>(tsynApplyElem (f i) a)"
  by (simp add: tsynscanl_insert tsynscanlext_singleton)

text {* @{term tsynScanl} distributes over concatenation. *}
lemma tsynscanl_sconc_msg: 
  "tsynScanl f i\<cdot>(\<up>(Msg a) \<bullet> as) = \<up>(Msg (f i a)) \<bullet> (tsynScanl f (f i a)\<cdot>as)"
  by (simp add: tsynscanl_insert tsynscanlext_sconc_msg)

text {* @{term tsynScanl} ignores empty time-slots. *}
lemma tsynscanl_sconc_null: "tsynScanl f i\<cdot>(\<up>null \<bullet> s) = \<up>null \<bullet> (tsynScanl f i\<cdot>s)"
  by (simp add: tsynscanl_insert tsynscanlext_sconc_null)

text {* @{term tsynScanl} leaves the length of a stream unchanged. *}
lemma tsynscanl_slen: "#(tsynScanl f i\<cdot>s) = #s"
  by (simp add: tsynscanl_insert tsynscanlext_slen)

text {* @{term tsynScanl} test on finite nat tsyn-stream. *}
lemma tsynscanl_test_finstream: 
  "tsynScanl plus 2 \<cdot>(<[Msg 1, Msg 4]>) = <[Msg 3, Msg 7]>"
  by (simp add: tsynscanl_insert tsynscanlext_sconc_msg tsynscanlext_singleton)

text {* @{term tsynScanl} test on infinite nat tsyn-stream. *}
lemma tsynscanl_test_infinstream: 
  "tsynScanl plus 2 \<cdot>(<[Msg 1, Msg 4]> \<bullet> ((<[null]>)\<infinity>)) = <[Msg 3, Msg 7]> \<bullet> ((<[null]>)\<infinity>)"
  apply (simp add: tsynscanl_insert)
  oops

text {* Abstraction of @{term tsynScanl} equals sscanl executed on abstracted stream. *}
lemma tsynscanl_tsynabs: "tsynAbs\<cdot>(tsynScanl f i\<cdot>s) = sscanl f i\<cdot>(tsynAbs\<cdot>s)"
  apply (induction s arbitrary: i rule: tsyn_ind, simp_all)
  apply (simp add: tsynscanl_sconc_msg tsynabs_sconc_msg)
  by (simp add: tsynscanl_sconc_null tsynabs_sconc_null)
  
(* ----------------------------------------------------------------------- *)
  subsection {* tsynDropWhile *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynDropWhile} insertion lemma. *}
lemma tsyndropwhile_insert: "tsynDropWhile f\<cdot>s = sscanlA (tsynDropWhile_h f) True\<cdot>s "
  by(simp add: tsynDropWhile_def)
    
text {* @{term tsynDropWhile} is strict. *}
lemma tsyndropwhile_strict [simp]: "tsynDropWhile f\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsyndropwhile_insert)

text {* If the head passes the predicate f, then the head of the result of @{term tsynDropWhile} 
        will be null. *}
lemma tsyndropwhile_sconc_msg_t:
  assumes "f a"
  shows "tsynDropWhile f\<cdot>(\<up>(Msg a) \<bullet> s) = \<up>null \<bullet> tsynDropWhile f\<cdot>s"
  using assms
  by (simp add: tsyndropwhile_insert)

text {* If the head fails the predicate f and is not null, then the head of the result of 
        @{term tsynDropWhile} will start with the head of the input. *}
lemma tsyndropwhile_sconc_msg_f:
  assumes "\<not>f a"
  shows "tsynDropWhile f\<cdot>(\<up>(Msg a) \<bullet> s) = \<up>(Msg a) \<bullet> s"
  using assms
  apply (simp add: tsyndropwhile_insert)
  apply (induction s arbitrary: f a rule: tsyn_ind, simp_all)
  using inject_scons by fastforce+

text {* If the head is null, then the head of the result of @{term tsynDropWhile} will be null. *}    
lemma tsyndropwhile_sconc_null: "tsynDropWhile f\<cdot>(\<up>null \<bullet> s) = \<up>null \<bullet> tsynDropWhile f\<cdot>s"
  by (simp add: tsyndropwhile_insert)
    
text {* If the only element in a singleton stream passes the predicate f, then @{term tsynDropWhile} 
        will produce the singleton stream with null. *}
lemma tsyndropwhile_singleton_msg_t: 
  assumes "f a" shows "tsynDropWhile f\<cdot>(\<up>(Msg a)) = \<up>null"
  using assms
  by (simp add: tsyndropwhile_insert)

text {* If the only element in a singleton stream fails the predicate f, then @{term tsynDropWhile} 
        does not change the stream. *}    
lemma tsyndropwhile_singleton_msg_f:
  assumes "\<not>f a" shows "tsynDropWhile f\<cdot>(\<up>(Msg a)) = \<up>(Msg a)"
  using assms
  by (simp add: tsyndropwhile_insert)

text {* If the only element in a singleton stream passes is null, then @{term tsynDropWhile} 
        will produce the singleton stream with null. *}
lemma tsyndropwhile_singleton_null: "tsynDropWhile f\<cdot>(\<up>null) = \<up>null"
  by (simp add: tsyndropwhile_insert)
  
text {* @{term tsynDropWhile} does not change the length of a stream. *}
lemma tsyndropwhile_slen: "#(tsynDropWhile f\<cdot>s) = #s "
  by (simp add: tsyndropwhile_insert)

text {* @{term tsynDropWhile} is idempotent. *}    
lemma tsyndropwhile_idem: "tsynDropWhile f\<cdot>(tsynDropWhile f\<cdot>s) = tsynDropWhile f\<cdot>s"
  apply (induction s arbitrary: f rule: tsyn_ind, simp_all)
  apply (metis tsyndropwhile_sconc_msg_f tsyndropwhile_sconc_msg_t tsyndropwhile_sconc_null)
  by (simp add: tsyndropwhile_sconc_null)

text {* @{term tsynDropWhile} test on finite stream. *}    
lemma tsyndropwhile_test_finstream: 
  "tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>(<[Msg 1, Msg 1, -, Msg 1, Msg 2, Msg 1]>) 
     = <[-, -, -, -, Msg 2, Msg 1]>"
  by (simp add: tsyndropwhile_insert)

text {* @{term tsynDropWhile} test on infinite stream. *}
lemma tsyndropwhile_test_infstream: 
  "tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>((<[Msg 1, -, Msg 2]>)\<infinity>) = 
     <[-, -, Msg 2]> \<bullet> ((<[Msg 1, -, Msg 2]>)\<infinity>)"
proof -
  have split_stream: "(<[Msg 1, -, Msg 2]>)\<infinity> = \<up>(Msg 1) \<bullet> \<up>- \<bullet> \<up>(Msg 2) \<bullet> (<[Msg 1, -, Msg 2]>\<infinity>)"
    by (metis (no_types, lifting) list2s_0 list2s_Suc lscons_conv sconc_scons' 
        sinftimes_unfold sup'_def)
  have first_elem_t: "(\<lambda> a. a \<noteq> (2 :: nat)) 1"
    by simp
  from split_stream first_elem_t have drop_first: 
      "tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>((<[Msg 1, -, Msg 2]>)\<infinity>) =
         \<up>- \<bullet> (tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>(\<up>- \<bullet> \<up>(Msg 2) \<bullet> (<[Msg 1, -, Msg 2]>\<infinity>)))"
    by (metis (mono_tags, lifting) inverseMsg.simps(2) tsyndropwhile_sconc_msg_t)      
  then have drop_second:
      "\<up>- \<bullet> (tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>(\<up>- \<bullet> \<up>(Msg 2) \<bullet> (<[Msg 1, -, Msg 2]>\<infinity>))) =
         \<up>- \<bullet> \<up>- \<bullet>(tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>(\<up>(Msg 2) \<bullet> (<[Msg 1, -, Msg 2]>\<infinity>)))"
    by (simp add: tsyndropwhile_sconc_null)
  then have drop_third:
      " \<up>- \<bullet> \<up>- \<bullet>(tsynDropWhile (\<lambda> a. a \<noteq> (2 :: nat))\<cdot>(\<up>(Msg 2) \<bullet> (<[Msg 1, -, Msg 2]>\<infinity>))) = 
          \<up>- \<bullet> \<up>- \<bullet> \<up>(Msg 2) \<bullet> (<[Msg 1, -, Msg 2]>\<infinity>)"
    by (simp add: tsyndropwhile_sconc_msg_f)
  from drop_first drop_second drop_third show ?thesis 
    by simp
qed

text {* Abstraction of @{term tsynDropWhile} equals sdropwhile executed on abstracted stream. *}
lemma tsyndropwhile_tsynabs: "tsynAbs\<cdot>(tsynDropWhile f\<cdot>s) = sdropwhile f\<cdot>(tsynAbs\<cdot>s)"
  apply (induction s rule: tsyn_ind, simp_all)
  apply (rename_tac x y)
  apply (case_tac "f x")
  apply (simp add: tsyndropwhile_sconc_msg_t tsynabs_sconc_msg tsynabs_sconc_null)
  apply (simp add: tsyndropwhile_sconc_msg_f tsynabs_sconc_msg)
  by (simp add: tsyndropwhile_sconc_null tsynabs_sconc_null)

(* ----------------------------------------------------------------------- *)
  subsection {* tsynZip *}
(* ----------------------------------------------------------------------- *)

declare tsynZip.simps [simp del]

text {* @{term tsynZip} is strict. *}
lemma tsynzip_strict [simp]: 
  "tsynZip\<cdot>\<epsilon>\<cdot>\<epsilon> = \<epsilon>"
  "tsynZip\<cdot>\<epsilon>\<cdot>x = \<epsilon>"
  "tsynZip\<cdot>y\<cdot>\<epsilon> = \<epsilon>"
  by (fixrec_simp)+

text {* @{term tsynZip} distributes over concatenation. *}
lemma tsynzip_sconc_msg:
  "tsynZip\<cdot>(\<up>(Msg x) \<bullet> xs)\<cdot>(\<up>y \<bullet> ys) = \<up>(Msg (x,y)) \<bullet> tsynZip\<cdot>xs\<cdot>ys"
  by (metis (no_types, lifting) tsynZip.simps(3) inverseMsg.simps(2) lscons_conv tsyn.distinct(1) 
      undiscr_Discr)

text {* @{term tsynZip} distributes over concatenation, having the first Stream consist of one
        null-element and the second stream is non-empty.  *}
lemma tsynzip_sconc_null:
  assumes "ys \<noteq> \<epsilon>"
  shows "tsynZip\<cdot>(\<up>null \<bullet> xs)\<cdot>ys = \<up>null \<bullet> tsynZip\<cdot>xs\<cdot>ys"
  by (metis (no_types, hide_lams) assms tsynZip.simps(3) lscons_conv scases undiscr_Discr)

text {* If the last element of a tsyn stream is a message, tsynLen is greater than 0 *}
lemma tsynlen_sfoot_msg_geq: 
  assumes "s \<noteq> \<epsilon>" 
    and "#s = Fin n" 
    and "sfoot s = (\<M> m)" 
  shows "tsynLen\<cdot>s \<ge> Fin 1"
  using assms 
  apply(induction s arbitrary: n m rule: tsyn_finind, simp_all)
  apply(metis One_nat_def lnat.con_rews lnzero_def neq02Suclnle tsynlen_sconc_msg)
  by (metis Fin_02bot fold_inf leI lnat_well_h2 lnsuc_lnle_emb lnzero_def notinfI3 only_empty_has_length_0 sconc_snd_empty sfoot_conc sfoot_one slen_scons tsyn.distinct(1) tsynlen_sconc_null)

text {*@{term tsynZip} of the concatenation of two streams equals the concatenation of 
        @{term tsynZip} of both streams if the first stream is finite and its last element is a message
        or it's empty. *}
lemma tsynzip_sconc: 
  assumes "#as = Fin n"
    and "sfoot as = (\<M> a) \<or> as = \<epsilon>" 
    and "tsynLen\<cdot>as = #bs" 
  shows "tsynZip\<cdot>(as \<bullet> xs)\<cdot>(bs \<bullet> ys) = tsynZip\<cdot>as\<cdot>bs \<bullet> tsynZip\<cdot>xs\<cdot>ys"
  using assms 
  apply(induction as arbitrary: n a bs xs ys rule: tsyn_finind, simp_all)
proof-
  fix m :: 'a
  fix s xs :: "'a tsyn stream"
  fix bsa ys :: "'b stream"
  fix na :: nat
  fix aa :: 'a
  assume ind_ass: "\<And>(n::nat) (a::'a) (bs::'b stream) (xs::'a tsyn stream) ys::'b stream.
           #s = Fin n \<Longrightarrow> sfoot s = (\<M> a) \<or> s = \<epsilon> \<Longrightarrow>
           tsynLen\<cdot>s = #bs  \<Longrightarrow> tsynZip\<cdot>(s \<bullet> xs)\<cdot>(bs \<bullet> ys) = tsynZip\<cdot>s\<cdot>bs \<bullet> tsynZip\<cdot>xs\<cdot>ys"
    and sconc_msg_s_sfoot_eq_msg: "sfoot (\<up>(\<M> m) \<bullet> s) = \<M> aa" 
    and tsynLen_slen_bsa_ass: "tsynLen\<cdot>(\<up>(\<M> m) \<bullet> s) = #bsa" 
    and slen_lnsuc_s_fin: "lnsuc\<cdot>(#s) = Fin na"
  then obtain b bss where bsa_below_def: "bsa = \<up>b \<bullet> bss"
    by (metis lnat.con_rews lnzero_def slen_empty_eq surj_scons tsynlen_sconc_msg)
  hence tsynlen_s_slen_bss_eq: "tsynLen\<cdot>s = #bss"
    by (metis bsa_below_def inject_lnsuc slen_scons tsynLen_slen_bsa_ass tsynlen_sconc_msg)
  hence sfoot_neq_null_or_empty: "sfoot s = (\<M> aa) \<or> s = \<epsilon>"
    by (metis Fin_02bot Fin_Suc inf_less_eq leI lnzero_def notinfI3 only_empty_has_length_0 sconc_msg_s_sfoot_eq_msg sconc_snd_empty sfoot_conc slen_lnsuc_s_fin slen_sconc_snd_inf slen_scons)
  hence "tsynZip\<cdot>(s \<bullet> xs)\<cdot>(bss \<bullet> ys) = tsynZip\<cdot>s\<cdot>bss \<bullet> tsynZip\<cdot>xs\<cdot>ys" using ind_ass
    by (metis fold_inf leI lnat_well_h2 lnsuc_lnle_emb notinfI3 slen_lnsuc_s_fin tsynlen_s_slen_bss_eq)
  thus "tsynZip\<cdot>(\<up>(\<M> m) \<bullet> s \<bullet> xs)\<cdot>(bsa \<bullet> ys) = tsynZip\<cdot>(\<up>(\<M> m) \<bullet> s)\<cdot>bsa \<bullet> tsynZip\<cdot>xs\<cdot>ys"
    by (simp add: bsa_below_def tsynzip_sconc_msg)
next
  fix s xs :: "'a tsyn stream"
  fix bsa ys :: "'b stream"
  fix na :: nat
  fix aa :: 'a
  assume ind_ass: "\<And>(n::nat) (a::'a) (bs::'b stream) (xs::'a tsyn stream) ys::'b stream.
           #s = Fin n \<Longrightarrow> sfoot s = (\<M> a) \<or> s = \<epsilon> \<Longrightarrow>
           tsynLen\<cdot>s = #bs \<Longrightarrow> tsynZip\<cdot>(s \<bullet> xs)\<cdot>(bs \<bullet> ys) = tsynZip\<cdot>s\<cdot>bs \<bullet> tsynZip\<cdot>xs\<cdot>ys"
          and sconc_null_s_sfoot_eq_msg: "sfoot (\<up>- \<bullet> s) = \<M> aa" 
          and tsynLen_slen_bsa_ass: "tsynLen\<cdot>(\<up>- \<bullet> s) = #bsa" 
          and slen_lnsuc_s_fin: "lnsuc\<cdot>(#s) = Fin na" 
  hence sconc_sfoot_eq: "sfoot (\<up>- \<bullet> s) = sfoot s"
    by (metis Fin_02bot fold_inf leI lnsuc_lnle_emb lnzero_def notinfI3 only_empty_has_length_0 sconc_snd_empty sfoot_conc sfoot_one slen_scons tsyn.distinct(1))
  hence bsa_neq_empty: "bsa \<noteq> \<epsilon>"
    by (metis Fin_02bot One_nat_def Suc_n_not_le_n less2nat_lemma lnat.con_rews lnzero_def sconc_null_s_sfoot_eq_msg tsynlen_sfoot_msg_geq slen_lnsuc_s_fin slen_scons strict_slen tsynLen_slen_bsa_ass)
  hence "tsynZip\<cdot>(\<up>- \<bullet> s \<bullet> xs)\<cdot>(bsa \<bullet> ys) = \<up>- \<bullet> tsynZip\<cdot>(s \<bullet> xs)\<cdot>(bsa \<bullet> ys)"
    by (metis sconc_snd_empty strictI tsynzip_sconc_null)
  thus "tsynZip\<cdot>(\<up>- \<bullet> s \<bullet> xs)\<cdot>(bsa \<bullet> ys) = tsynZip\<cdot>(\<up>- \<bullet> s)\<cdot>bsa \<bullet> tsynZip\<cdot>xs\<cdot>ys"
    by (metis (no_types, lifting) bsa_neq_empty fold_inf ind_ass leI lnat_well_h2 lnsuc_lnle_emb notinfI3 sconc_null_s_sfoot_eq_msg sconc_scons sconc_sfoot_eq slen_lnsuc_s_fin tsynLen_slen_bsa_ass tsynlen_sconc_null tsynzip_sconc_null)
qed

text {* @{term tsynZip} zips a non-empty singleton stream to a pair with the first element
        of the second stream. *}
lemma tsynzip_singleton_msg_first: "tsynZip\<cdot>(\<up>(Msg a))\<cdot>(\<up>b \<bullet> bs) = \<up>(Msg (a, b))"
  by (metis lscons_conv sup'_def tsynZip.simps(1) tsynzip_sconc_msg)

text{* @{term tsynZip} zips a non-empty tsyn stream to a pair with the element of the second
       singleton stream. *}
lemma tsynzip_singleton_msg_second: "tsynZip\<cdot>(\<up>(Msg a) \<bullet> as)\<cdot>(\<up>b) = \<up>(Msg (a, b))"
  by (metis lscons_conv sup'_def tsynzip_sconc_msg tsynzip_strict(3))

text {* @{term tsynZip} Empty singleton streams are zipping to null. *}
lemma tsynzip_singleton_null_first: 
  assumes "s \<noteq> \<epsilon>"
  shows "tsynZip\<cdot>(\<up>-)\<cdot>s = \<up>-"
  by (metis (no_types, lifting) assms lscons_conv sup'_def tsynZip.simps(1) tsynzip_sconc_null)

text{* @{term tsynZip} zips a tsyn stream beginning with null to a pair of null concatenated with
       the zipping of rest of the tsyn stream and the singleton stream *}
lemma tsynzip_singleton_null_second: "tsynZip\<cdot>(\<up>- \<bullet> as)\<cdot>(\<up>b) = \<up>- \<bullet> tsynZip\<cdot>as\<cdot>(\<up>b)"
  by (simp add: tsynzip_sconc_null)

lemma tsynzip_slen: "#bs = \<infinity> \<Longrightarrow> #(tsynZip\<cdot>as\<cdot>bs) = #as"
  sorry

lemma tsynzip_tsynlen: "#bs = \<infinity> \<Longrightarrow> tsynLen\<cdot>(tsynZip\<cdot>as\<cdot>bs) = tsynLen\<cdot>as"
  sorry

text {* Abstraction of @{term tsynZip} equals szip executed on abstracted stream. *}
lemma tsynzip_tsynabs: "tsynAbs\<cdot>(tsynZip\<cdot>as\<cdot>bs) = szip\<cdot>(tsynAbs\<cdot>as)\<cdot>bs"
  apply (induction as arbitrary: bs rule: tsyn_ind, simp_all)
  apply (rename_tac x y z)
  apply (rule_tac x = z in scases, simp_all)
  apply (simp add: tsynzip_sconc_msg tsynabs_sconc_msg)
  apply (rename_tac x y)
  apply (case_tac "y = \<epsilon>", simp_all)
  by (simp add: tsynzip_sconc_null tsynabs_sconc_null)

lemma tsynzip_tsynprojfst: 
  assumes "#as \<le> #bs" (* or the same assumptions as tsynzip_sconc *)
  shows "tsynProjFst\<cdot>(tsynZip\<cdot>as\<cdot>bs) = as"
  oops

lemma tsynzip_tsynprojsnd_tsynabs: 
  assumes "tsynLen\<cdot>as \<ge> #bs" 
  shows "tsynAbs\<cdot>(tsynProjSnd\<cdot>(tsynZip\<cdot>as\<cdot>bs)) = bs"
  oops                         

text {* @{term tsynZip} test on finite streams. *}
lemma tsynzip_test_finstream: 
  "tsynZip\<cdot>(<[Msg 1, null, Msg 2, Msg 3, null]>)\<cdot>(<[4, 2, 3]>) 
     = <[Msg (1,4), null, Msg (2,2), Msg (3,3)]>"
  apply (simp add: tsynzip_sconc_msg tsynzip_sconc_null)
  by (metis lscons_conv sup'_def tsynZip.simps(2) tsynzip_sconc_msg)

text {* @{term tsynZip} test on infinite streams. *}
lemma tsynzip_test_infstream: 
  "tsynZip\<cdot>(<[Msg 1, null]>\<infinity>)\<cdot>(\<up>2\<infinity>) = <[Msg (1,2),null]>\<infinity>"
  apply (subst rek2sinftimes [of "tsynZip\<cdot>(<[Msg 1, null]>\<infinity>)\<cdot>(\<up>2\<infinity>)" "<[Msg (1,2), null]>"])
  apply (simp_all)
  apply (subst sinftimes_unfold, simp)
  apply (subst sinftimes_unfold [of "\<up>2"])
  by (simp add: tsynzip_sconc_msg tsynzip_sconc_null)

(* ----------------------------------------------------------------------- *)
  section {* tsynSum - CaseStudy *}
(* ----------------------------------------------------------------------- *)

(* ToDo: add descriptions. *)

definition tsynSum :: 
  "'a :: {zero, countable, monoid_add, ab_semigroup_add, plus} tsyn stream \<rightarrow> 'a tsyn stream" where
  "tsynSum = tsynScanl plus 0"

lemma tsynsum_insert: "tsynSum\<cdot>s = tsynScanl plus 0\<cdot>s"
  by (simp add: tsynSum_def)

lemma tsynsum_strict [simp]: "tsynSum\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynsum_insert)

lemma tsynsum_singleton: "tsynSum\<cdot>(\<up>a) = \<up>a"
  by (cases a, simp_all add: tsynsum_insert tsynscanl_singleton)

lemma "tsynScanl plus n\<cdot>(\<up>(Msg a) \<bullet> as) = \<up>(Msg (n + a)) \<bullet> tsynMap (plus a)\<cdot>(tsynScanl plus n\<cdot>as)"
  apply (induction as arbitrary: a n rule: tsyn_ind, simp_all)
  apply (simp add: tsynscanl_singleton)         
  oops

lemma tsynsum_test_infmsg: "tsynSum\<cdot>(\<up>(Msg 0)\<infinity>) = \<up>(Msg 0)\<infinity>"
  by (metis add.left_neutral s2sinftimes sinftimes_unfold tsynSum_def tsynscanl_sconc_msg)

lemma tsynsum_test_infnull: "tsynSum\<cdot>(\<up>null\<infinity>) = \<up>null\<infinity>"
  by (metis s2sinftimes sinftimes_unfold tsynSum_def tsynscanl_sconc_null)

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
  by (simp add: tsynscanl_sconc_null tsyndom_sconc_null)

lemma tsynsum_even: assumes "tsynDom\<cdot>s \<subseteq> {n. even n}"
  shows "tsynDom\<cdot>(tsynSum\<cdot>s) \<subseteq> {n. even n}"
  by (simp add: assms tsynsum_insert tsynsum_even_h)

end