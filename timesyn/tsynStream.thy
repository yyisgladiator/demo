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

(* ToDo: add abbreviation *)

text {* @{term tsynLen}: Return the number of messages. *}
definition tsynLen:: "'a tsyn stream \<rightarrow> lnat" where 
  "tsynLen \<equiv> \<Lambda> s. #(tsynAbs\<cdot>s)"

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

text{* @{term tsynProjSnd}: Access the first stream of two zipped streams. *}
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

(* ToDo: review for stream beginning with null *)

(*
fun tsynRemDups_h :: "'a tsyn \<Rightarrow> 'a tsyn \<Rightarrow> ('a tsyn \<times> 'a tsyn)" where
"tsynRemDups_h x null = (null, x)" |
"tsynRemDups_h x y = (if x = y then (null, x) else (y, y))"

definition tsynRemDups :: "'a tsyn stream \<rightarrow> 'a tsyn stream" where 
"tsynRemDups = sscanlA tsynRemDups_h null"
*)

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

(* ----------------------------------------------------------------------- *)
  section {* Fixrec-Definitions on Time-Synchronous Streams *}
(* ----------------------------------------------------------------------- *)

(* Fixrec-Example *)

(* ToDo: add description. *)

fixrec tsynRemDups_h :: "'a tsyn stream \<rightarrow> 'a tsyn discr option \<rightarrow> 'a tsyn stream" where
  "tsynRemDups_h\<cdot>\<epsilon>\<cdot>option = \<epsilon>" |
  "tsynRemDups_h\<cdot>(up\<cdot>a && as)\<cdot>None = (
     if (undiscr a) = null then up\<cdot>a && tsynRemDups_h\<cdot>as\<cdot>None
     else up\<cdot>a && tsynRemDups_h\<cdot>as\<cdot>(Some a)
  )" |
  "tsynRemDups_h\<cdot>(up\<cdot>a && as)\<cdot>(Some b) = (
     if a = b then up\<cdot>(Discr null) && tsynRemDups_h\<cdot>as\<cdot>(Some b)
     else up\<cdot>a && tsynRemDups_h\<cdot>as\<cdot>(Some a)
  )"

lemma tsynRemDups_h_sconc_msg: assumes "a \<noteq> null"
  shows " tsynRemDups_h\<cdot>(\<up>(Msg a) \<bullet> as)\<cdot>None = \<up>(Msg a) \<bullet> tsynRemDups_h\<cdot>as\<cdot>(Some (Discr (Msg a)))"
  by (metis lscons_conv tsyn.distinct(1) tsynRemDups_h.simps(2) undiscr_Discr)

lemma tsynRemDups_h_sconc_null: "tsynRemDups_h\<cdot>(\<up>null \<bullet> as)\<cdot>None = \<up>null \<bullet> tsynRemDups_h\<cdot>as\<cdot>None"
  by (fold lscons_conv, simp)

(* ----------------------------------------------------------------------- *)
  section {* Lemmata on Time-Synchronous Streams *}
(* ----------------------------------------------------------------------- *)

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
lemma tsyndom_sconc_null [simp]: "tsynDom\<cdot>(\<up>null \<bullet> s) = tsynDom\<cdot>s"
  by (metis (no_types, lifting) Collect_cong Un_insert_left tsyn.distinct(1) insert_iff sdom2un 
      sup_bot.left_neutral tsyndom_insert)

(* ----------------------------------------------------------------------- *)
  subsection {* tsynAbs *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynAbs} insertion lemma. *}
lemma tsynabs_insert: "tsynAbs\<cdot>s = smap tsynAbsElem\<cdot>(sfilter {e. e \<noteq> null}\<cdot>s)"
  by (simp add: tsynAbs_def)

text {* @{term tsynAbs} test on infinite stream. *}
lemma tsynabs_test_infstream: "tsynAbs\<cdot>((<[Msg 1, Msg 2, null, Msg 3]>)\<infinity>) = (<[1,2,3]>)\<infinity>"
  by (simp add: tsynabs_insert)

text {* @{term tsynAbs} test on finite stream. *}
lemma tsynabs_test_finstream: "tsynAbs\<cdot>(<[Msg 1, Msg 2, null, null, Msg 1, null]>) = <[1,2,1]>"
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

text {* Length of @{term tsynAbs} is smaller or equal to the length of the original stream.  *}
lemma tsynabs_slen: "#(tsynAbs\<cdot>s) \<le> #s"
  by (simp add: slen_sfilterl1 tsynabs_insert)

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
  by (simp add: tsynMap_def)

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
  by (simp add: smap_split tsynMap_def)

text {* @{term tsynMap} leaves the length of a stream unchanged. *}
lemma tsynmap_slen: "#(tsynMap f\<cdot>s) = #s"
  by (simp add: tsynmap_insert)

(* ----------------------------------------------------------------------- *)
  subsection {* tsynProjFst *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynProjFst} insertion lemma. *}
lemma tsynprojfst_insert: "tsynProjFst\<cdot>x = smap tsynFst\<cdot>x"
  by (simp add: tsynProjFst_def)

text {* @{term tsynProjFst} test on infinitely many time-slots. *}
lemma tsynprojfst_test_infstream: 
  "tsynProjFst\<cdot>(sinftimes (<[ Msg (1, 2), null]>)) = sinftimes (<[Msg 1, null]>)"
  by(simp add: tsynprojfst_insert)

text {* @{term tsynProjFst} test on finite stream. *}
lemma tsynprojfst_test_finstream:
  "tsynProjFst\<cdot>(<[Msg (1, 2), Msg (3, 2), null, null, Msg (2, 1), null]>) 
     = (<[Msg 1, Msg 3, null, null, Msg 2, null]>)"
  by (simp add: tsynprojfst_insert)

text {* @{term tsynProjFst} maps the empty stream on the empty stream. *}
lemma tsynprojfst_strict [simp]: "tsynProjFst\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynprojfst_insert)

(* ----------------------------------------------------------------------- *)
  subsection {* tsynProjSnd *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynProjSnd} insertion lemma. *}
lemma tsynprojsnd_insert: "tsynProjSnd\<cdot>x = smap tsynSnd\<cdot>x"
  by (simp add: tsynProjSnd_def)

text {* @{term tsynProjSnd} test on infinitely many time-slots. *}
lemma tsynprojsnd_test_infstream: 
  "tsynProjSnd\<cdot>(sinftimes (<[ Msg (1, 2), null]>)) = sinftimes (<[Msg 2, null]>)"
  by (simp add: tsynprojsnd_insert)

text {* @{term tsynProjSnd} test on finite stream. *}
lemma tsynprojsnd_test_finstream: 
  "tsynProjSnd\<cdot>(<[Msg (1, 2), Msg (3, 2), null, null, Msg (2, 1), null]>) 
     = (<[Msg 2, Msg 2, null, null, Msg 1, null]>)"
  by (simp add: tsynprojsnd_insert)

text {* @{term tsynProjSnd} maps the empty stream on the empty stream. *}
lemma tsynprojsnd_strict [simp]: "tsynProjSnd\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynprojsnd_insert)

(* ----------------------------------------------------------------------- *)
  subsection {* tsynRemDups *}
(* ----------------------------------------------------------------------- *)

(*
text {* @{term tsynRemDups} insertion lemma. *}
lemma tsynremdups_insert: "tsynRemDups\<cdot>x = sscanlA tsynRemDups_sscanlA_h null\<cdot>x"
  by (simp add: tsynRemDups_def)

text {* @{term tsynRemDups} test on finite stream. *}
lemma tsynremdups_test_finstream: 
  "tsynRemDups\<cdot>(<[Msg (1 :: nat), Msg 1, null, null, Msg 1, Msg 2, null]>) = 
  <[Msg 1, null, null, null, null, Msg 2, null]>"
  by (simp add: tsynRemDups_def)

text {* @{term tsynRemDups} is strict. *}
lemma tsynremdups_strict: "tsynRemDups\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynRemDups_def)

text {* @{term tsynRemDups} test on infinitely many time-slots. *}
lemma tsynremdups_test_infstream: "tsynRemDups\<cdot>(sinftimes (<[Msg 1, Null]>)) = <[Msg 1]>"
  apply (simp add: tsynremdups_insert)
  oops
*)

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
  
text {* Length of @{term tsynFilter} is equal to the length of the original stream. *}
lemma tsynfilter_slen: "#((tsynFilter A)\<cdot>s) = #s"
  by (simp add: tsynfilter_insert)

(* ----------------------------------------------------------------------- *)
  subsection {* tsynScanl *}
(* ----------------------------------------------------------------------- *)

(* ToDo: add descriptions. *)

lemma tsynscanlext_insert: "tsynScanlExt f i\<cdot>s = sscanlA (tsynScanlExt_h f) i\<cdot>s"
  by (simp add: tsynScanlExt_def)

lemma tsynscanlext_strict [simp]: "tsynScanlExt f i\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynscanlext_insert)

lemma tsynscanlext_singleton: "tsynScanlExt f i\<cdot>(\<up>a) = \<up>(tsynApplyElem (\<lambda>x. fst (f i x)) a)"
  by (cases a, simp_all add: tsynscanlext_insert)

lemma tsynscanlext_sconc_msg: 
  "tsynScanlExt f i\<cdot>(\<up>(Msg a) \<bullet> as) = \<up>(Msg (fst (f i a))) \<bullet> (tsynScanlExt f (snd (f i a))\<cdot>as)"
  by (simp add: tsynscanlext_insert)

lemma tsynscanlext_sconc_null: "tsynScanlExt f i\<cdot>(\<up>null \<bullet> s) = \<up>null \<bullet> (tsynScanlExt f i\<cdot>s)"
  by (simp add: tsynscanlext_insert)

lemma tsynscanlext_slen: "#(tsynScanlExt f i\<cdot>s) = #s"
  by (simp add: tsynscanlext_insert)

lemma tsynscanl_insert: "tsynScanl f i\<cdot>s = tsynScanlExt (\<lambda>a b. (f a b, f a b)) i\<cdot>s"
  by (simp add: tsynScanl_def)

lemma tsynscanl_strict [simp]: "tsynScanl f i\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: tsynscanl_insert)

lemma tsynscanl_singleton: "tsynScanl f i\<cdot>(\<up>a) = \<up>(tsynApplyElem (f i) a)"
  by (simp add: tsynscanl_insert tsynscanlext_singleton)

lemma tsynscanl_sconc_msg: 
  "tsynScanl f i\<cdot>(\<up>(Msg a) \<bullet> as) = \<up>(Msg (f i a)) \<bullet> (tsynScanl f (f i a)\<cdot>as)"
  by (simp add: tsynscanl_insert tsynscanlext_sconc_msg)

lemma tsynscanl_sconc_null: "tsynScanl f i\<cdot>(\<up>null \<bullet> s) = \<up>null \<bullet> (tsynScanl f i\<cdot>s)"
  by (simp add: tsynscanl_insert tsynscanlext_sconc_null)

lemma tsynscanl_slen: "#(tsynScanl f i\<cdot>s) = #s"
  by (simp add: tsynscanl_insert tsynscanlext_slen)

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
  (* ToDo: adjust with tsyndom_sconc_msg *)
  apply (simp add: tsyndom_insert tsynscanl_insert tsynscanlext_insert)
  apply (smt Collect_mono_iff odd_add)
  by (simp add: tsynscanl_sconc_null)

lemma tsynsum_even: assumes "tsynDom\<cdot>s \<subseteq> {n. even n}"
  shows "tsynDom\<cdot>(tsynSum\<cdot>s) \<subseteq> {n. even n}"
  by (simp add: assms tsynsum_insert tsynsum_even_h)

end