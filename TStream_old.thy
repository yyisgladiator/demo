chapter {* Timed Streams *} 

theory TStream_old
imports Streams
begin

text {* Timed Streams*}

(* ----------------------------------------------------------------------- *)
section {* Type definition *}
(* ----------------------------------------------------------------------- *)

text {* Definition of  datatype  @{text "'m event"}; extends @{text "'m"} with a @{term "Tick"}. *}
datatype 'm event = Msg 'm | Tick

text {* Prove that datatype event is countable. Needed, since the domain-constructor defined
 to work for countable types.*}
instance event :: (countable) countable
apply countable_datatype
done

text {* Introduce symbol for ticks (@{text "\<surd>"}), marks the end of each time slot. *}
syntax
  "@Tick"     :: "'a event"       ("\<surd>")

translations
  "\<surd>"  == "CONST Tick"



text {*A timed stream is either finite (contains finitely many elements from M\<union>{\<surd>}),   
or it is infinite (contains infinitely many ticks). *}
typedef 'm tstream = "{t::'m event stream. #t \<noteq> \<infinity> \<or> #(sfilter {\<surd>}\<cdot>t) = \<infinity>}"
by (rule_tac x= "\<up>\<surd>" in exI, simp)


text {* Lifting setup, used to avoid Rep and Abs functions in typedef. 
Also forces user to prove correctness instantiation. *}

setup_lifting type_definition_tstream

text {* Example definition, empty stream. *}
lift_definition s1 :: "'m tstream" is "\<epsilon>"
by simp

text {* Example definition, stream with only one tick. *}
lift_definition s2 :: "'m tstream" is "\<up>\<surd>"
by simp

text {* The timed stream without any messages (only ticks) *}
lift_definition justtime :: "'m tstream" is "sinftimes (\<up>\<surd>)"
by simp

text {* Abbreviation *}
type_synonym ('im, 'om) tspf  = "'im tstream \<Rightarrow> 'om tstream" 

text {* Abbreviation *}
type_synonym 'im tspfo = "'im tstream \<Rightarrow> 'im tstream" 

text {* Convert a timed stream to an event list. *}
definition ts2list :: "'a tstream \<Rightarrow> 'a event list" where
"ts2list s \<equiv> if #(Rep_tstream s) \<noteq> \<infinity> then SOME l. list2s l = (Rep_tstream s) else undefined"

text {* Case study for ts2list. *}
lift_definition li1 :: "nat tstream" is "list2s [Msg 1, \<surd>]"
by simp

text {* Show that this is the stream we wanted. *}
lemma "li1 = Abs_tstream (\<up>(Msg 1) \<bullet> \<up>\<surd>)"
by (metis li1_def lscons_conv list2s_0 list2s_Suc sup'_def)

text {*Transform the timed stream back and get the initial list. *}
lemma "ts2list li1 = [Msg 1, \<surd>]"
apply (simp add: li1_def ts2list_def Abs_tstream_inverse)
by (metis (mono_tags, lifting) One_nat_def lscons_conv sconc_snd_empty list2s_0 list2s_Suc list2s_inj some_equality)



(* ----------------------------------------------------------------------- *)
section {* Definition of common functions *}
(* ----------------------------------------------------------------------- *)


text {* The functions on timed streams split into two groups:
 -Functions in the first group (prefix "ts") treat timed streams as ordinary streams. 
 -Functions in the second group (prefix "tst") work on blocks of messages.
*}

text {* Convert an event-spf to a timed-spf. Just a restriction of the function domain. *}
definition espf2tspf :: "('a event,'b event) spf \<Rightarrow> 'a tstream \<Rightarrow> 'b tstream" where
"espf2tspf f x = Abs_tstream (f\<cdot>(Rep_tstream x))"

text {* Retrieve the first element of a stream. *}
definition tshd  :: "'m tstream \<Rightarrow> 'm event" where
"tshd ts = shd (Rep_tstream ts)"

text {* Cut away the first element of a stream. *}
definition tsrt :: "'m tstream \<Rightarrow> 'm tstream" where
"tsrt = espf2tspf srt"

text {* Retrieve the first @{text "n"} elements of a stream. *}
definition tstake :: "nat \<Rightarrow> 'm tstream \<Rightarrow> 'm tstream" where
"tstake n ts = Abs_tstream (stake n\<cdot>(Rep_tstream ts))"

text {* Define the concatenation of a (finite) list of events with a timed stream. *}
definition tsconc :: "'m event list \<Rightarrow> 'm tstream \<Rightarrow> 'm tstream" (infixr "\<bullet>+" 65) where
"tsconc l = espf2tspf (\<Lambda> s. (list2s l) \<bullet> s)"

text {* Remove the first @{text "n"} elements of the stream. *}
definition tsdrop :: "nat \<Rightarrow> 'm tstream \<Rightarrow> 'm tstream" where
"tsdrop n = espf2tspf (sdrop n)"

text {* Get the n-th element of the stream, where n=0 returns the head of the stream.*}
definition tsnth :: "nat \<Rightarrow> 'm tstream \<Rightarrow> 'm event" where
"tsnth n ts = snth n (Rep_tstream ts)"

text {* Convert a timed stream to an untimed one (discarding timing information) *}
definition tsabs :: "'m tstream \<Rightarrow> 'm stream" where
"tsabs ts = smap (\<lambda>e. case e of Msg m \<Rightarrow> m | \<surd> \<Rightarrow> undefined)\<cdot>(sfilter {e. e \<noteq> \<surd>}\<cdot>(Rep_tstream ts))"

text {* Stream definition for case study. *}
lift_definition s3 :: "nat tstream" is "\<up>(Msg 1) \<bullet> \<up>(Msg 2) \<bullet> \<up>\<surd> \<bullet> \<up>(Msg 3) \<bullet> \<up>(Msg 4) \<bullet> sinftimes(\<up>\<surd>)"
by simp

text {* Case study for tsabs. *}
lemma "tsabs s3 = list2s [1, 2, 3, 4]"
by (simp add: s3_def tsabs_def Abs_tstream_inverse sfilter_sinftimes_nin)

text {* Retrieve the set of messages of a stream (not including the Tick). *}
definition tsdom :: "'m tstream \<Rightarrow> 'm set" where
"tsdom ts = {m. \<exists>k. tsnth k ts = Msg m}"

text {* Retrieve the first block of messages. *}
definition tsthd :: "'m tstream \<Rightarrow> 'm list" where
"tsthd ts = s2list (smap (\<lambda>e. case e of Msg m \<Rightarrow> m | \<surd> \<Rightarrow> undefined )
                         \<cdot>(stakewhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>(Rep_tstream ts)))"

text {* Test tsthd. Proof uses s2list2lcons: "#s \<noteq> \<infinity> \<Longrightarrow> s2list (\<up>a \<bullet> s) = a # (s2list s)" *}
lemma casestudy1: "tsthd s3 = [1, 2]"
apply (simp add: tsthd_def)
apply (simp add: s3_def)
apply (simp add: Abs_tstream_inverse)
apply (simp add: s2list2lcons)
done

text {* Lemma needed to test tsthd on an infinite timed stream. *}
lemma l4: "\<up>(Msg 3) \<bullet> \<up>(Msg 4) \<bullet> \<up>\<surd> \<bullet> sinftimes (\<up>\<surd>) = \<up>(Msg 3) \<bullet> \<up>(Msg 4) \<bullet> sinftimes (\<up>\<surd>)"
by (metis sinftimes_unfold)

text {* Case study for tsthd. *}
lemma casestudy2: "tsthd (Abs_tstream (\<up>(Msg 3) \<bullet> \<up>(Msg 4) \<bullet> sinftimes (\<up>\<surd>))) = [3, 4]"
apply (subgoal_tac "tsthd (Abs_tstream (\<up>(Msg 3) \<bullet> \<up>(Msg 4) \<bullet> \<up>\<surd> \<bullet> sinftimes (\<up>\<surd>))) = [3, 4]")
apply (simp add: l4)
by (simp add: tsthd_def Abs_tstream_inverse s2list2lcons)

text {* Cut away the first block of the stream *}
definition tstrt :: "'m tstream \<Rightarrow> 'm tstream" where
"tstrt = espf2tspf (srtdw (\<lambda>x. x \<noteq> \<surd>))"

text {* Case study to test tstrt. *}
lemma rt_s3: "tstrt s3 = Abs_tstream (\<up>(Msg 3) \<bullet> \<up>(Msg 4) \<bullet> sinftimes (\<up>\<surd>))"
apply (simp add: s3_def tstrt_def espf2tspf_def)
using s3.abs_eq s3.rep_eq by auto

text {* Take the first n blocks of an event stream (including ticks). *}
primrec esttake :: "nat \<Rightarrow> 'm event stream \<rightarrow> 'm event stream" where    
esttake_0:   "esttake 0 = \<bottom>" |
esttake_Suc: "esttake (Suc n) = fix\<cdot>(\<Lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda>a. if a = \<surd> then \<up>\<surd> \<bullet> esttake n\<cdot>(srt\<cdot>s) 
                                                           else \<up>a \<bullet> h\<cdot>(srt\<cdot>s)))"

text {* Timed truncation operator: Returns an event stream consisting of the first n blocks of a
 timed stream (including ticks). *}
definition tsttake :: "nat \<Rightarrow> 'm tstream \<Rightarrow> 'm event stream" where
"tsttake n ts = esttake n\<cdot>(Rep_tstream ts)"

text {* Timed truncation operator: Returns a timed stream consisting of the first n blocks of a 
timed stream (including ticks). *}
definition tsttake2 :: "nat \<Rightarrow> 'm tstream \<Rightarrow> 'm tstream" where
"tsttake2 n ts = Abs_tstream (esttake n\<cdot>(Rep_tstream ts))"

text {* Remove the first @{text "n"} blocks of the given stream *}
definition tstdrop :: "nat \<Rightarrow> 'm tstream \<Rightarrow> 'm tstream" where
"tstdrop n = espf2tspf (Fix.iterate n\<cdot>(srtdw (\<lambda>x. x \<noteq> \<surd>)))"

text {* Droping the n-th block for n=1 is the same as having the stream without the first block. *}
lemma tstdrop_tstrt: "tstdrop 1 b = tstrt b"
apply (simp add: tstdrop_def)
apply (simp add: tstrt_def)
apply (simp add: espf2tspf_def)
by (simp add: One_nat_def)

text {* Case study with s3 = [1, 2, \<surd>, 3, 4, \<surd>, \<surd>, ... ,\<surd> , ...] *}
lemma casestudy3: "tstdrop 1 s3 = Abs_tstream (\<up>(Msg 3) \<bullet> \<up>(Msg 4) \<bullet> sinftimes(\<up>\<surd>))"
by (simp only: tstdrop_tstrt, simp add: rt_s3)

text {* Retrieve the @{text "n"}th block of the stream, where n=0 returns the first block of the 
stream. *}
definition tstnth :: "nat \<Rightarrow> 'm tstream \<Rightarrow> 'm list" where
"tstnth n ts = tsthd (tstdrop n ts)"

text {* Case study for tstnth. *}
lemma casestudy4: "tstnth 1 s3 = [3, 4]"
by (simp only: tstnth_def tstdrop_tstrt rt_s3 casestudy2)

text {* Apply a function to all messages of a stream. Ticks are mapped to ticks. *}
definition tstmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a tstream \<Rightarrow> 'b tstream" where
"tstmap f = espf2tspf (smap (\<lambda>x. case x of Msg m \<Rightarrow> Msg (f m) | \<surd> \<Rightarrow> \<surd>))"

text {* "Unzipping" of timed streams: project to the first element of a tuple of streams. *}
definition tstprojfst :: "(('a \<times> 'b), 'a) tspf" where
"tstprojfst = tstmap fst"

text {* "Unzipping" of timed streams: project to the second element of tuple. *}
definition tstprojsnd :: "(('a \<times> 'b),'b) tspf" where
"tstprojsnd = tstmap snd"

text {* Remove all messages from the stream which are not included in the given set. *}
definition tstfilter :: "'m set \<Rightarrow> 'm tstream \<Rightarrow> 'm tstream" where
"tstfilter M = espf2tspf (sfilter (Msg ` M \<union> {\<surd>}))"

text {*A helper function (event-spf) for the following function tsttakewhile (timed-spf).
      Take the first elements of a stream as long as the given function evaluates to @{text "true"}.
 Ticks are always preserved. *}
definition esttakewhile :: "('m \<Rightarrow> bool) \<Rightarrow> 'm event stream \<rightarrow> 'm event stream" where
"esttakewhile f = fix\<cdot>(\<Lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> e. if e = \<surd> then \<up>\<surd> \<bullet> h\<cdot>(srt\<cdot>s) 
                                              else (if f (THE m. e = Msg m) then \<up>e \<bullet> h\<cdot>(srt\<cdot>s) 
                                                    else sfilter {\<surd>}\<cdot>(srt\<cdot>s))))" 

text {* The function tsttakewhile (timed-spf). *}
definition tsttakewhile :: "('m \<Rightarrow> bool) \<Rightarrow> 'm tstream \<Rightarrow> 'm tstream" where
"tsttakewhile f = espf2tspf (esttakewhile f)"

text {* A helper function (event-spf) for the following function tstdropwhile (timed-spf). 
  Drop the first elements of a stream, as long as a given function evaluates to @{text "true"}. 
Ticks are always preserved. *}
definition estdropwhile :: "('m \<Rightarrow> bool) \<Rightarrow> 'm event stream \<rightarrow> 'm event stream" where
"estdropwhile f = fix\<cdot>(\<Lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> e. if e = \<surd> then \<up>\<surd> \<bullet> h\<cdot>(srt\<cdot>s) 
                                              else (if f (THE m. e = Msg m) then h\<cdot>(srt\<cdot>s) else s)))"
text {* The function tstdropwhile (timed-spf). *}
definition tstdropwhile :: "('m \<Rightarrow> bool) \<Rightarrow> 'm tstream \<Rightarrow> 'm tstream" where
"tstdropwhile f = espf2tspf (estdropwhile f)"

text {* A helper function. Behaves like the following function tstscanl,
but only processes the first "n" elements of the given event stream. *}
primrec estscanl_pr :: "nat \<Rightarrow> ('o \<Rightarrow> 'i \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> 'i event stream \<Rightarrow> 'o event stream" where
"estscanl_pr 0 f q s = \<epsilon>" |
"estscanl_pr (Suc n) f q s = (if s=\<epsilon> then \<epsilon> 
                              else (if (shd s = \<surd>) then (\<up>\<surd> \<bullet> estscanl_pr n f q (srt\<cdot>s)) 
                                    else \<up>(Msg (f q (THE m. Msg m = shd s))) 
                                        \<bullet> (estscanl_pr n f (f q (THE m. Msg m = shd s)) (srt\<cdot>s))))"

text {* Apply a function elementwise to the input stream. Like @{text "map"}, 
but also takes the previously generated output element as additional input to the function. 
For the first computation, an initial value is provided. *}
definition tstscanl :: "('o \<Rightarrow> 'i \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> ('i, 'o) tspf" where
"tstscanl f q = espf2tspf (\<Lambda> s. \<Squnion>i. estscanl_pr i f q s)"

text {* Check whether a given tspfo is type-invariant. A tspfo is considered type-invariant, if for
all input streams, the domain of the output stream is a subset of the domain of the input stream. *}
definition tstypeinv :: "'m tspfo \<Rightarrow> bool" where
"tstypeinv f \<equiv> \<forall>M s. tsdom s \<subseteq> M \<longrightarrow> tsdom (f s) \<subseteq> M"

text {* Fairness predicate on event stream processing function. An espf is considered fair
  if all inputs with infinitely many ticks are mapped to outputs with infinitely many ticks. *}
definition estfair :: "('i event,'o event) spf \<Rightarrow> bool" where
"estfair f \<equiv> \<forall>s. #(sfilter {\<surd>}\<cdot>s) = \<infinity> \<longrightarrow> #(sfilter {\<surd>}\<cdot>(f\<cdot>s)) = \<infinity>" 

text {* Add to simplificator to make proofs easier for the user. *}
declare Rep_tstream [simp add]
declare Rep_tstream_inverse [simp add]

(* ----------------------------------------------------------------------- *)
section {* Lemmas *}
(* ----------------------------------------------------------------------- *)

text {* Abs_Rep *}
lemma Abs_Rep: "Abs_tstream (Rep_tstream t) = t"
apply simp
done

text {* Rep_Abs *}
lemma Rep_Abs: "#t \<noteq> \<infinity> \<or> #(sfilter {\<surd>}\<cdot>t) = \<infinity> \<Longrightarrow> Rep_tstream (Abs_tstream t) = t"
apply (simp add: Abs_tstream_inverse)
done

text {* typedef tstream unfold. *}
lemma tstreaml1[simp]: "#(Rep_tstream x) \<noteq> \<infinity> \<or> #(sfilter {\<surd>}\<cdot>(Rep_tstream x)) = \<infinity>"
apply (insert Rep_tstream [of x])
apply simp
done

text {* By appending an event on the left side, a timed stream remains a timed stream. *}
lemma tstream_scons_eq[simp]: "((\<up>e \<bullet> rs) \<in> {t::'a event stream. #t \<noteq> \<infinity> \<or> #({\<surd>} \<ominus> t) = \<infinity>}) 
                      \<longleftrightarrow> (rs \<in> {t. #t \<noteq> \<infinity> \<or> #({\<surd>} \<ominus> t) = \<infinity>})"
apply (smt fold_inf lnat.injects mem_Collect_eq sfilter_in sfilter_nin slen_scons)
done

text {* Another useful variant of this identity: *}
lemma [simp]: "Rep_tstream (Abs_tstream (\<up>e \<bullet> Rep_tstream s)) = (\<up>e \<bullet> Rep_tstream s)"
using Abs_tstream_inverse Rep_tstream tstream_scons_eq 
apply blast
done

text {* The following implication follows from the type definition of timed streams. *}
lemma Rep_tstreamD1: "(Rep_tstream s = ts) \<Longrightarrow> (ts \<in> {t::'a event stream. #t \<noteq> \<infinity> \<or> #({\<surd>} \<ominus> t) = \<infinity>})"
using Rep_tstream 
apply blast
done






text {* If a timed stream is non-empty, then, using the list-tstream concatenation
tsconc :: "'m event list \<Rightarrow> 'm tstream \<Rightarrow> 'm tstream" (infixr "\<bullet>+")
we can write the stream as a concatenation of the head and its rest. *}
lemma tstream_exhaust: "ts \<noteq> Abs_tstream \<epsilon> \<Longrightarrow>  \<exists>hd rs. ts = [hd] \<bullet>+ rs"
apply (rule_tac x="Rep_tstream ts" in scases)
apply (frule Rep_tstreamD1)
apply (drule_tac f="Abs_tstream" in arg_cong)
apply simp
apply (rule_tac x="a" in exI)
apply (rule_tac x="Abs_tstream s" in exI)
apply (rule Rep_tstream_inject [THEN iffD1])
apply (simp add: tsconc_def espf2tspf_def)
apply (smt Abs_tstream_inverse Rep_tstream tstream_scons_eq)
done

text {*If P holds for empty and non-empty timed streams, it holds for all timed streams. *}
lemma tscases1: "\<And>x P. \<lbrakk>x = Abs_tstream \<epsilon> \<Longrightarrow> P; \<And>e s. x = [e] \<bullet>+ s \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
apply (insert tstream_exhaust)
apply blast
done

text {*  Similiarly, if P holds for empty streams, and for non-empty ones which might begin with 
a message or a tick, it holds for all timed streams. *}
lemma tscases: "\<And>x P. \<lbrakk>x = Abs_tstream \<epsilon> \<Longrightarrow> P; \<And>m s. x = [Msg m] \<bullet>+ s \<Longrightarrow> P; \<And>s. x = [\<surd>] \<bullet>+ s \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
apply (metis event.exhaust tscases1)
done

text {* If a stream is infinite, then it has infinitely many ticks.*}
lemma a: "#(Rep_tstream rs) = \<infinity> \<longrightarrow> #({\<surd>} \<ominus> Rep_tstream rs) = \<infinity>"
using tstreaml1
by simp

text {* If transform list to stream and append it on a timed stream, result also a timed stream. *}
lemma list_conc_tstream [simp]: "list2s es \<bullet> Rep_tstream rs \<in> {t::'a event stream. #t \<noteq> \<infinity> \<or> #({\<surd>} \<ominus> t) = \<infinity>}"
apply (induct es)
apply (simp only: list2s_0)
apply (simp only: sconc_fst_empty)
apply (simp only: Rep_tstream)
apply simp
done

text {* The concatenation of an empty list with a timed streams returns the timed stream itself. *}
lemma [simp]: "([] \<bullet>+ rs) = rs"
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
done

text {* Head of concatenation of an 1-element list with a timed stream is the element of the list.*}
lemma [simp]: "tshd ([e] \<bullet>+ rs) = e"
apply (simp add: tshd_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
done

text {* The head of the concatenation of a list with a timed stream is the head of the list. *}
lemma [simp]: "tshd ((e#es) \<bullet>+ rs) = e"
apply (simp add: tshd_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
apply (subst tstream_scons_eq Abs_tstream_inverse)
apply (subst tstream_scons_eq)
apply (subst list_conc_tstream)
apply simp
apply simp
done

text {* Remainder of the concat of an 1-element list with a timed stream is the stream itself.*}
lemma [simp]: "tsrt ([e] \<bullet>+ rs) = rs"
apply (simp add: tsrt_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
done

text {* The remainder of the concatenation of a list with a timed stream is the same as
the concatenation of the remainder of the list with the timed stream. **}
lemma [simp]: "tsrt ((e#es) \<bullet>+ rs) = (es \<bullet>+ rs)"
apply (simp add: tsrt_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
apply (subst tstream_scons_eq Abs_tstream_inverse)
apply (subst tstream_scons_eq)
apply (subst list_conc_tstream)
apply simp
apply simp
done

text {* Retrieving the first 0 elements of a stream returns the empty stream. *}
lemma [simp]: "tstake 0 x = Abs_tstream \<bottom>"
apply (simp add: tstake_def)
done

text {* Taking n+1 elements from the concatenation of a 1-element list with a timed stream
is like appending the element of the list to the n-prefix of the timed stream.*}
lemma [simp]: "tstake (Suc n) ([e] \<bullet>+ rs) =  Abs_tstream (\<up>e \<bullet> Rep_tstream (tstake n rs))"
apply (simp add: tstake_def)
apply (simp add: tsconc_def )
apply (simp add: espf2tspf_def)
apply (simp add: Rep_Abs)
done

text {*If all k-prefixes of two timed streams are equal for all k, then the two streams are equal.*}
lemma tstake_lemma: "(\<And>k. tstake k x = tstake k y) \<Longrightarrow> x = y" 
apply (rule Rep_tstream_inject [THEN iffD1])
apply (rule stream.take_lemma)
apply (simp add: tstake_def)
apply (smt tstake_def Abs_tstream_inverse Rep_Abs Rep_tstream sconc_fst_inf split_streaml1)
done

text {* *If for all streams, all inputs with infinitely many ticks are mapped apply a function to outputs with
 infinitely many ticks, then the function is fair. *}
lemma estfairI: "(\<And>s. #(sfilter {\<surd>}\<cdot>s) = \<infinity> \<Longrightarrow> #(sfilter {\<surd>}\<cdot>(f\<cdot>s)) = \<infinity>) \<Longrightarrow> estfair f"
apply (simp add: estfair_def)
done

text {* If a function is fair and an input stream has many ticks, then the output stream of f also has 
infinitely many ticks. *}
lemma estfairD: "\<lbrakk>estfair f;#(sfilter {\<surd>}\<cdot>s) = \<infinity>\<rbrakk> \<Longrightarrow> #(sfilter {\<surd>}\<cdot>(f\<cdot>s)) = \<infinity>"
apply (simp add: estfair_def)
done

text {* A timed stream without its head element is still a timed stream. *}
lemma srt_tstream[simp]: "srt\<cdot>(Rep_tstream x) \<in> {t::'a event stream. #t \<noteq> \<infinity> \<or> #({\<surd>} \<ominus> t) = \<infinity>}"
apply (smt Rep_tstream inf_scase inject_scons mem_Collect_eq sfilter_in sfilter_nin slen_scons 
stream.sel_rews(2) surj_scons)
done

text {*  Removing the first 0 elements of a stream returns the stream itself. *}
lemma [simp]: "tsdrop 0 x = x"
apply (simp add: tsdrop_def)
apply (simp add: espf2tspf_def)
done

text {* After dropping n elements, a timed stream remains a timed stream. *}
lemma Rep_Abs_sdrop[simp]: 
  "sdrop n\<cdot>(Rep_tstream x) \<in> {t::'a event stream. #t \<noteq> \<infinity> \<or> #({\<surd>} \<ominus> t) = \<infinity>}"
apply (metis (mono_tags, lifting) fair_sdrop_rev mem_Collect_eq slen_sfilter_sdrop tstreaml1)
done

text {* Dropping n+1 elements from a stream is the same as dropping n elements out of the
rest(without the head element) of the stream. *}
lemma tsdrop_forw_tsrt: "tsdrop (Suc n) x = tsdrop n (tsrt x)"
apply (simp add: tsdrop_def)
apply (simp add: tsrt_def)
apply (simp add: espf2tspf_def)
apply (smt Abs_tstream_inverse Rep_Abs Rep_Abs_sdrop fair_sdrop inf_less_eq sdrop_forw_rt 
slen_sfilter_sdrop_ile tstreaml1)
done

text {* Dropping n+1 elements from a stream is the same as dropping n elements out of the stream, 
and then removing the head element from it. *}
lemma tsdrop_back_tsrt:"tsdrop (Suc n) x = tsrt (tsdrop n x)"
apply (simp add: tsdrop_def)
apply (simp add: tsrt_def)
apply (simp add: espf2tspf_def)
apply (metis (no_types, lifting) Abs_tstream_inverse Rep_Abs_sdrop sdrop_back_rt)
done

text {* If the domain of a stream is a subset of a set M, then the domain of the remainder
of the stream after removing the head element, is also a subset of the set M. *}
lemma tsdom_tsrtI: "tsdom x \<subseteq> M \<Longrightarrow> tsdom (tsrt x) \<subseteq> M"
apply (simp add: tsdom_def)
apply (simp add: tsrt_def)
apply (simp add: espf2tspf_def)
apply (simp add: tsnth_def)
apply (subst Abs_tstream_inverse)
apply simp
using srt_tstream 
apply blast
apply (rule_tac B="{m. \<exists>k. snth k (Rep_tstream x) = Msg m}" in subset_trans)
apply (rule subsetI)
apply simp
apply (erule exE)
apply (rule_tac x="Suc k" in exI)
apply (simp add: snth_rt)
apply simp
done

text {* If the domain of a stream is a subset of a set M, then the domain of the remainder
of the stream after removing n elements, is also a subset of the set M. *}
lemma tsdom_tsdropI: "tsdom s \<subseteq> M \<Longrightarrow> tsdom (tsdrop n s) \<subseteq> M"
apply (simp add: atomize_imp)
apply (rule_tac x="s" in spec)
apply (induct_tac n)
apply simp
apply (rule allI)
apply (rule impI)
apply (erule_tac x="tsrt x" in allE)
apply (drule mp)
apply (rule tsdom_tsrtI)
apply assumption
apply (simp add: tsdrop_forw_tsrt)
done

text {* Every infinite timed stream has at least a tick in it. *}
lemma tsnth_tickl: "#(Rep_tstream x) = \<infinity> \<Longrightarrow> \<exists>n. tsnth n x = \<surd>"
apply (simp add: tsnth_def)
apply (rule ccontr)
apply simp
apply (insert ex_snth_in_sfilter_nempty [of "Rep_tstream x" "{\<surd>}"])
apply simp
apply (insert Rep_tstream [of x])
apply simp
done

text {* The remainder of the concatenation of an 1-element list with a timed stream is the
timed stream itself. *}
lemma [simp]: "tstrt ([Msg m] \<bullet>+ rs) = tstrt rs"
apply (simp add: tstrt_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
done

text {* Concatenating an 1-element list consisting of a tick, with a timed stream, 
and then removing the first block of it, yields the timed stream again. *}
lemma [simp]: "tstrt ([\<surd>] \<bullet>+ rs) = rs"
apply (simp add: tstrt_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
done

text {* Taking the (n+1)-th element of the concatenation of an 1-element list with a timed stream
is the same as taking the n-th element of the timed stream. *}
lemma [simp]: "tsnth (Suc n) ([e] \<bullet>+ rs) = tsnth n rs"
apply (simp add: tsnth_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
done

text {*  Taking the 0-th element of the stream is apply definition of tsnth the same as 
taking the head of the stream. *}
lemma [simp]: "tsnth 0 x = tshd x"
apply (simp add: tsnth_def)
apply (simp add: tshd_def)
done

text {* Dropping n+1 elements from the concatenation of an 1-element list with a timed stream
is the same as dropping n elements from the timed stream. *}
lemma [simp]: "tsdrop (Suc n) ([e] \<bullet>+ rs) = tsdrop n rs"
apply (simp add: tsdrop_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
done

text {* The domain of the infinite stream consisting only of ticks is empty. *}
lemma tsdom_tsjusttime[simp]: "tsdom justtime = {}"
apply (simp add: justtime_def)
apply (simp add: tsdom_def)
apply (simp add: tsnth_def)
apply (subst Abs_tstream_inverse)
apply simp
apply (simp add: snth_def)
done

text {* Taking at least one block from the concatenation of an 1-message list with a stream is the
 same as taking these blocks from the timed stream and then appending the list message on it. *}
lemma tsttake_Suc_Msg [simp]: "tsttake (Suc n) ([Msg m] \<bullet>+ rs) = \<up>(Msg m) \<bullet> tsttake (Suc n) rs"
apply (simp add: tsttake_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
apply (subst fix_eq2, simp+)
done

text {* Taking at least one block from the concatenation of a list consisting of one tick
with a stream is the same as taking one less block from the timed stream and then appending the tick
on it. *}
lemma tsttake_Suc_Tick [simp]: "tsttake (Suc n) ([\<surd>] \<bullet>+ rs) = \<up>\<surd> \<bullet> tsttake n rs"
apply (simp add: tsttake_def)
apply (simp add: tsconc_def)
apply (simp add: espf2tspf_def)
apply (subst fix_eq2, simp+)
done

text {* If for every stream, which has either infinite many ticks, or is finite, a property P holds,
then the property P holds for any timed stream. *}
lemma PRep_tstreamI: "\<lbrakk>\<And>x. (#(sfilter {\<surd>}\<cdot>x) = \<infinity> \<or> #x \<noteq> \<infinity>)  \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> P (Rep_tstream y)"
using tstreaml1 
apply blast
done

text {* Retrieving the first 0 elements of a stream returns the empty stream *}
lemma [simp]: "tsttake 0 x = \<epsilon>"
apply (simp add: tsttake_def)
done

text {* Take the first n+1 blocks of an event stream, where the stream has no messages in the first block,
 is the same as taking the first tick and n blocks. *}
lemma esttake_Tick[simp]: "esttake (Suc n)\<cdot>(\<up>\<surd> \<bullet> x) = \<up>\<surd> \<bullet> esttake n\<cdot>x"
apply simp
apply (subst fix_eq2, auto)
done

text {* Take the first n+1 blocks of an event stream, where the stream has one message in the first block,
 is the same as taking the first message and continue checking that same first block. *}
lemma esttake_Msg[simp]: "esttake (Suc n)\<cdot>(\<up>(Msg m) \<bullet> x) = \<up>(Msg m) \<bullet> esttake (Suc n)\<cdot>x"
apply simp
apply (subst fix_eq2, auto)
done

text {* Take the first x blocks of an empty stream returns the empty stream. *}
lemma esttake_ep[simp]: "esttake x\<cdot>\<epsilon> = \<epsilon>"
apply (induct_tac x)
apply simp
apply simp
apply (subst fix_eq2, auto)
done

text {* To prove the following lemmas, it is easier to remove e esttake_Suc from simplifier: *}
declare esttake_Suc [simp del]

text {* Now we test the esttake_ep lemma: *}
definition just1 :: "nat event stream" where
"just1 = \<up>(Msg 1)"

text {* We test the esttake function by taking more elements than the length of the stream.
As expected, we get the stream back: *}
lemma "esttake 3\<cdot>just1 = \<up>(Msg 1)"
by (metis just1_def esttake_Msg esttake_ep numeral_3_eq_3 sconc_snd_empty)

text {* We prove that taking the first 1,2,...,n,... blocks of an event stream with esttake forms a chain. 
Thus, we have to show that for all i: esttake i \<sqsubseteq> esttake (Suc i) *}
lemma chain_esttake[simp]: "chain esttake"
apply (rule chainI)
apply (rule cfun_belowI)
apply (rule_tac x=i in spec)
apply (rule_tac x=x in ind)
apply auto
apply (case_tac "x")
apply auto
apply (case_tac "a")
apply auto
apply (rule monofun_cfun_arg)
apply auto
apply (rule monofun_cfun_arg)
apply auto
done

text {* The limit of the prefixes of a stream, which are produced apply esttake, is the stream itself.
 As we we are in a CPO, upper bounds of chains always exist. *}
lemma reach_stream: "(\<Squnion>i. stake i\<cdot>s) = s"
apply (rule stream.take_lemma [OF spec [where x=s]])
apply (induct_tac n, simp, rule allI)
apply (rule_tac y=x in scases', simp)
apply (subst lub_range_shift [where j="Suc 0", THEN sym],simp+)
apply (subst contlub_cfun_arg [THEN sym], auto) 
done

text {* Same for esttake. *}
lemma reach_estream: "(\<Squnion>k. esttake k\<cdot>x) = x"
apply (rule stream.take_lemma)
apply (rule_tac x=x in spec)
apply (induct_tac n)
apply auto
apply (rule_tac x=x in scases)
apply auto
apply (case_tac "a")
apply auto
apply (subst lub_range_shift [where j = "Suc 0", THEN sym])
apply simp
apply auto
apply (subst contlub_cfun_arg [THEN sym])
apply simp
apply (rule ch2ch_Rep_cfunL)
apply (rule chainI)
apply (rule chain_esttake [THEN chainE])
apply simp
apply (rule cfun_arg_cong)
apply (erule_tac x="s" in allE)
apply (erule subst)
apply (rule cfun_arg_cong)
apply (rule sym)
apply (subst lub_range_shift [where j = "Suc 0", THEN sym])
apply simp
apply simp
apply (subst lub_range_shift [where j = "Suc 0", THEN sym])
apply auto
apply (subst contlub_cfun_arg [THEN sym])
apply auto
done


text {* esttake of esttake.*}
lemma esttake_esttake[simp]: "esttake k\<cdot>(esttake n\<cdot>s) = esttake (min k n)\<cdot>s"
apply (rule_tac x="k" in spec)
apply (rule_tac x="n" in spec)
apply (rule ind [of _ s])
apply simp
apply simp
apply (case_tac "a")
apply simp
apply (rule allI)
apply (rule allI)
apply (case_tac "x")
apply simp
apply simp
apply (case_tac "xa")
apply simp
apply simp
apply (rule allI)
apply (rule allI)
apply (case_tac "x")
apply simp
apply simp
apply (case_tac "xa")
apply simp
apply simp
done

text {*If all k-prefixes of two timed streams are equal for all k, then the two streams are equal.*}
lemma esttake_lemma: "(\<And>k. esttake k\<cdot>x = esttake k\<cdot>y) \<Longrightarrow> x = y"
apply (subst reach_estream [THEN sym])
apply (rule sym)
apply (subst reach_estream [THEN sym])
apply (rule lub_eq)
apply auto
done

text {* The take functions give apply definition prefixes of the stream: *}
lemma ub_of_esttake[simp]: "esttake k\<cdot>x \<sqsubseteq> x"
apply (rule_tac y="\<Squnion> k. esttake k\<cdot>x" in below_trans)
apply (rule is_ub_thelub)
apply simp
apply (subst reach_estream)
apply simp
done

text {* If length of prefix is infinite, then the prefix equals the stream itself. *}
lemma esttake_infD: "#(esttake k\<cdot>x) = \<infinity> \<Longrightarrow> esttake k\<cdot>x = x"
apply (subgoal_tac "esttake k\<cdot>x \<sqsubseteq> x")
apply (rule eq_less_and_fst_inf)
apply simp
apply simp
apply simp
done

text {* We prove that taking the first 1,2,...,n,... blocks of a stream with tsttake forms a chain. 
Thus, we have to show that for all i: tsttake i \<sqsubseteq> tsttake (Suc i) *}
lemma chain_tsttake[simp]: "chain tsttake"
apply (rule chainI)
apply (rule fun_belowI)
apply (simp add: tsttake_def)
apply (rule chainE)
apply (rule ch2ch_fun)
apply (rule ch2ch_monofun)
apply simp
apply (simp add: monofun_Rep_cfun)
apply simp
done

text {* The limit of the prefixes of a stream, which are blocks produced apply tsttake, 
is the stream itself. *}
lemma tsttake_lub: "(\<Squnion>k. tsttake k x) = Rep_tstream x"
apply (simp add: tsttake_def)
apply (rule reach_estream)
done

text {* If all block prefixes of two timed streams are equal, then the two streams are equal. *}
lemma tsttake_lemma: "(\<And>n. tsttake n x = tsttake n y) \<Longrightarrow> x = y"
apply (rule Rep_tstream_inject [THEN iffD1])
apply (rule esttake_lemma)
apply (simp add: tsttake_def)
done

text {* If the number of elements from a set X in a stream s is infinite, then it remains infinite
even after we drop from the stream all elements not in X. *}
lemma srtdw_tstream[simp]: "srtdw (\<lambda>x. x \<noteq> \<surd>)\<cdot>(Rep_tstream x) \<in> {t::'a event stream. #t \<noteq> \<infinity> \<or> #({\<surd>} \<ominus> t) = \<infinity>}"
apply (insert sfilter_srtdwl2 [of "{\<surd>}" "Rep_tstream x"])
apply simp
apply (metis inf_less_eq slen_srtdw tstreaml1)
done

text {* Using the above lemma, we can add the following rewriting rule for srtdw:*}
lemma [simp]: 
"Rep_tstream (Abs_tstream (srtdw (\<lambda>x. x \<noteq> \<surd>)\<cdot>(Rep_tstream x))) =  srtdw (\<lambda>x. x \<noteq> \<surd>)\<cdot>(Rep_tstream x)"
using Abs_tstream_inverse 
using srtdw_tstream 
apply blast
done

text {* Now we can show that, apply using srtdw multiple times for dropping blocks out of a stream, 
the result still remains timed stream. *}
lemma [simp]: 
  "iterate n\<cdot>(srtdw (\<lambda>x. x \<noteq> \<surd>))\<cdot>(Rep_tstream s) \<in> {t::'a event stream. #t \<noteq> \<infinity> \<or> #({\<surd>} \<ominus> t) = \<infinity>}"
apply (rule_tac x="s" in spec)
apply (induct_tac n)
apply (simp del: iterate_Suc)
apply (rule allI)
using tstreaml1 
apply blast
apply (smt Abs_tstream_inverse iterate_Suc2 srtdw_tstream)
done

text {* Dropping n+1 blocks from a timed stream is the same as dropping the first block of the 
stream apply applying tstrt and then dropping the remaining n blocks. *}
lemma tstdrop_Suc_forw: "tstdrop (Suc n) x = tstdrop n (tstrt x)"
apply (simp add: tstdrop_def)
apply (simp add: tstrt_def)
apply (simp add: espf2tspf_def del: iterate_Suc)
apply (subst iterate_Suc2)
apply simp
done

text {* Taking the (n+1)-th block of a stream is the same as removing the first block from it
and afterwards taking the n-th block of the remainder. *}
lemma tstnth_Suc [simp]: "tstnth (Suc n) x = tstnth n (tstrt x)"
apply (simp add: tstnth_def)
apply (simp add: tstdrop_Suc_forw)
done

text {* Removing the first 0 blocks of a stream returns the stream itself. *}
lemma [simp]: "tstdrop 0 b = b"
apply (simp add: tstdrop_def)
apply (simp add: espf2tspf_def)
done

text {* Taking block 0 is the same as taking the head block of the timed stream. *}
lemma [simp]: "tstnth 0 b = tsthd b"
apply (simp add: tstnth_def)
done

text {* Taking the first elements of a stream means returning a prefix of the stream. *}
lemma [simp]: "stakewhile p\<cdot>s \<sqsubseteq> s"
apply (rule_tac x="s" in ind)
apply auto
done

text {*For a timed stream which has at least a tick: if the function sdropwhile is used to drop
all the messages until a tick comes, then it fulfills: *}
lemma sfilterl5:
  "sfilter {\<surd>}\<cdot>x \<noteq> \<epsilon> \<Longrightarrow> \<up>\<surd> \<bullet> srt\<cdot>(sdropwhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>x) = sdropwhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>x"
apply (simp add: atomize_imp)
apply (rule_tac x="x" in ind)
apply simp
apply simp
apply (case_tac "a")
apply simp
apply simp
done

text {*Taking events from a stream until a tick is found, and then taking from the result n events,
is same as first taking n events, and then from the result taking events until a tick is found. *}
lemma esttake_stakewhilel1:
  "esttake n\<cdot>(stakewhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>x) = stakewhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>(esttake n\<cdot>x)"
apply (rule_tac x="n" in spec)
apply (rule_tac x="x" in ind)
apply simp
apply simp
apply (rule allI)
apply (case_tac "a")
apply simp
apply (case_tac "x")
apply simp
apply simp
apply (case_tac "x")
apply simp
apply simp
done

text {*Dropping events from a stream until a tick is found, and then taking from the result n
events, is same as first taking n events, and then from result taking events until tick found. *}
lemma esttake_sdropwhilel1:
  "esttake n\<cdot>(sdropwhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>x) = sdropwhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>(esttake n\<cdot>x)"
apply (rule_tac x="n" in spec)
apply (rule_tac x="x" in ind)
apply simp
apply simp
apply (rule allI)
apply (case_tac "a")
apply simp
apply (case_tac "x")
apply simp
apply simp
apply (case_tac "x")
apply simp
apply simp
done

text {*If we use stakewhile to retreave all messages until a tick is found, we automatically get a
prefix stream consisting of only one block. This means, applying on the left side esttake (Suc n) 
for any n=0,1,.., won't make any difference and the result will just be the first block. *}
lemma esttake_stakewhilel2:
  "stakewhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>x = esttake (Suc n)\<cdot>(stakewhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>x)"
apply (rule_tac x="n" in spec)
apply (rule_tac x="x" in ind)
apply simp
apply simp
apply (rule allI)
apply (case_tac "a")
apply simp
apply simp
done

text {*For any stream, its prefix concatenated with its suffix returns the stream itself. *}
lemma stakewhile_sdropwhile[simp]:"stakewhile p\<cdot>x \<bullet> sdropwhile p\<cdot>x = x"
apply (rule stream.take_lemma)
apply (rule_tac x="x" in spec)
apply (induct_tac n)
apply simp
apply simp
done

text {*Taking n+1 blocks is the same as initially taking the first block, and then taking the 
remaining blocks. *}
lemma esttake_tstreaml1: "sfilter {\<surd>}\<cdot>x \<noteq> \<epsilon> \<Longrightarrow> 
   esttake (Suc n)\<cdot>x = stakewhile (\<lambda>x. x \<noteq> \<surd>)\<cdot>x \<bullet> \<up>\<surd> \<bullet> esttake n\<cdot>(srtdw (\<lambda>x. x \<noteq> \<surd>)\<cdot>x)"
apply (simp add: srtdw_def)
apply (subst esttake_Tick [THEN sym])
apply (subst sfilterl5)
apply (rule notI)
apply simp
apply (subst esttake_stakewhilel2 [where n="n"])
apply (subst esttake_stakewhilel1)
apply (subst esttake_sdropwhilel1)
apply simp
done


end





