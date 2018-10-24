(*
    Komponist:    Sebastian Stüber
    Description:  This is a specification of the "Alternating Bit Protocol" on timed streams. 
*)

theory ABP
imports TStream Channel OptionCpo 

begin
  default_sort countable



(* ----------------------------------------------------------------------- *)
  section \<open>Definition of basic datatypes \<close>
(* ----------------------------------------------------------------------- *)


datatype data = \<D> nat

  (* needs to be instanciated to countables in order to use with streams *)
  instance data::countable
  apply(intro_classes)
  by(countable_datatype)


(* overriedes definition of "M" in Channel.thy *)
datatype M = D data | B bool | DB data bool
  (* DB is used to hide (data\<times>bool) type *)

  instance M::countable
  apply(intro_classes)
  by(countable_datatype)

(* Stands for : DataBitPair *)
definition DBP :: "(data \<times> bool) \<Rightarrow> M" where
"DBP \<equiv> \<lambda>(d,b). DB d b"


(* defines which elements are allowed on the channels *)
  (* overwrites the "ctype" definition in Channel.thy ! *)
fun ctype :: "channel \<Rightarrow> M set" where
"ctype c1 = range D"    | (* external \<rightarrow> Send*)
"ctype c2 = range B"    | (* Med2 \<rightarrow> Send *)
"ctype c3 = range DBP"  | (* Send \<rightarrow> Med1 *)
"ctype c4 = range DBP"  | (* Med1 \<rightarrow> Recv *)
"ctype c5 = range D"    | (* Recv \<rightarrow> external *)
"ctype c6 = range B"      (* Recv \<rightarrow> Med2 *)


(* StBundles are defined with "M stream". these are converters from the "subtypes" of M to M and back *)
definition m2d :: "M tstream \<Rightarrow> data tstream" where
"m2d s \<equiv> tstmap (inv D) s"
definition d2m :: "data tstream \<Rightarrow> M tstream" where
"d2m s \<equiv> tstmap D s"

definition m2b :: "M tstream \<Rightarrow> bool tstream" where
"m2b s \<equiv> tstmap (inv B) s"
definition b2m :: "bool tstream \<Rightarrow> M tstream" where
"b2m s \<equiv> tstmap B s"

definition m2db :: "M tstream \<Rightarrow> (data\<times>bool) tstream" where
"m2db s \<equiv> tstmap (inv DBP) s"
definition db2m :: "(data\<times>bool) tstream \<Rightarrow> M tstream" where
"db2m s \<equiv> tstmap DBP s"






(* ----------------------------------------------------------------------- *)
  subsection \<open>Definition of "Timed Stream Bundles"\<close>
(* ----------------------------------------------------------------------- *)


(* alternative tsdom definition, because the original one is very hard to use *)
definition tsdom2 :: "'a tstream \<Rightarrow> 'a set" where
"tsdom2 t = {a | a. (Msg a) \<in> sdom\<cdot>(Rep_tstream t)}"

lemma "tsdom t = tsdom2 t"
proof
  show "tsdom t\<subseteq> tsdom2 t"
  proof 
    fix x
    assume "x\<in>(tsdom t)"
    obtain k where k_def: "tsnth k t = Msg x" using \<open>x \<in> tsdom t\<close> tsdom_def by auto
    hence "snth k (Rep_tstream t) = Msg x" by (metis k_def tsnth_def)
    hence "Fin k < #(Rep_tstream t)" sorry
    hence "Msg x \<in> sdom\<cdot>(Rep_tstream t)" by (metis k_def snth2sdom tsnth_def) 
    thus "x\<in>(tsdom2 t)" by (simp add: tsdom2_def) 
  qed
  show "tsdom2 t\<subseteq> tsdom t"
    by (metis (mono_tags, lifting) mem_Collect_eq sdom2snth subsetI tsdom2_def tsdom_def tsnth_def)
qed


  (* Definition: Welltyped. "a \<rightharpoonup> b" means "a => b option" *)
  (* Every TStream may only contain certain elements *)
definition tsb_welltyped :: "(channel \<rightharpoonup> M tstream) => bool" where
"tsb_welltyped f \<equiv> \<forall>c \<in> dom f. tsdom2 (the(f c)) \<subseteq> ctype c"


  (* Definition: Timed Stream Bundle. *)
    (* this is not a cpo because tStream is no CPO (and will never be) *)
  typedef TSB = "{b :: channel \<rightharpoonup> M tstream . tsb_welltyped b }"
  using tsb_welltyped_def by auto
  
  setup_lifting type_definition_TSB




(* ----------------------------------------------------------------------- *)
  subsubsection \<open>Definition on TSB\<close>
(* ----------------------------------------------------------------------- *)



  (* returns the tstream flowing in given channel *)
  definition tsbGetCh :: "TSB \<Rightarrow> channel \<Rightarrow> M tstream" (" _ \<close> _")where
  "tsbGetCh b c = the ((Rep_TSB b) c)"


  definition tsrcDups_helper :: "'m event stream \<rightarrow> 'm event stream" where
  "tsrcDups_helper \<equiv> \<mu> h. (\<Lambda> s. if s = \<epsilon> then \<epsilon> else \<up>(shd s) \<bullet> h\<cdot>(estdropwhile (\<lambda>x. Msg x = shd s)\<cdot>s))"
  
  (* remove successive duplicates on tstreams *)
  definition tsrcdups :: "'m tstream \<Rightarrow> 'm tstream" where
  "tsrcdups = espf2tspf tsrcDups_helper"


  definition tsbDom :: "TSB \<Rightarrow> channel set" where
  "tsbDom tb = dom (Rep_TSB tb)"

  (* returns the first n blocks of the TSB *)
  definition tsbTTake :: "nat \<Rightarrow> TSB \<Rightarrow> TSB" where 
  "tsbTTake n tb = Abs_TSB (\<lambda>c. (c\<in>tsbDom tb) \<leadsto> (tsttake2 n (tb \<close> c)))"
  
   (* Channels not in the channel set are set to "None". *)
  definition tsbRestrict:: "channel set \<Rightarrow> TSB \<Rightarrow> TSB" where
  "tsbRestrict cs b  \<equiv>  Abs_TSB (Rep_TSB b |` cs)"
  
  abbreviation tsbRestrict_abbr :: "TSB \<Rightarrow> channel set \<Rightarrow> TSB" (infix "\<bar>" 65)
  where "b\<bar>cs \<equiv> tsbRestrict cs b"
    


lemma tsdom_conc [simp]: "tsdom2 ([\<surd>] \<bullet>+ ts) = tsdom2 ts"
by(simp add: tsconc_def espf2tspf_def tsdom2_def)

(* ----------------------------------------------------------------------- *)
  subsection \<open>Definition of "Timed Stream (Bundle) Processing Function"\<close>
(* ----------------------------------------------------------------------- *)


  (* normal wellformed definition, similar to SPF *)
  (* an TSPF has a fixed input-channel-set and output-set.  *)
  definition tspf_wellformed :: "(TSB \<rightharpoonup> TSB) \<Rightarrow> bool" where
  "tspf_wellformed f \<equiv> \<exists>In Out. \<forall>b. (b \<in> dom f \<longleftrightarrow> tsbDom b = In) \<and> 
    (b \<in> dom f \<longrightarrow> tsbDom (the (f b)) = Out)"

  definition tspf_weakCausality :: "(TSB \<rightharpoonup> TSB) \<Rightarrow> bool" where
  "tspf_weakCausality f \<equiv> (\<forall>i. \<forall>b1 b2. (b1\<in> dom f \<and> b2 \<in>dom f\<and> tsbTTake i b1 = tsbTTake i b2) 
      \<longrightarrow> (tsbTTake i (the (f b1)) = tsbTTake i (the (f b2))))" 


  (* A component may only react one time-stamp after it received the input *)
  definition tspf_strongCausality :: "(TSB \<rightharpoonup> TSB) \<Rightarrow> bool" where
  "tspf_strongCausality f \<equiv> (\<forall>i. \<forall>b1 b2. (b1\<in> dom f \<and> b2 \<in>dom f\<and> tsbTTake i b1 = tsbTTake i b2) 
      \<longrightarrow> (tsbTTake (Suc i) (the (f b1)) = tsbTTake (Suc i) (the (f b2))))" 

   definition tspf_welltyped ::"(TSB \<rightharpoonup> TSB) \<Rightarrow> bool" where
   "tspf_welltyped f \<equiv> tspf_strongCausality f \<and> tspf_wellformed f"

  lemma tspf_strongc_exists: "tspf_strongCausality [(Abs_TSB empty) \<mapsto> (Abs_TSB empty)]"
  by(simp add: tspf_strongCausality_def)

  lemma [simp]: assumes "tsb_welltyped x"
  shows "Rep_TSB (Abs_TSB x) = x"
  by (simp add: Abs_TSB_inverse assms)

  lemma tspf_wellformed_exists: "tspf_wellformed [Abs_TSB Map.empty \<mapsto> Abs_TSB Map.empty]"
  apply(simp add: tspf_wellformed_def tsbDom_def dom_def tsb_welltyped_def)
  apply(rule+)
  by (smt Abs_TSB_inverse Collect_empty_eq Rep_TSB_inject dom_def dom_eq_empty_conv mem_Collect_eq option.collapse tsb_welltyped_def)
  

  typedef TSPF = "{F :: TSB \<rightharpoonup> TSB. tspf_welltyped F}"
  using tspf_strongc_exists tspf_wellformed_exists tspf_welltyped_def by auto

setup_lifting type_definition_TSPF




(* ----------------------------------------------------------------------- *)
  subsubsection \<open>Definition on TSPF\<close>
(* ----------------------------------------------------------------------- *)


  (* Input Channel set of an TSPF-Component *)
  definition tspfDom :: "TSPF \<Rightarrow> channel set" where
  "tspfDom F = tsbDom (SOME b. b \<in> dom (Rep_TSPF F))"

  (* Output Channel set of an TSPF-Component *)
  definition tspfRan :: "TSPF \<Rightarrow> channel set" where
  "tspfRan F = tsbDom (SOME b. b \<in> ran (Rep_TSPF F))"


  (* helper definition for composition. Later used to show that the result is indeed a correct TSPF *)
  definition tspfCompHelper :: "TSPF => TSPF => (TSB \<rightharpoonup> TSB)"  where
  "tspfCompHelper f1 f2 \<equiv> 
  let I1  = tspfDom f1;  (* Input channels of component 1 *)
      I2  = tspfDom f2;  (* Input channels of component 2 *)
      O1  = tspfRan f1;  (* Output channels of component 1 *)
      O2  = tspfRan f2;  (* Output channels of component 2 *)
      L   = (I1 \<inter> O2) \<union> (I2 \<inter> O1); (* Internal Channels *)
      In  = (I1 \<union> I2) - L; (* Input channels of the composed component *)
      Out = (O1 \<union> O2) - L  (* Output channels of the composed component *)
  in (\<lambda> b . (tsbDom b = In) \<leadsto> THE y . y\<in>{ z \<bar> Out   | z .
          z \<bar> In = b
      \<and>   z \<bar> O1 = the (Rep_TSPF f1 (z \<bar> I1))
      \<and>   z \<bar> O2 = the (Rep_TSPF f2 (z \<bar> I2)) })"
      (* \<and> sbDom\<cdot>z = (I1\<union>I2\<union>O1\<union>O2) *) 
  
  text {* composition operator *}
  definition tspfComp :: "TSPF \<Rightarrow> TSPF \<Rightarrow> TSPF" (infixl "\<otimes>" 50)  where
  "tspfComp f1 f2 \<equiv> Abs_TSPF (tspfCompHelper f1 f2)"



(* ----------------------------------------------------------------------- *)
  subsubsection \<open>Lemmas on TSPF\<close>
(* ----------------------------------------------------------------------- *)

lemma tspfcomp_well [simp]: "tspf_wellformed (tspfCompHelper f1 f2)"
sorry

lemma tspfcomp_dom [simp]: "tspfDom(f1\<otimes>f2) = (tspfDom f1 \<union> tspfDom f2) 
            - ((tspfDom f1 \<inter> tspfRan f2) \<union> (tspfDom f2 \<inter> tspfRan f1))"
sorry

(* composit operator is commutative *)
lemma tspfcomp_commute: "(a \<otimes> b) = (b \<otimes> a)"
apply(simp add: tspfComp_def tspfCompHelper_def Let_def)
by (metis Collect_conj_eq Int_commute Un_commute setcompr_eq_image)

(* toDo: composite operator is associative *)
  (* stronger / different assumtions needed \<Or>? *)
lemma assumes "tspfDom a \<inter> tspfDom b = {}"
              "tspfDom b \<inter> tspfDom c = {}"
              "tspfDom a \<inter> tspfDom c = {}"

              "tspfRan a \<inter> tspfRan b = {}" (*nötig ? *)
              "tspfRan b \<inter> tspfRan c = {}"
              "tspfRan a \<inter> tspfRan c = {}"
     shows "((a \<otimes> b) \<otimes> c) = (a \<otimes> (b \<otimes> c))"
apply(simp add: tspfComp_def tspfCompHelper_def Let_def)
oops





(* ----------------------------------------------------------------------- *)
  subsection \<open>Definition of "Timed Stream Processing Specifications"\<close>
(* ----------------------------------------------------------------------- *)

definition tsps_wellformed :: "TSPF set \<Rightarrow> bool" where
"tsps_wellformed S \<equiv> \<exists>In Out. \<forall> f\<in>S . (tspfDom f = In \<and> tspfRan f=Out) "

(* Timed Stream Processing Specifications *)
typedef TSPS = "{S :: TSPF set . tsps_wellformed S }"
using tsps_wellformed_def by auto

setup_lifting type_definition_TSPS




(* ----------------------------------------------------------------------- *)
  subsubsection \<open>Definition on TSPS\<close>
(* ----------------------------------------------------------------------- *)

definition tspsDom :: "TSPS \<Rightarrow> channel set" where
"tspsDom S = tspfDom (SOME f. f\<in> Rep_TSPS S)"

definition tspsRan :: "TSPS \<Rightarrow> channel set" where
"tspsRan S = tspfRan (SOME f. f\<in> Rep_TSPS S)"

definition tspsComp :: "TSPS \<Rightarrow> TSPS \<Rightarrow> TSPS" (infixl "\<Otimes>" 50) where 
"tspsComp S1 S2 \<equiv> let repS1 = Rep_TSPS S1;
                      repS2 = Rep_TSPS S2     in
                  Abs_TSPS {f1 \<otimes> f2 | f1 f2. f1\<in>repS1 \<and> f2\<in>repS2}"




(* ----------------------------------------------------------------------- *)
  subsubsection \<open>Lemmas on TSPS\<close>
(* ----------------------------------------------------------------------- *)

lemma tsps_eq: assumes "\<And>f1 . f1\<in>(Rep_TSPS S1) \<Longrightarrow> f1\<in>(Rep_TSPS S2)" 
      and "\<And>f2 . f2\<in>(Rep_TSPS S2) \<Longrightarrow> f2\<in>(Rep_TSPS S1)"
  shows "S1 = S2"
by (metis (full_types) Rep_TSPS_inverse assms(1) assms(2) equalityI subsetI)


lemma [simp]: assumes "tsps_wellformed x" 
  shows "Rep_TSPS (Abs_TSPS x) = x"
by (simp add: Abs_TSPS_inverse assms)

lemma tspsComp_well [simp]: "tsps_wellformed {f1 \<otimes> f2 | f1 f2. f1\<in> (Rep_TSPS S1) \<and> f2\<in>(Rep_TSPS S2)}"
proof (cases "(Rep_TSPS S1) = {} \<or> (Rep_TSPS S2) = {}")
  case True thus ?thesis
    by (smt Collect_cong Rep_TSPS empty_def mem_Collect_eq) 
  next
  case False
  thus ?thesis sorry
qed

(* composite operator in TSPS is commutative *)
lemma tspscomp_commute: "(X \<Otimes> Y) = (Y \<Otimes> X)"
apply(simp add: tspsComp_def)
using tspfcomp_commute by (metis (no_types, lifting))

(* The empty-specification composed with anything is again empty *)
lemma [simp]: "(Abs_TSPS {}) \<Otimes> X = (Abs_TSPS {})"
by(simp add: tspsComp_def tsps_wellformed_def)

(* on one-element sets the \<Otimes>-operator behaves exactly like \<otimes> *)
lemma [simp]: "(Abs_TSPS {f1}) \<Otimes> (Abs_TSPS {f2}) = Abs_TSPS{f1\<otimes>f2}"
by(simp add: tspsComp_def tsps_wellformed_def)










(* ----------------------------------------------------------------------- *)
  section \<open>Alternating Bit Protocol\<close>
(* ----------------------------------------------------------------------- *)




(* Send component *)



(* this function describes the "Send" part of the Alternating Bit Protocol *)

(* the 3. Input saves the time since the last message was sent *)
(* the 4. Input is the previous Message (prevM), in case this Message needs to be resend *)
definition send2 :: "data event stream \<Rightarrow> bool event stream \<Rightarrow> nat \<Rightarrow> (data\<times>bool) \<Rightarrow> (data\<times>bool) event stream " where
                                                         (* count    previous *)
"send2 \<equiv> \<mu> f . (\<lambda> input asEvent count prevTupel. 
  (* if inputs are empty abort *)
  if (input = \<epsilon> \<or> asEvent = \<epsilon>) then \<epsilon> else

    let newTupel = (inv Msg (shd input), \<not> snd prevTupel) in
                                      (* 2. element in tupel *)

    (* correct response from Recv arrived, send next Data element *)
    if(shd asEvent = Msg (snd prevTupel)) then <[Msg newTupel, \<surd>]> \<bullet> f (srt\<cdot>input) (srt\<cdot>asEvent) 0 newTupel 
     (* bestätigung angekommen *)                                   (* delete first tick     counterReset *)
    else 
      (* if timeout (more than 3 ticks without response from Recv) then resend message *)
      if (count = 4) then (<[Msg prevTupel,\<surd>]>) \<bullet> f input (srt\<cdot>asEvent) 0 prevTupel  
      
      (* no timeout, no correct response ... *)
      (* counter = 0,1,2,3 *)
      else \<up>\<surd> \<bullet> f input (srt\<cdot>asEvent) (Suc count) prevTupel)"


definition send_helper :: "data tstream \<Rightarrow> bool tstream \<Rightarrow> (data\<times>bool) tstream" where
"send_helper input as \<equiv>
    let initialBit= False ;
        inS       = Rep_tstream input ; (* go inside tstreams, work with event streams*)
        asEvent   = Rep_tstream as;
        asAddHead = \<up>(Msg initialBit) \<bullet> asEvent in
  Abs_tstream (send2 inS asAddHead 0 (undefined, \<not>initialBit))"
(* go back to tstreams *)



(* Send-Component *)
  (* c1  \<rightarrow> Input,  Data *)
  (* c2  \<rightarrow> Input,  Bit  *)
  (* c3  \<rightarrow> Output, Data\<times>Bit  *)
lift_definition Send :: TSPF is
"\<lambda>b. (tsbDom b = {c1,c2}) \<leadsto> 
    let input = m2d (b \<close> c1);
        as    = m2b (b \<close> c2);
        ds    = db2m (send_helper input as) in
    Abs_TSB [c3 \<mapsto> [\<surd>] \<bullet>+ ds]"
apply(simp add: tspf_welltyped_def Let_def)
apply rule+
sorry


(* Send hat kein Oracel, ist also deterministisch *)
lift_definition SEND :: TSPS is "{Send}"
using tsps_wellformed_def by auto




(* From here: Recv definition *)


(* c4 \<rightarrow> Input, (data,bit) *)
(* c5 \<rightarrow> Output, data without duplication  *)
(* c6 \<rightarrow> Output, bit *)
lift_definition Recv :: TSPF is
"(\<lambda>b. (tsbDom b = {c4}) \<leadsto> 
    let dr = [\<surd>] \<bullet>+ m2db (b \<close> c4); (* the \<surd> is there to ensure strong causality *)
        drNoDup = tsrcdups dr;
        out = d2m (tstprojfst drNoDup);
        ar  = b2m (tstprojsnd dr)   in 
    Abs_TSB [c5 \<mapsto> out, c6 \<mapsto> ar ])"
sorry

lift_definition RECV :: TSPS is "{Recv}"
using tsps_wellformed_def by auto




(* From here: Medium definition *)

(* tstream kein CPO, event stream allerdings, daher konvertierung *)
definition outswitch2 :: "'a event stream \<Rightarrow> bool stream \<Rightarrow> 'a event stream" where
"outswitch2 \<equiv> \<mu> f . (\<lambda>input oracle . 
  (* abort if inputs are empty *)
  if(input=\<epsilon> \<or> oracle = \<epsilon>) then \<epsilon> else 
    (* ignore -Tick- in input stream *)
    if (shd input = \<surd>) then \<up>\<surd> \<bullet> f (srt\<cdot>input) oracle else 
      (* if oracle is True then -shd input- is in the output stream *)
      if (shd oracle) then \<up>(shd input) \<bullet> f (srt\<cdot>input) (srt\<cdot>oracle) 
        (* otherwise delete -shd input- *)
        else f (srt\<cdot>input) (srt\<cdot>oracle) ) "

definition outswitch :: "'a tstream \<Rightarrow> bool stream \<Rightarrow> 'a tstream" where
"outswitch input oracle = [\<surd>] \<bullet>+ Abs_tstream (outswitch2 (Rep_tstream input) oracle)"
                            (* \<bullet>+ = concat tStream *)
  
definition mediumTSPF :: "channel \<Rightarrow> channel \<Rightarrow> bool stream \<Rightarrow> TSPF" where
"mediumTSPF cFrom cTo oracle \<equiv> Abs_TSPF (\<lambda> b. (tsbDom b = {cFrom}) \<leadsto> 
          Abs_TSB [cTo \<mapsto> outswitch (b\<close>cFrom) oracle])"
                                    (* getChannel *)

definition medium :: "channel \<Rightarrow> channel \<Rightarrow> TSPF set" where
"medium cFrom cTo = { (mediumTSPF cFrom cTo oracle) | oracle .  #(sfilter{True}\<cdot>oracle)=\<infinity> }"


(* c3 \<rightarrow> Input, data\<times>bool *)
(* c4 \<rightarrow> Output, data\<times>bool *)
lift_definition MED1 :: TSPS is "medium c3 c4"
sorry

lift_definition MED2 :: TSPS is "medium c6 c2"
sorry




(* ----------------------------------------------------------------------- *)
  subsection \<open>Lemmas on ABP\<close>
(* ----------------------------------------------------------------------- *)

lemma send_dom [simp]: "tspfDom Send = {c1,c2}"
apply(simp add: tspfDom_def Send.rep_eq)
apply(simp add: tsbDom_def tsb_welltyped_def)
sorry

lemma send_ran [simp]: "tspfRan Send = {c3}"
sorry

lemma medium_dom [simp]:"tspfDom (mediumTSPF cFrom cTo oracle) = {cFrom}"
apply(simp add: tspfDom_def mediumTSPF_def)
sorry

lemma medium_ran [simp]:"tspfRan (mediumTSPF cFrom cTo oracle) = {cTo}"
apply(simp add: tspfRan_def mediumTSPF_def)
sorry

lemma "mediumTSPF cFrom cTo oracle"
(* lemmas über outswitch *)
lemma [simp]:"cont (\<lambda> f . (\<lambda>input oracle . 
  (* abort if inputs are empty *)
  if(input=\<epsilon> \<or> oracle = \<epsilon>) then \<epsilon> else 
    (* ignore -Tick- in input stream *)
    if (shd input = \<surd>) then \<up>\<surd> \<bullet> f (srt\<cdot>input) oracle else 
      (* if oracle is True then -shd input- is in the output stream *)
      if (shd oracle) then \<up>(shd input) \<bullet> f (srt\<cdot>input) (srt\<cdot>oracle) 
        (* otherwise delete -shd input- *)
        else f (srt\<cdot>input) (srt\<cdot>oracle) ))"
sorry

lemma outswitch2_eps [simp]: "outswitch2 \<epsilon> oracle = \<epsilon>"
by (subst outswitch2_def [THEN fix_eq2], auto)

lemma outswitch2_eps2 [simp]: "outswitch2 ts \<epsilon> = \<epsilon>"
by (subst outswitch2_def [THEN fix_eq2], auto)

lemma outswitch2_tick: assumes "oracle \<noteq> \<epsilon>"
  shows "outswitch2 (\<up>\<surd>\<bullet>ts) oracle = \<up>\<surd> \<bullet> outswitch2 ts oracle"
using assms by (subst outswitch2_def [THEN fix_eq2], auto)

lemma outswitch2_true:"outswitch2 (\<up>(Msg a) \<bullet> ts) (\<up>True \<bullet> os) = \<up>(Msg a) \<bullet> outswitch2 ts os"
by (subst outswitch2_def [THEN fix_eq2], auto)

lemma outswitch2_false: "outswitch2 (\<up>(Msg a) \<bullet> ts) (\<up>False \<bullet> os) = outswitch2 ts os"
by (subst outswitch2_def [THEN fix_eq2], auto)


lemma outswitch2_len [simp]: assumes "#(sfilter{True}\<cdot>oracle)=\<infinity>"
  shows "#(outswitch2 ts oracle) \<le> #ts"
sorry

lemma outswitch2_ticks [simp]: assumes "#oracle = \<infinity>"
  shows "#(sfilter {\<surd>}\<cdot>(outswitch2 ts oracle)) = #(sfilter {\<surd>}\<cdot>ts)"
sorry

lemma [simp]:  "Rep_tstream (Abs_tstream (outswitch2 (Rep_tstream ts) oracle)) = (outswitch2 (Rep_tstream ts) oracle)"
sorry

lemma outswitch_eps [simp]: "outswitch s1 oracle = Abs_tstream (\<up>\<surd>)"
apply (simp add: outswitch_def s1.rep_eq tsconc_def espf2tspf_def)
by (metis s1.abs_eq s1.rep_eq sconc_snd_empty)

lemma outswitch_tick: assumes "oracle \<noteq> \<epsilon>"
  shows "outswitch ([\<surd>]\<bullet>+ts) oracle = [\<surd>] \<bullet>+ outswitch ts oracle"
by(simp add: outswitch_def tsconc_def espf2tspf_def outswitch2_tick assms)





(* hier kommt die echte komposition *)

definition SendMed1:: "bool stream \<Rightarrow> TSPF" where
"SendMed1 oracle \<equiv> Abs_TSPF (\<lambda>b. (tsbDom b = {c1,c2}) \<leadsto> 
  Abs_TSB [c4 \<mapsto> (outswitch (the ((Rep_TSPF Send) b) \<close> c3) oracle)])"



lift_definition SENDMED1 :: TSPS is 
  "{ SendMed1 oracle | oracle .  #(sfilter{True}\<cdot>oracle)=\<infinity> }"
sorry

lemma "({c3} \<union> {c4} - ({c1, c2} \<inter> {c4} \<union> {c3} \<inter> {c3})) = {c4}"
sorry

lemma assumes "g = h"
  shows "Abs_TSPF(\<lambda>b. (tsbDom b = {c1, c2})\<leadsto>g b) = Abs_TSPF(\<lambda>b. (tsbDom b = {c1, c2})\<leadsto>h b)"
sorry

lemma comp2SendMed2: assumes "#(sfilter{True}\<cdot>oracle)=\<infinity>"
  shows "Send \<otimes> (mediumTSPF c3 c4 oracle) = SendMed1 oracle"
sorry

lemma sendMedComp: "SEND \<Otimes> MED1 = Abs_TSPS {Send \<otimes> (mediumTSPF c3 c4 oracle) | oracle .  #(sfilter{True}\<cdot>oracle)=\<infinity>}"
apply(simp add: tspsComp_def SEND.rep_eq MED1.rep_eq medium_def)
by metis

lemma "SEND \<Otimes> MED1 = SENDMED1"
by (smt Collect_cong SENDMED1_def comp2SendMed2 sendMedComp)
(*
proof (rule tsps_eq)
  fix f1
  assume f1_def: "f1 \<in> Rep_TSPS (SEND \<Otimes> MED1)"
  hence "f1 \<in> Rep_TSPS SENDMED1"
  by (smt Collect_cong SENDMED1_def comp2SendMed2 sendMedComp)
 *)
(* hence f1_def2: "f1 \<in>{Send \<otimes> (mediumTSPF c3 c4 oracle) | oracle .  #(sfilter{True}\<cdot>oracle)=\<infinity>}"
    by (smt Collect_cong SENDMED1.rep_eq SENDMED1_def comp2SendMed2 sendMedComp)
  obtain oracel where "f1 = (Send \<otimes> (mediumTSPF c3 c4 oracel)) \<and> #(sfilter{True}\<cdot>oracel)=\<infinity>"
    using f1_def2 by blast
  thus "f1 \<in> Rep_TSPS SENDMED1" by (smt SENDMED1.rep_eq comp2SendMed2 mem_Collect_eq)
*)


(* example stream used als Input for the ABP-component*)
lift_definition tInHelper :: "M tstream" is
"<[(Msg (D (\<D> 1))), (Msg (D (\<D> 2)))]>"
by simp

(* liftet --tInHelper-- to a TSB *)
lift_definition tIn :: TSB is 
"[c1 \<mapsto> tInHelper]"
apply(simp add: tsb_welltyped_def tsdom2_def tInHelper.rep_eq)
by auto



definition oneComp :: "bool stream \<Rightarrow> bool stream \<Rightarrow> TSPF" where
"oneComp oracle1 oracle2 \<equiv> let med1 = (mediumTSPF c3 c4 oracle1);
                               med2 =  (mediumTSPF c6 c2 oracle2) in
                           (Send \<otimes> med1) \<otimes> (Recv \<otimes> med2)"

lemma oneComp_dom[simp]: "tspfDom (oneComp o1 o2) = {c1}"
sorry

lemma oneComp_ran[simp]: "tspfRan (oneComp o1 o2) = {c5}"
sorry

lemma goalTSPF [simp]: assumes "#(sfilter{True}\<cdot>oracle1)=\<infinity>" and "#(sfilter{True}\<cdot>oracle2)=\<infinity>"
  shows "tsabs ((the ((Rep_TSPF (oneComp oracle1 oracle2)) tIn)) \<close> c5 ) = tsabs tInHelper"
sorry

lemma goalTSPF2 [simp]: assumes "#(sfilter{True}\<cdot>oracle1)=\<infinity>" 
        and "#(sfilter{True}\<cdot>oracle2)=\<infinity>" and "tsbDom input = {c1}" 
  shows "tsabs ((the ((Rep_TSPF (oneComp oracle1 oracle2)) input)) \<close> c5 ) = tsabs (input \<close> c1)"
sorry

(* the one component to rule them all *)
definition ONECOMP :: TSPS where
"ONECOMP \<equiv> (SEND \<Otimes> MED1) \<Otimes> (RECV \<Otimes> MED2)"

lift_definition OneCompTSPS ::TSPS is 
"{oneComp oracle1 oracle2 | 
                      oracle1 oracle2 .  #(sfilter{True}\<cdot>oracle1)=\<infinity> \<and>  #(sfilter{True}\<cdot>oracle2)=\<infinity>}"
apply(simp add: tsps_wellformed_def)
by fastforce

lemma ONE2one: "ONECOMP = OneCompTSPS"
apply(simp add: OneCompTSPS_def)
apply(simp add: ONECOMP_def oneComp_def tspsComp_def Let_def)
apply(simp add: MED1.rep_eq MED2.rep_eq SEND.rep_eq RECV.rep_eq)
apply(simp add: medium_def)
by (metis (no_types, hide_lams))


(* Goal1 : *)
lemma assumes "f \<in> (Rep_TSPS ONECOMP)"
  shows "tsabs ((the ((Rep_TSPF f) tIn)) \<close> c5 ) = tsabs tInHelper"
by (smt Abs_TSPS_inverse MED1.rep_eq MED2.rep_eq ONECOMP_def RECV.rep_eq SEND.rep_eq assms goalTSPF medium_def mem_Collect_eq oneComp_def singletonD tspsComp_def tspsComp_well)



(* Final Goal *)
(* take an arbitrary stream in the spcification of ABP-component 
    and an arbitrary input with correct domain *)
lemma assumes "f \<in> (Rep_TSPS ONECOMP)" and "tsbDom input = {c1}" 
  shows "tsabs ((the ((Rep_TSPF f) input)) \<close> c5 ) = tsabs (input \<close> c1)"
by (smt Abs_TSPS_inverse MED1.rep_eq MED2.rep_eq ONECOMP_def RECV.rep_eq SEND.rep_eq assms goalTSPF2 medium_def mem_Collect_eq oneComp_def singletonD tspsComp_def tspsComp_well)





end
