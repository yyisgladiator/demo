theory Medium_SPS

imports "../SPS" "../../timesyn/tsynBundle"


(* Description: Rekursive Medium definition for Dennis group. Since the Medium does not yet exist
    as uspec the lemma will be "sorry" and proven later *)
begin 

(****************************************************************************)
    section \<open>State Datatype\<close>
(****************************************************************************)
    text \<open>Autogenerated from MAA, exactly like the deterministic automaton\<close>

(* This are the actual states from MAA *)
datatype MediumSubstate = TheOne (* Das MAA-Modell hat nur diesen einen State *)

(* And these have also the variables *)
datatype MediumState = State MediumSubstate nat

fun getSubState :: "MediumState \<Rightarrow> MediumSubstate" where
"getSubState (State automaton_s automaton_sum) = automaton_s"

fun getCounter :: "MediumState \<Rightarrow> nat" where
"getCounter (State automaton_s automaton_counter) = automaton_counter"





(* Platzhalter für das finale Medium h lemma *)
(* NEVER use h_MED_def instead use the following lemmata *)
definition h_MED :: "MediumState \<Rightarrow> 'm SPS" where
"h_MED = undefined"





(****************************************************************************)
    section \<open>Definitions\<close>
(****************************************************************************)
    text \<open>Not every function we need exists. So here some dummies and the description\<close>



(* prepends the SB to every input ! *)
(* so internally it will call "ufApplyIn sbConcEq". Marc is defining that function right now *)
(* notice that this function is not cont *)
definition spsConcIn :: "'m SB \<Rightarrow> 'm SPS \<Rightarrow> 'm SPS" where
"spsConcIn = undefined"


(* Prepends the SB to every output ! *)
(* internally it calls "spfConc" which in turn calls "ufApplyOut sbConcEq" *)
(* It's cont without conditions. The domain of the SB does not change the type of the SPS *)
definition spsConcOut :: "'m SB \<Rightarrow> 'm SPS \<rightarrow> 'm SPS" where
"spsConcOut = undefined"


(* Basically a huge Union *)
(* an SPF is in the resulting SPS iff it is contained in one of the input SPS *)
(* NOT cont *)
definition spsFlatten :: "'m SPS set \<Rightarrow> 'm SPS" where
"spsFlatten = undefined"


(* creates an SB with the element on channel (\<C> ''Input Channel'') *)
definition makeInput::"'a \<Rightarrow> 'm SB"  where
"makeInput = undefined"

(* creates an SB with the element on channel (\<C> ''Output Channel'') *)
definition makeOutput::"'a \<Rightarrow> 'm SB"  where
"makeOutput = undefined"

(* creates an SB with "null" on the given channel *)
definition makeNull:: "channel \<Rightarrow> 'm SB" where
"makeNull = undefined"




(****************************************************************************)
    section \<open>Lemma\<close>
(****************************************************************************)
    text \<open>The lemma we can generate for you\<close>




subsection \<open>Lemma only over SPS\<close>


(* counter not null, drop every message and count one down *)
lemma "spsConcIn (makeInput m) (h_MED (State TheOne (Suc n))) = spsConcOut (makeNull (\<C> ''Output Channel''))\<cdot>(h_MED (State TheOne (Suc n)))"
  oops

(* If a "null" comes in send it out and stay in the same state *) 
lemma "spsConcIn (makeNull (\<C> ''Input Channel'')) (h_MED state) = spsConcOut (makeNull (\<C> ''Output Channel''))\<cdot>(h_MED state)"
  oops

(* Counter hit zero, so pass the message and reset the countdown to a random value *)
lemma "spsConcIn (makeInput m) (h_MED (State TheOne 0)) = spsConcOut (makeOutput m)\<cdot>(spsFlatten {h_MED (State TheOne n) |  n. True})"
  oops







  subsection\<open>Lemma that convert to SPF\<close>

(* get the "SPF set" from the SPS *)
definition h_MED_SET :: "MediumState \<Rightarrow> 'm SPF set" where
"h_MED_SET state = Rep_rev_uspec (h_MED state)"


(* counter not null, drop every message and count one down *)
lemma assumes "spf \<in> h_MED_SET (State TheOne (Suc n))"
  shows "\<exists> stepSpf. stepSpf \<in> h_MED_SET (State TheOne n) 
    \<and> spf \<rightleftharpoons> (ubConc (makeInput m)\<cdot>sb) = ubConc (makeNull (\<C> ''Output Channel''))\<cdot>(stepSpf \<rightleftharpoons> sb)"
  oops

(* If a "null" comes in send it out and stay in the same state *)
lemma assumes "spf \<in> h_MED_SET state"
  shows "\<exists> stepSpf. stepSpf \<in> h_MED_SET state 
    \<and> spf \<rightleftharpoons> (ubConc (makeNull (\<C> ''Input Channel''))\<cdot>sb) = ubConc (makeNull (\<C> ''Output Channel''))\<cdot>(stepSpf \<rightleftharpoons> sb)"
  oops

(* Counter hit zero, so pass the message and reset the countdown to a random value *)
lemma assumes "spf \<in> h_MED_SET (State TheOne 0)"
  shows "\<exists> n stepSpf. stepSpf \<in> h_MED_SET (State TheOne n) 
    \<and> spf \<rightleftharpoons> (ubConc (makeInput m)\<cdot>sb) = ubConc (makeOutput m)\<cdot>(stepSpf \<rightleftharpoons> sb)"
  oops


end