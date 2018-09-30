(*
 * DO NOT MODIFY!
 * This file was generated from Sender.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Sep 5, 2018 3:18:21 PM by isartransformer 1.0.0
 *)
theory SenderAutomaton
  imports bundle.tsynBundle automat.dAutomaton

begin

(* TODO Das sollte vielleicht wo anders hin *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"

section \<open>Datatype definition\<close>

datatype senderMessage = SenderBool "bool" | SenderNat "nat" | SenderPair_SenderNat_SenderBool "(nat\<times>bool)"
instance senderMessage :: countable
  apply(intro_classes)
  by(countable_datatype)

instantiation senderMessage :: message
begin
  fun ctype_senderMessage :: "channel  \<Rightarrow> senderMessage set" where
  "ctype_senderMessage c = (
    if c = \<C> ''as'' then range SenderBool else
    if c = \<C> ''i'' then range SenderNat else
    if c = \<C> ''ds'' then range SenderPair_SenderNat_SenderBool else
    {})"
    instance
    by(intro_classes)
end


section \<open>Helpers to create a bundle from a single raw element\<close>

lift_definition createAsBundle :: "bool \<Rightarrow> senderMessage tsyn SB" is
"\<lambda>x. [\<C> ''as'' \<mapsto> \<up>(Msg (SenderBool x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createIBundle :: "nat \<Rightarrow> senderMessage tsyn SB" is
"\<lambda>x. [\<C> ''i'' \<mapsto> \<up>(Msg (SenderNat x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createDsBundle :: "(nat\<times>bool) \<Rightarrow> senderMessage tsyn SB" is
"\<lambda>x. [\<C> ''ds'' \<mapsto> \<up>(Msg (SenderPair_SenderNat_SenderBool x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp


section \<open>Helpers to create a bundle from a single tsyn element\<close>

fun createTsynAsBundle :: "bool tsyn \<Rightarrow> senderMessage tsyn SB" where
"createTsynAsBundle (Msg x) = (createAsBundle x)" |
"createTsynAsBundle null = (tsynbNull (\<C> ''as''))"

fun createTsynIBundle :: "nat tsyn \<Rightarrow> senderMessage tsyn SB" where
"createTsynIBundle (Msg x) = (createIBundle x)" |
"createTsynIBundle null = (tsynbNull (\<C> ''i''))"

fun createTsynDsBundle :: "(nat\<times>bool) tsyn \<Rightarrow> senderMessage tsyn SB" where
"createTsynDsBundle (Msg x) = (createDsBundle x)" |
"createTsynDsBundle null = (tsynbNull (\<C> ''ds''))"


section \<open>Helpers to create a bundle from a tsyn list of elements\<close>

fun createLongAsBundle :: "(bool tsyn) list \<Rightarrow> senderMessage tsyn SB" where
"createLongAsBundle (x#xs) = ubConcEq (createTsynAsBundle x)\<cdot>(createLongAsBundle xs)" |
"createLongAsBundle []     = ubLeast {\<C> ''as''}"

fun createLongIBundle :: "(nat tsyn) list \<Rightarrow> senderMessage tsyn SB" where
"createLongIBundle (x#xs) = ubConcEq (createTsynIBundle x)\<cdot>(createLongIBundle xs)" |
"createLongIBundle []     = ubLeast {\<C> ''i''}"

fun createLongDsBundle :: "((nat\<times>bool) tsyn) list \<Rightarrow> senderMessage tsyn SB" where
"createLongDsBundle (x#xs) = ubConcEq (createTsynDsBundle x)\<cdot>(createLongDsBundle xs)" |
"createLongDsBundle []     = ubLeast {\<C> ''ds''}"


section \<open>Lemmas for "createXBundle"\<close>

lemma createAsBundle_dom [simp]: "ubDom\<cdot>(createAsBundle x) = {\<C> ''as''}"
  by (simp add: createAsBundle.rep_eq ubdom_insert)

lemma createAsBundle_getch [simp]: "(createAsBundle x).(\<C> ''as'') = \<up>(Msg (SenderBool x))"
  by (simp add: createAsBundle.rep_eq ubgetch_insert)

lemma createAsBundle_len [simp]: "ubLen (createAsBundle x) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)

lemma createIBundle_dom [simp]: "ubDom\<cdot>(createIBundle x) = {\<C> ''i''}"
  by (simp add: createIBundle.rep_eq ubdom_insert)

lemma createIBundle_getch [simp]: "(createIBundle x).(\<C> ''i'') = \<up>(Msg (SenderNat x))"
  by (simp add: createIBundle.rep_eq ubgetch_insert)

lemma createIBundle_len [simp]: "ubLen (createIBundle x) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)

lemma createDsBundle_dom [simp]: "ubDom\<cdot>(createDsBundle x) = {\<C> ''ds''}"
  by (simp add: createDsBundle.rep_eq ubdom_insert)

lemma createDsBundle_getch [simp]: "(createDsBundle x).(\<C> ''ds'') = \<up>(Msg (SenderPair_SenderNat_SenderBool x))"
  by (simp add: createDsBundle.rep_eq ubgetch_insert)

lemma createDsBundle_len [simp]: "ubLen (createDsBundle x) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)


section \<open>Lemmas for "createTsynXBundle"\<close>

lemma createTsynAsBundle_dom [simp]: "ubDom\<cdot>(createTsynAsBundle x) = {\<C> ''as''}"
  by (cases x, simp_all)

lemma createTsynAsBundle_len [simp]: "ubLen (createTsynAsBundle x) = Fin 1"
  apply (cases x, simp_all)
  oops

lemma createTsynIBundle_dom [simp]: "ubDom\<cdot>(createTsynIBundle x) = {\<C> ''i''}"
  by (cases x, simp_all)

lemma createTsynIBundle_len [simp]: "ubLen (createTsynIBundle x) = Fin 1"
  apply (cases x, simp_all)
  oops

lemma createTsynDsBundle_dom [simp]: "ubDom\<cdot>(createTsynDsBundle x) = {\<C> ''ds''}"
  by (cases x, simp_all)

lemma createTsynDsBundle_len [simp]: "ubLen (createTsynDsBundle x) = Fin 1"
  apply (cases x, simp_all)
  oops


section \<open>Lemmas for "createLongXBundle"\<close>

lemma createLongAsBundle_dom [simp]: "ubDom\<cdot>(createLongAsBundle xs) = {\<C> ''as''}"
  proof (induction xs)
    case Nil then show ?case by simp
  next
    case (Cons a _)
      then show ?case
        proof (cases a)
          case (Msg _) then show ?thesis by (simp add: Cons.IH)
        next
          case null then show ?thesis by (simp add: Cons.IH)
        qed
  qed

lemma createLongAsBundle_len [simp]: "ubLen (createLongAsBundle xs) = Fin (length xs)"
  oops

lemma createLongIBundle_dom [simp]: "ubDom\<cdot>(createLongIBundle xs) = {\<C> ''i''}"
  proof (induction xs)
    case Nil then show ?case by simp
  next
    case (Cons a _)
      then show ?case
        proof (cases a)
          case (Msg _) then show ?thesis by (simp add: Cons.IH)
        next
          case null then show ?thesis by (simp add: Cons.IH)
        qed
  qed

lemma createLongIBundle_len [simp]: "ubLen (createLongIBundle xs) = Fin (length xs)"
  oops

lemma createLongDsBundle_dom [simp]: "ubDom\<cdot>(createLongDsBundle xs) = {\<C> ''ds''}"
  proof (induction xs)
    case Nil then show ?case by simp
  next
    case (Cons a _)
      then show ?case
        proof (cases a)
          case (Msg _) then show ?thesis by (simp add: Cons.IH)
        next
          case null then show ?thesis by (simp add: Cons.IH)
        qed
  qed

lemma createLongDsBundle_len [simp]: "ubLen (createLongDsBundle xs) = Fin (length xs)"
  oops


section \<open>Automaton definition\<close>

(* These are the actual states from MAA *)
datatype SenderSubstate = Sf | St

(* And these have also the variables *)
datatype SenderState = SenderState SenderSubstate (* buffer = *) "nat list" (* c = *) "nat"

(* Function to get the substate *)
fun getSenderSubState :: "SenderState \<Rightarrow> SenderSubstate" where
"getSenderSubState (SenderState s _ _) = s"

(* Functions to get the variables *)
fun getBuffer :: "SenderState \<Rightarrow> nat list" where
"getBuffer (SenderState _ var_buffer var_c) = var_buffer"

fun getC :: "SenderState \<Rightarrow> nat" where
"getC (SenderState _ var_buffer var_c) = var_c"


(* Helper that allows us to utilize pattern matching *)
fun senderTransitionH :: "(SenderState \<times> (senderMessage tsyn \<times> senderMessage tsyn)) \<Rightarrow> (SenderState \<times> senderMessage tsyn SB)" where
"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg (SenderBool port_as), \<^cancel>\<open>i\<mapsto>\<close>Msg (SenderNat port_i))) =
  (if((size var_buffer)>1 \<and> port_as=False) then ((SenderState St (prepend (butlast var_buffer) port_i) 3, (createDsBundle (Pair (last (butlast var_buffer)) True))))
   else if((size var_buffer)=1 \<and> port_as=False) then ((SenderState St (prepend (butlast var_buffer) port_i) 3, (createDsBundle (Pair port_i True))))
   else if((size var_buffer)=0) then ((SenderState Sf (prepend var_buffer port_i) 3, (createDsBundle (Pair port_i False))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=True) then ((SenderState Sf (prepend var_buffer port_i) (var_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=True) then ((SenderState Sf (prepend var_buffer port_i) 3, (createDsBundle (Pair (last var_buffer) False))))
   else (SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds''))))" |

"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg (SenderBool port_as), \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)>1 \<and> port_as=False) then ((SenderState St (butlast var_buffer) 3, (createDsBundle (Pair (last (butlast var_buffer)) True))))
   else if((size var_buffer)=1 \<and> port_as=False) then ((SenderState St (butlast var_buffer) var_c, (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)=0) then ((SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=True) then ((SenderState Sf var_buffer (var_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=True) then ((SenderState Sf var_buffer 3, (createDsBundle (Pair (last var_buffer) False))))
   else (SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds''))))" |

"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>Msg (SenderNat port_i))) =
  (if((size var_buffer)=0) then ((SenderState Sf (prepend var_buffer port_i) 3, (createDsBundle (Pair port_i False))))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState Sf (prepend var_buffer port_i) (var_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState Sf (prepend var_buffer port_i) 3, (createDsBundle (Pair (last var_buffer) False))))
   else (SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds''))))" |

"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)=0) then ((SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState Sf var_buffer 3, (createDsBundle (Pair (last var_buffer) False))))
   else (SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds''))))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg (SenderBool port_as), \<^cancel>\<open>i\<mapsto>\<close>Msg (SenderNat port_i))) =
  (if((size var_buffer)=0) then ((SenderState St (prepend var_buffer port_i) 3, (createDsBundle (Pair port_i True))))
   else if((size var_buffer)>1 \<and> port_as=True) then ((SenderState Sf (prepend (butlast var_buffer) port_i) 3, (createDsBundle (Pair (last (butlast var_buffer)) False))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=False) then ((SenderState St (prepend var_buffer port_i) (var_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=False) then ((SenderState St (prepend var_buffer port_i) 3, (createDsBundle (Pair (last var_buffer) True))))
   else if((size var_buffer)=1 \<and> port_as=True) then ((SenderState Sf (prepend (butlast var_buffer) port_i) 3, (createDsBundle (Pair port_i False))))
   else (SenderState St var_buffer var_c, (tsynbNull (\<C> ''ds''))))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg (SenderBool port_as), \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)=0) then ((SenderState St var_buffer var_c, (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>1 \<and> port_as=True) then ((SenderState Sf (butlast var_buffer) 3, (createDsBundle (Pair (last (butlast var_buffer)) False))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=False) then ((SenderState St var_buffer (var_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=False) then ((SenderState St var_buffer 3, (createDsBundle (Pair (last var_buffer) True))))
   else if((size var_buffer)=1 \<and> port_as=True) then ((SenderState Sf (butlast var_buffer) var_c, (tsynbNull (\<C> ''ds''))))
   else (SenderState St var_buffer var_c, (tsynbNull (\<C> ''ds''))))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>Msg (SenderNat port_i))) =
  (if((size var_buffer)=0) then ((SenderState St (prepend var_buffer port_i) 3, (createDsBundle (Pair port_i True))))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState St (prepend var_buffer port_i) (var_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState St (prepend var_buffer port_i) 3, (createDsBundle (Pair (last var_buffer) True))))
   else (SenderState St var_buffer var_c, (tsynbNull (\<C> ''ds''))))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)=0) then ((SenderState St var_buffer var_c, (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState St var_buffer (var_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState St var_buffer 3, (createDsBundle (Pair (last var_buffer) True))))
   else (SenderState St var_buffer var_c, (tsynbNull (\<C> ''ds''))))"

(* Transition function *)
fun senderTransition :: "(SenderState \<times> senderMessage tsyn sbElem) \<Rightarrow> (SenderState \<times> senderMessage tsyn SB)" where
"senderTransition (s,b) = (if dom(Rep_sbElem b) = {\<C> ''as'', \<C> ''i''} then senderTransitionH (s, (Rep_sbElem b\<rightharpoonup>\<C> ''as'', Rep_sbElem b\<rightharpoonup>\<C> ''i'')) else undefined)"

lift_definition SenderAutomaton :: "(SenderState, senderMessage tsyn) dAutomaton" is
"(senderTransition, SenderState St []  0, tsynbNull (\<C> ''ds''), {\<C> ''as'', \<C> ''i''}, {\<C> ''ds''})"
  by simp

definition SenderSPF :: "senderMessage tsyn SPF" where
"SenderSPF = da_H SenderAutomaton"


section \<open>Lemmata for the transitions\<close>

(* Line 33 in the MAA model *)
lemma tbd_0_0:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "spfConcIn  (createAsBundle port_as \<uplus> createIBundle port_i)\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (createDsBundle (Pair (last (butlast var_buffer)) True))\<cdot>(da_h SenderAutomaton (SenderState St (prepend (butlast var_buffer) port_i) 3))"
  oops

(* Line 35 in the MAA model *)
lemma tbd_0_1:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "spfConcIn  (createAsBundle port_as \<uplus> createIBundle port_i)\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (createDsBundle (Pair port_i True))\<cdot>(da_h SenderAutomaton (SenderState St (prepend (butlast var_buffer) port_i) 3))"
  oops

(* Line 43 in the MAA model *)
lemma tbd_0_2:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (createAsBundle port_as \<uplus> createIBundle port_i)\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (createDsBundle (Pair port_i False))\<cdot>(da_h SenderAutomaton (SenderState Sf (prepend var_buffer port_i) 3))"
  oops

(* Line 45 in the MAA model *)
lemma tbd_0_3:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "spfConcIn  (createAsBundle port_as \<uplus> createIBundle port_i)\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf (prepend var_buffer port_i) (var_c-1)))"
  oops

(* Line 47 in the MAA model *)
lemma tbd_0_4:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "spfConcIn  (createAsBundle port_as \<uplus> createIBundle port_i)\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (createDsBundle (Pair (last var_buffer) False))\<cdot>(da_h SenderAutomaton (SenderState Sf (prepend var_buffer port_i) 3))"
  oops

(* Line 34 in the MAA model *)
lemma tbd_1_0:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "spfConcIn  (createAsBundle port_as \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (createDsBundle (Pair (last (butlast var_buffer)) True))\<cdot>(da_h SenderAutomaton (SenderState St (butlast var_buffer) 3))"
  oops

(* Line 36 in the MAA model *)
lemma tbd_1_1:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "spfConcIn  (createAsBundle port_as \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St (butlast var_buffer) var_c))"
  oops

(* Line 38 in the MAA model *)
lemma tbd_1_2:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (createAsBundle port_as \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))"
  oops

(* Line 40 in the MAA model *)
lemma tbd_1_3:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "spfConcIn  (createAsBundle port_as \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer (var_c-1)))"
  oops

(* Line 41 in the MAA model *)
lemma tbd_1_4:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "spfConcIn  (createAsBundle port_as \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (createDsBundle (Pair (last var_buffer) False))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer 3))"
  oops

(* Line 44 in the MAA model *)
lemma tbd_2_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> createIBundle port_i)\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (createDsBundle (Pair port_i False))\<cdot>(da_h SenderAutomaton (SenderState Sf (prepend var_buffer port_i) 3))"
  oops

(* Line 46 in the MAA model *)
lemma tbd_2_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> createIBundle port_i)\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf (prepend var_buffer port_i) (var_c-1)))"
  oops

(* Line 48 in the MAA model *)
lemma tbd_2_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> createIBundle port_i)\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (createDsBundle (Pair (last var_buffer) False))\<cdot>(da_h SenderAutomaton (SenderState Sf (prepend var_buffer port_i) 3))"
  oops

(* Line 37 in the MAA model *)
lemma tbd_3_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))"
  oops

(* Line 39 in the MAA model *)
lemma tbd_3_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))"
  oops

(* Line 42 in the MAA model *)
lemma tbd_3_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (createDsBundle (Pair (last var_buffer) False))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer 3))"
  oops

(* Line 25 in the MAA model *)
lemma tbd_4_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (createAsBundle port_as \<uplus> createIBundle port_i)\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (createDsBundle (Pair port_i True))\<cdot>(da_h SenderAutomaton (SenderState St (prepend var_buffer port_i) 3))"
  oops

(* Line 27 in the MAA model *)
lemma tbd_4_1:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "spfConcIn  (createAsBundle port_as \<uplus> createIBundle port_i)\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (createDsBundle (Pair (last (butlast var_buffer)) False))\<cdot>(da_h SenderAutomaton (SenderState Sf (prepend (butlast var_buffer) port_i) 3))"
  oops

(* Line 28 in the MAA model *)
lemma tbd_4_2:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "spfConcIn  (createAsBundle port_as \<uplus> createIBundle port_i)\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St (prepend var_buffer port_i) (var_c-1)))"
  oops

(* Line 30 in the MAA model *)
lemma tbd_4_3:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "spfConcIn  (createAsBundle port_as \<uplus> createIBundle port_i)\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (createDsBundle (Pair (last var_buffer) True))\<cdot>(da_h SenderAutomaton (SenderState St (prepend var_buffer port_i) 3))"
  oops

(* Line 32 in the MAA model *)
lemma tbd_4_4:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "spfConcIn  (createAsBundle port_as \<uplus> createIBundle port_i)\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (createDsBundle (Pair port_i False))\<cdot>(da_h SenderAutomaton (SenderState Sf (prepend (butlast var_buffer) port_i) 3))"
  oops

(* Line 17 in the MAA model *)
lemma tbd_5_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (createAsBundle port_as \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))"
  oops

(* Line 18 in the MAA model *)
lemma tbd_5_1:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "spfConcIn  (createAsBundle port_as \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (createDsBundle (Pair (last (butlast var_buffer)) False))\<cdot>(da_h SenderAutomaton (SenderState Sf (butlast var_buffer) 3))"
  oops

(* Line 20 in the MAA model *)
lemma tbd_5_2:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "spfConcIn  (createAsBundle port_as \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer (var_c-1)))"
  oops

(* Line 22 in the MAA model *)
lemma tbd_5_3:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "spfConcIn  (createAsBundle port_as \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (createDsBundle (Pair (last var_buffer) True))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer 3))"
  oops

(* Line 24 in the MAA model *)
lemma tbd_5_4:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "spfConcIn  (createAsBundle port_as \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf (butlast var_buffer) var_c))"
  oops

(* Line 26 in the MAA model *)
lemma tbd_6_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> createIBundle port_i)\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (createDsBundle (Pair port_i True))\<cdot>(da_h SenderAutomaton (SenderState St (prepend var_buffer port_i) 3))"
  oops

(* Line 29 in the MAA model *)
lemma tbd_6_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> createIBundle port_i)\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St (prepend var_buffer port_i) (var_c-1)))"
  oops

(* Line 31 in the MAA model *)
lemma tbd_6_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> createIBundle port_i)\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (createDsBundle (Pair (last var_buffer) True))\<cdot>(da_h SenderAutomaton (SenderState St (prepend var_buffer port_i) 3))"
  oops

(* Line 19 in the MAA model *)
lemma tbd_7_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))"
  oops

(* Line 21 in the MAA model *)
lemma tbd_7_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer (var_c-1)))"
  oops

(* Line 23 in the MAA model *)
lemma tbd_7_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (tsynbNull (\<C> ''as'') \<uplus> tsynbNull (\<C> ''i''))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (createDsBundle (Pair (last var_buffer) True))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer 3))"
  oops


end