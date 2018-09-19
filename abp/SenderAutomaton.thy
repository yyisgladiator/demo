(*
 * DO NOT MODIFY!
 * This file was generated from Sender.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Sep 19, 2018 11:04:38 PM by isartransformer 1.0.0
 *)
theory SenderAutomaton
  imports bundle.tsynBundle automat.dAutomaton

begin

(* Helper for easier generation *)
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

(* Create one sbElem for all input streams *)
fun createSbElem_As_I :: "(bool tsyn) \<Rightarrow> (nat tsyn) \<Rightarrow> (senderMessage tsyn sbElem)" where
"createSbElem_As_I null null = Abs_sbElem [\<C> ''as'' \<mapsto> null, \<C> ''i'' \<mapsto> null]" |
"createSbElem_As_I (Msg port_as) null = Abs_sbElem [\<C> ''as'' \<mapsto> Msg (SenderBool port_as), \<C> ''i'' \<mapsto> null]" |
"createSbElem_As_I null (Msg port_i) = Abs_sbElem [\<C> ''as'' \<mapsto> null, \<C> ''i'' \<mapsto> Msg (SenderNat port_i)]" |
"createSbElem_As_I (Msg port_as) (Msg port_i) = Abs_sbElem [\<C> ''as'' \<mapsto> Msg (SenderBool port_as), \<C> ''i'' \<mapsto> Msg (SenderNat port_i)]"

(* Create one SB for all input streams *)
fun createBundle_As_I :: "(bool tsyn) \<Rightarrow> (nat tsyn) \<Rightarrow> (senderMessage tsyn SB)" where
"createBundle_As_I port_as  port_i  = (sbe2SB (createSbElem_As_I port_as  port_i ))"

lift_definition createAsBundle :: "bool \<Rightarrow> senderMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''as'' \<mapsto> Msg (SenderBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createIBundle :: "nat \<Rightarrow> senderMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''i'' \<mapsto> Msg (SenderNat x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createDsBundle :: "(nat\<times>bool) \<Rightarrow> senderMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''ds'' \<mapsto> Msg (SenderPair_SenderNat_SenderBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp


section \<open>Helpers to create a bundle from a single tsyn element\<close>

fun createTsynAsBundle :: "bool tsyn \<Rightarrow> senderMessage tsyn SB" where
"createTsynAsBundle (Msg x) = sbe2SB (createAsBundle x)" |
"createTsynAsBundle null = sbe2SB (sbeNull {\<C> ''as''})"

declare createTsynAsBundle.simps[simp del]

fun createTsynIBundle :: "nat tsyn \<Rightarrow> senderMessage tsyn SB" where
"createTsynIBundle (Msg x) = sbe2SB (createIBundle x)" |
"createTsynIBundle null = sbe2SB (sbeNull {\<C> ''i''})"

declare createTsynIBundle.simps[simp del]

fun createTsynDsBundle :: "(nat\<times>bool) tsyn \<Rightarrow> senderMessage tsyn SB" where
"createTsynDsBundle (Msg x) = sbe2SB (createDsBundle x)" |
"createTsynDsBundle null = sbe2SB (sbeNull {\<C> ''ds''})"

declare createTsynDsBundle.simps[simp del]


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

lemma createAsBundle_dom [simp]: "sbeDom (createAsBundle x) = {\<C> ''as''}"
  apply(simp add: sbeDom_def createAsBundle_def)
  using createAsBundle.abs_eq createAsBundle.rep_eq by auto

lemma createAsBundle_getch [simp]: "(sbe2SB (createAsBundle x)).(\<C> ''as'') = \<up>(Msg (SenderBool x))"
  by (simp add: createAsBundle.rep_eq sbe2sb_getch)

lemma createAsBundle_len [simp]: "ubLen (sbe2SB (createAsBundle x)) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)

lemma createIBundle_dom [simp]: "sbeDom (createIBundle x) = {\<C> ''i''}"
  apply(simp add: sbeDom_def createIBundle_def)
  using createIBundle.abs_eq createIBundle.rep_eq by auto

lemma createIBundle_getch [simp]: "(sbe2SB (createIBundle x)).(\<C> ''i'') = \<up>(Msg (SenderNat x))"
  by (simp add: createIBundle.rep_eq sbe2sb_getch)

lemma createIBundle_len [simp]: "ubLen (sbe2SB (createIBundle x)) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)

lemma createDsBundle_dom [simp]: "sbeDom (createDsBundle x) = {\<C> ''ds''}"
  apply(simp add: sbeDom_def createDsBundle_def)
  using createDsBundle.abs_eq createDsBundle.rep_eq by auto

lemma createDsBundle_getch [simp]: "(sbe2SB (createDsBundle x)).(\<C> ''ds'') = \<up>(Msg (SenderPair_SenderNat_SenderBool x))"
  by (simp add: createDsBundle.rep_eq sbe2sb_getch)

lemma createDsBundle_len [simp]: "ubLen (sbe2SB (createDsBundle x)) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)


section \<open>Lemmas for "createTsynXBundle"\<close>

lemma createTsynAsBundle_dom [simp]: "ubDom\<cdot>(createTsynAsBundle x) = {\<C> ''as''}"
  by (cases x, simp_all add: createTsynAsBundle.simps)

lemma createTsynAsBundle_len [simp]: "ubLen (sbe2DB (createTsynAsBundle x)) = Fin 1"
  apply (cases x, simp_all)
  oops

lemma createTsynIBundle_dom [simp]: "ubDom\<cdot>(createTsynIBundle x) = {\<C> ''i''}"
  by (cases x, simp_all add: createTsynIBundle.simps)

lemma createTsynIBundle_len [simp]: "ubLen (sbe2DB (createTsynIBundle x)) = Fin 1"
  apply (cases x, simp_all)
  oops

lemma createTsynDsBundle_dom [simp]: "ubDom\<cdot>(createTsynDsBundle x) = {\<C> ''ds''}"
  by (cases x, simp_all add: createTsynDsBundle.simps)

lemma createTsynDsBundle_len [simp]: "ubLen (sbe2DB (createTsynDsBundle x)) = Fin 1"
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
  (if((size var_buffer)>1 \<and> port_as=False) then ((SenderState St (prepend (butlast var_buffer) port_i) 3, (sbe2SB (createDsBundle (Pair (last (butlast var_buffer)) True)))))
   else if((size var_buffer)=1 \<and> port_as=False) then ((SenderState St (prepend (butlast var_buffer) port_i) 3, (sbe2SB (createDsBundle (Pair port_i True)))))
   else if((size var_buffer)=0) then ((SenderState Sf (prepend var_buffer port_i) 3, (sbe2SB (createDsBundle (Pair port_i False)))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=True) then ((SenderState Sf (prepend var_buffer port_i) (var_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=True) then ((SenderState Sf (prepend var_buffer port_i) 3, (sbe2SB (createDsBundle (Pair (last var_buffer) False)))))
   else (SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds''))))" |

"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg (SenderBool port_as), \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)>1 \<and> port_as=False) then ((SenderState St (butlast var_buffer) 3, (sbe2SB (createDsBundle (Pair (last (butlast var_buffer)) True)))))
   else if((size var_buffer)=1 \<and> port_as=False) then ((SenderState St (butlast var_buffer) var_c, (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)=0) then ((SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=True) then ((SenderState Sf var_buffer (var_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=True) then ((SenderState Sf var_buffer 3, (sbe2SB (createDsBundle (Pair (last var_buffer) False)))))
   else (SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds''))))" |

"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>Msg (SenderNat port_i))) =
  (if((size var_buffer)=0) then ((SenderState Sf (prepend var_buffer port_i) 3, (sbe2SB (createDsBundle (Pair port_i False)))))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState Sf (prepend var_buffer port_i) (var_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState Sf (prepend var_buffer port_i) 3, (sbe2SB (createDsBundle (Pair (last var_buffer) False)))))
   else (SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds''))))" |

"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)=0) then ((SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState Sf var_buffer 3, (sbe2SB (createDsBundle (Pair (last var_buffer) False)))))
   else (SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds''))))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg (SenderBool port_as), \<^cancel>\<open>i\<mapsto>\<close>Msg (SenderNat port_i))) =
  (if((size var_buffer)=0) then ((SenderState St (prepend var_buffer port_i) 3, (sbe2SB (createDsBundle (Pair port_i True)))))
   else if((size var_buffer)>1 \<and> port_as=True) then ((SenderState Sf (prepend (butlast var_buffer) port_i) 3, (sbe2SB (createDsBundle (Pair (last (butlast var_buffer)) False)))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=False) then ((SenderState St (prepend var_buffer port_i) (var_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=False) then ((SenderState St (prepend var_buffer port_i) 3, (sbe2SB (createDsBundle (Pair (last var_buffer) True)))))
   else if((size var_buffer)=1 \<and> port_as=True) then ((SenderState Sf (prepend (butlast var_buffer) port_i) 3, (sbe2SB (createDsBundle (Pair port_i False)))))
   else (SenderState St var_buffer var_c, (tsynbNull (\<C> ''ds''))))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg (SenderBool port_as), \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)=0) then ((SenderState St var_buffer var_c, (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>1 \<and> port_as=True) then ((SenderState Sf (butlast var_buffer) 3, (sbe2SB (createDsBundle (Pair (last (butlast var_buffer)) False)))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=False) then ((SenderState St var_buffer (var_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=False) then ((SenderState St var_buffer 3, (sbe2SB (createDsBundle (Pair (last var_buffer) True)))))
   else if((size var_buffer)=1 \<and> port_as=True) then ((SenderState Sf (butlast var_buffer) var_c, (tsynbNull (\<C> ''ds''))))
   else (SenderState St var_buffer var_c, (tsynbNull (\<C> ''ds''))))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>Msg (SenderNat port_i))) =
  (if((size var_buffer)=0) then ((SenderState St (prepend var_buffer port_i) 3, (sbe2SB (createDsBundle (Pair port_i True)))))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState St (prepend var_buffer port_i) (var_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState St (prepend var_buffer port_i) 3, (sbe2SB (createDsBundle (Pair (last var_buffer) True)))))
   else (SenderState St var_buffer var_c, (tsynbNull (\<C> ''ds''))))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)=0) then ((SenderState St var_buffer var_c, (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState St var_buffer (var_c-1), (tsynbNull (\<C> ''ds''))))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState St var_buffer 3, (sbe2SB (createDsBundle (Pair (last var_buffer) True)))))
   else (SenderState St var_buffer var_c, (tsynbNull (\<C> ''ds''))))"

(* Transition function *)
fun senderTransition :: "(SenderState \<times> senderMessage tsyn sbElem) \<Rightarrow> (SenderState \<times> senderMessage tsyn SB)" where
"senderTransition (s,b) = (if (sbeDom b) = {\<C> ''as'', \<C> ''i''} then senderTransitionH (s, (Rep_sbElem b\<rightharpoonup>\<C> ''as'', Rep_sbElem b\<rightharpoonup>\<C> ''i'')) else undefined)"

(* The final automaton *)
lift_definition SenderAutomaton :: "(SenderState, senderMessage tsyn) dAutomaton" is
"(senderTransition, SenderState St []  0, tsynbNull (\<C> ''ds''), {\<C> ''as'', \<C> ''i''}, {\<C> ''ds''})"
  by simp

(* Stream processing function for each state (handy for step lemmata) *)
definition SenderStep :: "(SenderState \<Rightarrow> (senderMessage tsyn, senderMessage tsyn) SPF)" where
"SenderStep = da_h SenderAutomaton"

(* The final SPF *)
definition SenderSPF :: "(senderMessage tsyn, senderMessage tsyn) SPF" where
"SenderSPF = da_H SenderAutomaton"


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 33:  Sf -> St [buffer.size()>1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma transition_0_0:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (createSbElem_As_I (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend (butlast var_buffer) port_i) 3, (sbe2SB (createDsBundle (Pair (last (butlast var_buffer)) True))))"
  oops

(* Line 35:  Sf -> St [buffer.size()=1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma transition_0_1:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (createSbElem_As_I (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend (butlast var_buffer) port_i) 3, (sbe2SB (createDsBundle (Pair port_i True))))"
  oops

(* Line 43:  Sf -> Sf [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma transition_0_2:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (createSbElem_As_I (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (sbe2SB (createDsBundle (Pair port_i False))))"
  oops

(* Line 45:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma transition_0_3:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (createSbElem_As_I (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) (var_c-1), (tsynbNull (\<C> ''ds'')))"
  oops

(* Line 47:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma transition_0_4:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (createSbElem_As_I (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (sbe2SB (createDsBundle (Pair (last var_buffer) False))))"
  oops

(* Line 34:  Sf -> St [buffer.size()>1] {as==false, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma transition_1_0:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (createSbElem_As_I (Msg port_as) null))
         = (SenderState St (butlast var_buffer) 3, (sbe2SB (createDsBundle (Pair (last (butlast var_buffer)) True))))"
  oops

(* Line 36:  Sf -> St [buffer.size()=1] {as==false, i==null} / {buffer=buffer.butlast()}; *)
lemma transition_1_1:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (createSbElem_As_I (Msg port_as) null))
         = (SenderState St (butlast var_buffer) var_c, (tsynbNull (\<C> ''ds'')))"
  oops

(* Line 38:  Sf -> Sf [buffer.size()=0 && as!=null] {i==null}; *)
lemma transition_1_2:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (createSbElem_As_I (Msg port_as) null))
         = (SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds'')))"
  oops

(* Line 40:  Sf -> Sf [buffer.size()>0 && c>0] {as==true, i==null} / {c=c-1}; *)
lemma transition_1_3:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (createSbElem_As_I (Msg port_as) null))
         = (SenderState Sf var_buffer (var_c-1), (tsynbNull (\<C> ''ds'')))"
  oops

(* Line 41:  Sf -> Sf [buffer.size()>0 && c=0] {as==true, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma transition_1_4:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (createSbElem_As_I (Msg port_as) null))
         = (SenderState Sf var_buffer 3, (sbe2SB (createDsBundle (Pair (last var_buffer) False))))"
  oops

(* Line 44:  Sf -> Sf [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma transition_2_0:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (createSbElem_As_I null (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (sbe2SB (createDsBundle (Pair port_i False))))"
  oops

(* Line 46:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma transition_2_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (createSbElem_As_I null (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) (var_c-1), (tsynbNull (\<C> ''ds'')))"
  oops

(* Line 48:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma transition_2_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (createSbElem_As_I null (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (sbe2SB (createDsBundle (Pair (last var_buffer) False))))"
  oops

(* Line 37:  Sf -> Sf [buffer.size()=0] {as==null, i==null}; *)
lemma transition_3_0:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (createSbElem_As_I null null))
         = (SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds'')))"
  oops

(* Line 39:  Sf -> Sf [buffer.size()>0 && c>0] {as==null, i==null}; *)
lemma transition_3_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (createSbElem_As_I null null))
         = (SenderState Sf var_buffer var_c, (tsynbNull (\<C> ''ds'')))"
  oops

(* Line 42:  Sf -> Sf [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma transition_3_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (createSbElem_As_I null null))
         = (SenderState Sf var_buffer 3, (sbe2SB (createDsBundle (Pair (last var_buffer) False))))"
  oops

(* Line 25:  St -> St [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma transition_4_0:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (createSbElem_As_I (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (sbe2SB (createDsBundle (Pair port_i True))))"
  oops

(* Line 27:  St -> Sf [buffer.size()>1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma transition_4_1:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (createSbElem_As_I (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend (butlast var_buffer) port_i) 3, (sbe2SB (createDsBundle (Pair (last (butlast var_buffer)) False))))"
  oops

(* Line 28:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma transition_4_2:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (createSbElem_As_I (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) (var_c-1), (tsynbNull (\<C> ''ds'')))"
  oops

(* Line 30:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma transition_4_3:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (createSbElem_As_I (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (sbe2SB (createDsBundle (Pair (last var_buffer) True))))"
  oops

(* Line 32:  St -> Sf [buffer.size()=1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma transition_4_4:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (createSbElem_As_I (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend (butlast var_buffer) port_i) 3, (sbe2SB (createDsBundle (Pair port_i False))))"
  oops

(* Line 17:  St -> St [buffer.size()=0 && as!=null] {i==null}; *)
lemma transition_5_0:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (createSbElem_As_I (Msg port_as) null))
         = (SenderState St var_buffer var_c, (tsynbNull (\<C> ''ds'')))"
  oops

(* Line 18:  St -> Sf [buffer.size()>1] {as==true, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma transition_5_1:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (createSbElem_As_I (Msg port_as) null))
         = (SenderState Sf (butlast var_buffer) 3, (sbe2SB (createDsBundle (Pair (last (butlast var_buffer)) False))))"
  oops

(* Line 20:  St -> St [buffer.size()>0 && c>0] {as==false, i==null} / {c=c-1}; *)
lemma transition_5_2:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (createSbElem_As_I (Msg port_as) null))
         = (SenderState St var_buffer (var_c-1), (tsynbNull (\<C> ''ds'')))"
  oops

(* Line 22:  St -> St [buffer.size()>0 && c=0] {as==false, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma transition_5_3:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (createSbElem_As_I (Msg port_as) null))
         = (SenderState St var_buffer 3, (sbe2SB (createDsBundle (Pair (last var_buffer) True))))"
  oops

(* Line 24:  St -> Sf [buffer.size()=1] {as==true, i==null} / {buffer=buffer.butlast()}; *)
lemma transition_5_4:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (createSbElem_As_I (Msg port_as) null))
         = (SenderState Sf (butlast var_buffer) var_c, (tsynbNull (\<C> ''ds'')))"
  oops

(* Line 26:  St -> St [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma transition_6_0:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (createSbElem_As_I null (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (sbe2SB (createDsBundle (Pair port_i True))))"
  oops

(* Line 29:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma transition_6_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState St var_buffer var_c), (createSbElem_As_I null (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) (var_c-1), (tsynbNull (\<C> ''ds'')))"
  oops

(* Line 31:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma transition_6_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (createSbElem_As_I null (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (sbe2SB (createDsBundle (Pair (last var_buffer) True))))"
  oops

(* Line 19:  St -> St [buffer.size()=0] {as==null, i==null}; *)
lemma transition_7_0:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (createSbElem_As_I null null))
         = (SenderState St var_buffer var_c, (tsynbNull (\<C> ''ds'')))"
  oops

(* Line 21:  St -> St [buffer.size()>0 && c>0] {as==null, i==null} / {c=c-1}; *)
lemma transition_7_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState St var_buffer var_c), (createSbElem_As_I null null))
         = (SenderState St var_buffer (var_c-1), (tsynbNull (\<C> ''ds'')))"
  oops

(* Line 23:  St -> St [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma transition_7_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (createSbElem_As_I null null))
         = (SenderState St var_buffer 3, (sbe2SB (createDsBundle (Pair (last var_buffer) True))))"
  oops


section \<open>Step-wise lemmata for the SPF\<close>

(* Line 33:  Sf -> St [buffer.size()>1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma step_0_0:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) (Msg port_i))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair (last (butlast var_buffer)) True)))\<cdot>(da_h SenderAutomaton (SenderState St (prepend (butlast var_buffer) port_i) 3))"
  oops

(* Line 35:  Sf -> St [buffer.size()=1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma step_0_1:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) (Msg port_i))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair port_i True)))\<cdot>(da_h SenderAutomaton (SenderState St (prepend (butlast var_buffer) port_i) 3))"
  oops

(* Line 43:  Sf -> Sf [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma step_0_2:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) (Msg port_i))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair port_i False)))\<cdot>(da_h SenderAutomaton (SenderState Sf (prepend var_buffer port_i) 3))"
  oops

(* Line 45:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma step_0_3:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) (Msg port_i))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf (prepend var_buffer port_i) (var_c-1)))"
  oops

(* Line 47:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma step_0_4:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) (Msg port_i))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair (last var_buffer) False)))\<cdot>(da_h SenderAutomaton (SenderState Sf (prepend var_buffer port_i) 3))"
  oops

(* Line 34:  Sf -> St [buffer.size()>1] {as==false, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma step_1_0:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) null)\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair (last (butlast var_buffer)) True)))\<cdot>(da_h SenderAutomaton (SenderState St (butlast var_buffer) 3))"
  oops

(* Line 36:  Sf -> St [buffer.size()=1] {as==false, i==null} / {buffer=buffer.butlast()}; *)
lemma step_1_1:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) null)\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St (butlast var_buffer) var_c))"
  oops

(* Line 38:  Sf -> Sf [buffer.size()=0 && as!=null] {i==null}; *)
lemma step_1_2:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) null)\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))"
  oops

(* Line 40:  Sf -> Sf [buffer.size()>0 && c>0] {as==true, i==null} / {c=c-1}; *)
lemma step_1_3:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) null)\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer (var_c-1)))"
  oops

(* Line 41:  Sf -> Sf [buffer.size()>0 && c=0] {as==true, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma step_1_4:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) null)\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair (last var_buffer) False)))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer 3))"
  oops

(* Line 44:  Sf -> Sf [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma step_2_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (createBundle_As_I null (Msg port_i))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair port_i False)))\<cdot>(da_h SenderAutomaton (SenderState Sf (prepend var_buffer port_i) 3))"
  oops

(* Line 46:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma step_2_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (createBundle_As_I null (Msg port_i))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf (prepend var_buffer port_i) (var_c-1)))"
  oops

(* Line 48:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma step_2_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (createBundle_As_I null (Msg port_i))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair (last var_buffer) False)))\<cdot>(da_h SenderAutomaton (SenderState Sf (prepend var_buffer port_i) 3))"
  oops

(* Line 37:  Sf -> Sf [buffer.size()=0] {as==null, i==null}; *)
lemma step_3_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (createBundle_As_I null null)\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))"
  oops

(* Line 39:  Sf -> Sf [buffer.size()>0 && c>0] {as==null, i==null}; *)
lemma step_3_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (createBundle_As_I null null)\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))"
  oops

(* Line 42:  Sf -> Sf [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma step_3_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (createBundle_As_I null null)\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair (last var_buffer) False)))\<cdot>(da_h SenderAutomaton (SenderState Sf var_buffer 3))"
  oops

(* Line 25:  St -> St [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma step_4_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) (Msg port_i))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair port_i True)))\<cdot>(da_h SenderAutomaton (SenderState St (prepend var_buffer port_i) 3))"
  oops

(* Line 27:  St -> Sf [buffer.size()>1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma step_4_1:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) (Msg port_i))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair (last (butlast var_buffer)) False)))\<cdot>(da_h SenderAutomaton (SenderState Sf (prepend (butlast var_buffer) port_i) 3))"
  oops

(* Line 28:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma step_4_2:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) (Msg port_i))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St (prepend var_buffer port_i) (var_c-1)))"
  oops

(* Line 30:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma step_4_3:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) (Msg port_i))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair (last var_buffer) True)))\<cdot>(da_h SenderAutomaton (SenderState St (prepend var_buffer port_i) 3))"
  oops

(* Line 32:  St -> Sf [buffer.size()=1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma step_4_4:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) (Msg port_i))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair port_i False)))\<cdot>(da_h SenderAutomaton (SenderState Sf (prepend (butlast var_buffer) port_i) 3))"
  oops

(* Line 17:  St -> St [buffer.size()=0 && as!=null] {i==null}; *)
lemma step_5_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) null)\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))"
  oops

(* Line 18:  St -> Sf [buffer.size()>1] {as==true, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma step_5_1:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) null)\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair (last (butlast var_buffer)) False)))\<cdot>(da_h SenderAutomaton (SenderState Sf (butlast var_buffer) 3))"
  oops

(* Line 20:  St -> St [buffer.size()>0 && c>0] {as==false, i==null} / {c=c-1}; *)
lemma step_5_2:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) null)\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer (var_c-1)))"
  oops

(* Line 22:  St -> St [buffer.size()>0 && c=0] {as==false, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma step_5_3:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) null)\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair (last var_buffer) True)))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer 3))"
  oops

(* Line 24:  St -> Sf [buffer.size()=1] {as==true, i==null} / {buffer=buffer.butlast()}; *)
lemma step_5_4:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "spfConcIn  (createBundle_As_I (Msg port_as) null)\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState Sf (butlast var_buffer) var_c))"
  oops

(* Line 26:  St -> St [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma step_6_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (createBundle_As_I null (Msg port_i))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair port_i True)))\<cdot>(da_h SenderAutomaton (SenderState St (prepend var_buffer port_i) 3))"
  oops

(* Line 29:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma step_6_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (createBundle_As_I null (Msg port_i))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St (prepend var_buffer port_i) (var_c-1)))"
  oops

(* Line 31:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma step_6_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (createBundle_As_I null (Msg port_i))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair (last var_buffer) True)))\<cdot>(da_h SenderAutomaton (SenderState St (prepend var_buffer port_i) 3))"
  oops

(* Line 19:  St -> St [buffer.size()=0] {as==null, i==null}; *)
lemma step_7_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (createBundle_As_I null null)\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))"
  oops

(* Line 21:  St -> St [buffer.size()>0 && c>0] {as==null, i==null} / {c=c-1}; *)
lemma step_7_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (createBundle_As_I null null)\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (tsynbNull (\<C> ''ds''))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer (var_c-1)))"
  oops

(* Line 23:  St -> St [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma step_7_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (createBundle_As_I null null)\<cdot>(da_h SenderAutomaton (SenderState St var_buffer var_c))
         = spfConcOut (sbe2SB (createDsBundle (Pair (last var_buffer) True)))\<cdot>(da_h SenderAutomaton (SenderState St var_buffer 3))"
  oops


end