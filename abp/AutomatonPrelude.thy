(*
 * DO NOT MODIFY!
 * This file was generated and will be overridden when the models change.
 *
 * Generated on Aug 15, 2018 4:59:44 PM by isartransformer 1.0.0
 *)
theory AutomatonPrelude

imports automat.dAutomaton automat.ndAutomaton bundle.tsynBundle

begin

fun prepend:: "'a::type list \<Rightarrow> 'a::type \<Rightarrow> 'a::type list" where
"prepend xs x= x#xs"

datatype abpMessage = ABPPair_nat_bool "(nat\<times>bool)" | ABPBool "bool" | ABPNat "nat"

instance abpMessage :: countable
  apply(intro_classes)
  by(countable_datatype)

instantiation abpMessage :: message
begin
  fun ctype_abpMessage :: "channel  \<Rightarrow> abpMessage set" where
  "ctype_abpMessage c = (
    if c = \<C> ''as'' then range ABPBool else              (* MediumRS.as -> Sender.as *)
    if c = \<C> ''dr'' then range ABPPair_nat_bool else     (* MediumSR.dr -> Receiver.dr *)
    if c = \<C> ''ds'' then range ABPPair_nat_bool else     (* Sender.ds -> MediumSR.ds *)
    if c = \<C> ''ar'' then range ABPBool else              (* Receiver.ar -> MediumRS.ar *)
    if c = \<C> ''o'' then range ABPNat else                (* Receiver.o *)
    if c = \<C> ''i'' then range ABPNat else                (* Sender.i *)
    {})"

  instance
    by(intro_classes)
end


section \<open>Helpers to create a bundle from a single raw element\<close>

lift_definition createAsBundle :: "bool \<Rightarrow> abpMessage tsyn SB" is
"\<lambda>x. [ \<C> ''as'' \<mapsto> \<up>(Msg (ABPBool x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createDrBundle :: "(nat\<times>bool) \<Rightarrow> abpMessage tsyn SB" is
"\<lambda>x. [ \<C> ''dr'' \<mapsto> \<up>(Msg (ABPPair_nat_bool x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createDsBundle :: "(nat\<times>bool) \<Rightarrow> abpMessage tsyn SB" is
"\<lambda>x. [ \<C> ''ds'' \<mapsto> \<up>(Msg (ABPPair_nat_bool x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createArBundle :: "bool \<Rightarrow> abpMessage tsyn SB" is
"\<lambda>x. [ \<C> ''ar'' \<mapsto> \<up>(Msg (ABPBool x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createOBundle :: "nat \<Rightarrow> abpMessage tsyn SB" is
"\<lambda>x. [ \<C> ''o'' \<mapsto> \<up>(Msg (ABPNat x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition createIBundle :: "nat \<Rightarrow> abpMessage tsyn SB" is
"\<lambda>x. [ \<C> ''i'' \<mapsto> \<up>(Msg (ABPNat x))]"
  unfolding ubWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp


section \<open>Helpers to create a bundle from a single tsyn element\<close>

fun createTsynAsBundle :: "bool tsyn \<Rightarrow> abpMessage tsyn SB" where
"createTsynAsBundle (Msg x) = (createAsBundle x)" |
"createTsynAsBundle null = (tsynbNull (\<C> ''as''))"

fun createTsynDrBundle :: "(nat\<times>bool) tsyn \<Rightarrow> abpMessage tsyn SB" where
"createTsynDrBundle (Msg x) = (createDrBundle x)" |
"createTsynDrBundle null = (tsynbNull (\<C> ''dr''))"

fun createTsynDsBundle :: "(nat\<times>bool) tsyn \<Rightarrow> abpMessage tsyn SB" where
"createTsynDsBundle (Msg x) = (createDsBundle x)" |
"createTsynDsBundle null = (tsynbNull (\<C> ''ds''))"

fun createTsynArBundle :: "bool tsyn \<Rightarrow> abpMessage tsyn SB" where
"createTsynArBundle (Msg x) = (createArBundle x)" |
"createTsynArBundle null = (tsynbNull (\<C> ''ar''))"

fun createTsynOBundle :: "nat tsyn \<Rightarrow> abpMessage tsyn SB" where
"createTsynOBundle (Msg x) = (createOBundle x)" |
"createTsynOBundle null = (tsynbNull (\<C> ''o''))"

fun createTsynIBundle :: "nat tsyn \<Rightarrow> abpMessage tsyn SB" where
"createTsynIBundle (Msg x) = (createIBundle x)" |
"createTsynIBundle null = (tsynbNull (\<C> ''i''))"


section \<open>Helpers to create a bundle from a tsyn list of elements\<close>

fun createLongAsBundle :: "(bool tsyn) list \<Rightarrow> abpMessage tsyn SB" where
"createLongAsBundle (x#xs) = ubConcEq (createTsynAsBundle x)\<cdot>(createLongAsBundle xs)" |
"createLongAsBundle []     = ubLeast {\<C> ''as''}"

fun createLongDrBundle :: "((nat\<times>bool) tsyn) list \<Rightarrow> abpMessage tsyn SB" where
"createLongDrBundle (x#xs) = ubConcEq (createTsynDrBundle x)\<cdot>(createLongDrBundle xs)" |
"createLongDrBundle []     = ubLeast {\<C> ''dr''}"

fun createLongDsBundle :: "((nat\<times>bool) tsyn) list \<Rightarrow> abpMessage tsyn SB" where
"createLongDsBundle (x#xs) = ubConcEq (createTsynDsBundle x)\<cdot>(createLongDsBundle xs)" |
"createLongDsBundle []     = ubLeast {\<C> ''ds''}"

fun createLongArBundle :: "(bool tsyn) list \<Rightarrow> abpMessage tsyn SB" where
"createLongArBundle (x#xs) = ubConcEq (createTsynArBundle x)\<cdot>(createLongArBundle xs)" |
"createLongArBundle []     = ubLeast {\<C> ''ar''}"

fun createLongOBundle :: "(nat tsyn) list \<Rightarrow> abpMessage tsyn SB" where
"createLongOBundle (x#xs) = ubConcEq (createTsynOBundle x)\<cdot>(createLongOBundle xs)" |
"createLongOBundle []     = ubLeast {\<C> ''o''}"

fun createLongIBundle :: "(nat tsyn) list \<Rightarrow> abpMessage tsyn SB" where
"createLongIBundle (x#xs) = ubConcEq (createTsynIBundle x)\<cdot>(createLongIBundle xs)" |
"createLongIBundle []     = ubLeast {\<C> ''i''}"


section \<open>Lemmas for "createXBundle"\<close>

lemma createAsBundle_dom [simp]: "ubDom\<cdot>(createAsBundle x) = {\<C> ''as''}"
  by (simp add: createAsBundle.rep_eq ubdom_insert)

lemma createAsBundle_getch [simp]: "(createAsBundle x).(\<C> ''as'') = \<up>(Msg (ABPBool x))"
  by (simp add: createAsBundle.rep_eq ubgetch_insert)

lemma createAsBundle_len [simp]: "ubLen (createAsBundle x) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)

lemma createDrBundle_dom [simp]: "ubDom\<cdot>(createDrBundle x) = {\<C> ''dr''}"
  by (simp add: createDrBundle.rep_eq ubdom_insert)

lemma createDrBundle_getch [simp]: "(createDrBundle x).(\<C> ''dr'') = \<up>(Msg (ABPPair_nat_bool x))"
  by (simp add: createDrBundle.rep_eq ubgetch_insert)

lemma createDrBundle_len [simp]: "ubLen (createDrBundle x) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)

lemma createDsBundle_dom [simp]: "ubDom\<cdot>(createDsBundle x) = {\<C> ''ds''}"
  by (simp add: createDsBundle.rep_eq ubdom_insert)

lemma createDsBundle_getch [simp]: "(createDsBundle x).(\<C> ''ds'') = \<up>(Msg (ABPPair_nat_bool x))"
  by (simp add: createDsBundle.rep_eq ubgetch_insert)

lemma createDsBundle_len [simp]: "ubLen (createDsBundle x) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)

lemma createArBundle_dom [simp]: "ubDom\<cdot>(createArBundle x) = {\<C> ''ar''}"
  by (simp add: createArBundle.rep_eq ubdom_insert)

lemma createArBundle_getch [simp]: "(createArBundle x).(\<C> ''ar'') = \<up>(Msg (ABPBool x))"
  by (simp add: createArBundle.rep_eq ubgetch_insert)

lemma createArBundle_len [simp]: "ubLen (createArBundle x) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)

lemma createOBundle_dom [simp]: "ubDom\<cdot>(createOBundle x) = {\<C> ''o''}"
  by (simp add: createOBundle.rep_eq ubdom_insert)

lemma createOBundle_getch [simp]: "(createOBundle x).(\<C> ''o'') = \<up>(Msg (ABPNat x))"
  by (simp add: createOBundle.rep_eq ubgetch_insert)

lemma createOBundle_len [simp]: "ubLen (createOBundle x) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)

lemma createIBundle_dom [simp]: "ubDom\<cdot>(createIBundle x) = {\<C> ''i''}"
  by (simp add: createIBundle.rep_eq ubdom_insert)

lemma createIBundle_getch [simp]: "(createIBundle x).(\<C> ''i'') = \<up>(Msg (ABPNat x))"
  by (simp add: createIBundle.rep_eq ubgetch_insert)

lemma createIBundle_len [simp]: "ubLen (createIBundle x) = Fin 1"
  apply (subst ubLen_def)
  apply (simp add: usclLen_stream_def)
  by (metis (full_types) LeastI)


section \<open>Lemmas for "createTsynXBundle"\<close>

lemma createTsynAsBundle_dom [simp]: "ubDom\<cdot>(createTsynAsBundle x) = {\<C> ''as''}"
  by (cases x, simp_all)

lemma createTsynAsBundle_len [simp]: "ubLen (createTsynAsBundle x) = Fin 1"
  apply (cases x, simp_all)
  oops

lemma createTsynDrBundle_dom [simp]: "ubDom\<cdot>(createTsynDrBundle x) = {\<C> ''dr''}"
  by (cases x, simp_all)

lemma createTsynDrBundle_len [simp]: "ubLen (createTsynDrBundle x) = Fin 1"
  apply (cases x, simp_all)
  oops

lemma createTsynDsBundle_dom [simp]: "ubDom\<cdot>(createTsynDsBundle x) = {\<C> ''ds''}"
  by (cases x, simp_all)

lemma createTsynDsBundle_len [simp]: "ubLen (createTsynDsBundle x) = Fin 1"
  apply (cases x, simp_all)
  oops

lemma createTsynArBundle_dom [simp]: "ubDom\<cdot>(createTsynArBundle x) = {\<C> ''ar''}"
  by (cases x, simp_all)

lemma createTsynArBundle_len [simp]: "ubLen (createTsynArBundle x) = Fin 1"
  apply (cases x, simp_all)
  oops

lemma createTsynOBundle_dom [simp]: "ubDom\<cdot>(createTsynOBundle x) = {\<C> ''o''}"
  by (cases x, simp_all)

lemma createTsynOBundle_len [simp]: "ubLen (createTsynOBundle x) = Fin 1"
  apply (cases x, simp_all)
  oops

lemma createTsynIBundle_dom [simp]: "ubDom\<cdot>(createTsynIBundle x) = {\<C> ''i''}"
  by (cases x, simp_all)

lemma createTsynIBundle_len [simp]: "ubLen (createTsynIBundle x) = Fin 1"
  apply (cases x, simp_all)
  oops


section \<open>Lemmas for "createLongXBundle"\<close>

lemma createLongAsBundle_dom [simp]: "ubDom\<cdot>(createLongAsBundle xs) = {\<C> ''as''}"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a _)
    then show ?case
      proof (cases a)
        case (Msg _)
        then show ?thesis by (simp add: Cons.IH)
      next
        case null
        then show ?thesis by (simp add: Cons.IH)
      qed
  qed

lemma createLongAsBundle_len [simp]: "ubLen (createLongAsBundle xs) = Fin (length xs)"
  oops

lemma createLongDrBundle_dom [simp]: "ubDom\<cdot>(createLongDrBundle xs) = {\<C> ''dr''}"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a _)
    then show ?case
      proof (cases a)
        case (Msg _)
        then show ?thesis by (simp add: Cons.IH)
      next
        case null
        then show ?thesis by (simp add: Cons.IH)
      qed
  qed

lemma createLongDrBundle_len [simp]: "ubLen (createLongDrBundle xs) = Fin (length xs)"
  oops

lemma createLongDsBundle_dom [simp]: "ubDom\<cdot>(createLongDsBundle xs) = {\<C> ''ds''}"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a _)
    then show ?case
      proof (cases a)
        case (Msg _)
        then show ?thesis by (simp add: Cons.IH)
      next
        case null
        then show ?thesis by (simp add: Cons.IH)
      qed
  qed

lemma createLongDsBundle_len [simp]: "ubLen (createLongDsBundle xs) = Fin (length xs)"
  oops

lemma createLongArBundle_dom [simp]: "ubDom\<cdot>(createLongArBundle xs) = {\<C> ''ar''}"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a _)
    then show ?case
      proof (cases a)
        case (Msg _)
        then show ?thesis by (simp add: Cons.IH)
      next
        case null
        then show ?thesis by (simp add: Cons.IH)
      qed
  qed

lemma createLongArBundle_len [simp]: "ubLen (createLongArBundle xs) = Fin (length xs)"
  oops

lemma createLongOBundle_dom [simp]: "ubDom\<cdot>(createLongOBundle xs) = {\<C> ''o''}"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a _)
    then show ?case
      proof (cases a)
        case (Msg _)
        then show ?thesis by (simp add: Cons.IH)
      next
        case null
        then show ?thesis by (simp add: Cons.IH)
      qed
  qed

lemma createLongOBundle_len [simp]: "ubLen (createLongOBundle xs) = Fin (length xs)"
  oops

lemma createLongIBundle_dom [simp]: "ubDom\<cdot>(createLongIBundle xs) = {\<C> ''i''}"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a _)
    then show ?case
      proof (cases a)
        case (Msg _)
        then show ?thesis by (simp add: Cons.IH)
      next
        case null
        then show ?thesis by (simp add: Cons.IH)
      qed
  qed

lemma createLongIBundle_len [simp]: "ubLen (createLongIBundle xs) = Fin (length xs)"
  oops


end