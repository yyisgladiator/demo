(*<*)
theory sbElem
  imports inc.Channel
begin
(*>*)

default_sort chan
(* Move to prelude and add mono2mono rules
section \<open> mono2mono\<close>
named_theorems mono2mono "monofun intro rule"
*)
section \<open>sbElem\<close>

subsection \<open>sbElem Definition \<close>
fun sbElem_well :: "('c::chan \<Rightarrow> M) option \<Rightarrow> bool" where
"sbElem_well None = ((Rep ` (UNIV::'c set)) \<subseteq> cEmpty)" |  (* Schöner? *)
"sbElem_well (Some sbe) = (\<forall> c. sbe c \<in> ctype ((Rep::'c\<Rightarrow>channel) c))" (* cbot ist leer, daher wird das nie wahr sein für das leere Bündel *)

text\<open>Type sbElem is can be interpreted as a Timeslice\<close>
typedef 'c::chan sbElem  ("(_\<^sup>\<surd>)" [1000] 999) = "{f:: ('c::chan \<Rightarrow> M) option. sbElem_well f}"
proof(cases "((range (Rep::'c \<Rightarrow> channel) \<subseteq> cEmpty))")
  case True
  then show ?thesis
    apply(rule_tac x=None in exI)
    by simp
next
  case False
  then have "\<forall>c\<in>(range (Rep::'c\<Rightarrow>channel)). ctype c \<noteq> {}"
    using cEmpty_def chan_botsingle by blast
  then have "sbElem_well (Some(\<lambda>(c::'c). (SOME m. m \<in> ctype (Rep c))))"
    apply(simp add: sbElem_well.cases,auto)
    by (simp add: some_in_eq)
  then show ?thesis
    by blast
qed

text\<open>Instantiation of sbElem as a discrete cpo\<close>
instantiation  sbElem::(chan)discrete_cpo
begin
definition "below_sbElem = (\<lambda>(sbe1::'a sbElem) sbe2. (sbe1 = sbe2))"
instance
  by(standard, simp add: below_sbElem_def)
end

lemma sbe_eqI:"Rep_sbElem sbe1 = Rep_sbElem sbe2 \<Longrightarrow> sbe1 = sbe2"
  by (simp add: Rep_sbElem_inject)

subsection\<open>chIsEmpty lemmas\<close>
lemma sbtypeempty_sbewell:"chIsEmpty TYPE ('cs) \<Longrightarrow> sbElem_well (None::('cs \<Rightarrow> M) option)"
  by(simp add: chIsEmpty_def)

lemma sbtypeempty_notsbewell:"chIsEmpty TYPE ('cs) \<Longrightarrow> \<not>sbElem_well (Some (f::'cs \<Rightarrow> M))"
  apply(simp add: chIsEmpty_def)
  by (simp add: cEmpty_def image_subset_iff)

lemma sbtypeepmpty_sbenone[simp]:"chIsEmpty TYPE ('cs) \<Longrightarrow> (sbe::'cs\<^sup>\<surd>) = Abs_sbElem(None)"
  apply(simp add: chIsEmpty_def)
  apply(rule sbe_eqI)
  apply(simp add: sbtypeempty_sbewell Abs_sbElem_inverse)
  by (metis not_Some_eq Rep_sbElem mem_Collect_eq chIsEmpty_def sbtypeempty_notsbewell)

setup_lifting type_definition_sbElem

subsection \<open>sbElem functions\<close>

text\<open>This function retrieves an element on channel e from the sbElem. This only works
      if Elements are allowed on channel e and channel e is also in type c\<close>
definition sbegetch::"'e \<Rightarrow> 'c\<^sup>\<surd> \<Rightarrow> M"where (*works if sbe \<noteq> None* and 'e \<subseteq> 'c *)
"sbegetch c = (\<lambda> sbe. ((the (Rep_sbElem sbe)) (Abs (Rep c))))"


text\<open>This function Converts the Domain of an sbElem. This works if the Domain it converts to, is
      smaller or equal\<close>
definition sbeConvert::"'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd>"where
"sbeConvert = (\<lambda>sbe. Abs_sbElem(Some (\<lambda>c. sbegetch c sbe)))"

lemma sberestrict_getch: assumes"Rep (c::'c) \<in> range(Rep::'d \<Rightarrow> channel)"
  shows "sbegetch c ((sbeConvert::'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd>) sbe) = sbegetch c sbe"
  oops

text\<open>This unites two sbElems. It works, if type e is a subset of the union of type c and d. First
     sbElem has priority\<close>
definition sbeUnion::"'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd> \<Rightarrow> 'e\<^sup>\<surd>"where
"sbeUnion = (\<lambda>sbe1 sbe2. Abs_sbElem (Some(\<lambda> c. if (Rep c \<in> (range (Rep ::'c \<Rightarrow> channel))) then
                  sbegetch c sbe1 else  sbegetch c sbe2)))"

lemma sbeunion_getchfst:assumes "Rep (c::'c) \<in> range(Rep::'e \<Rightarrow> channel)"
  shows "sbegetch c ((sbeUnion::'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd> \<Rightarrow> 'e\<^sup>\<surd>) sbe1 sbe2) = sbegetch c sbe1"
  oops

lemma sbeunion_getchsnd:assumes "Rep (c::'d) \<in> range(Rep::'e \<Rightarrow> channel)"
                     and "Rep c \<notin> range(Rep::'c \<Rightarrow> channel)"
  shows"sbegetch c ((sbeUnion::'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd> \<Rightarrow> 'e\<^sup>\<surd>) sbe1 sbe2) = sbegetch c sbe2"
  oops

(*<*)
end
(*>*)
