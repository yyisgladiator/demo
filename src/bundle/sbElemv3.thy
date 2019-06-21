theory sbElemv3

imports stream.Streams inc.Channelv3
begin

default_sort chan

section \<open>sbElem\<close>

subsection \<open>sbElem Definition \<close>
fun sbElem_well :: "('c::chan \<Rightarrow> M) option \<Rightarrow> bool" where
"sbElem_well None = ((Rep ` (UNIV::'c set)) \<subseteq> cEmpty)" |  (* Schöner? *)
"sbElem_well (Some sbe) = (\<forall> c. sbe c \<in> ctype (Rep c))" (* cbot ist leer, daher wird das nie wahr sein für das leere Bündel *)

text{*Type sbElem is can be interpreted as a Timeslice*}
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

text{*Instantiation of sbElem as a discrete cpo*}
instantiation  sbElem::(chan)discrete_cpo
begin
definition "below_sbElem = (\<lambda>(sbe1::'a sbElem) sbe2. (sbe1 = sbe2))"
instance
  by(standard, simp add: below_sbElem_def)
end

setup_lifting type_definition_sbElem

subsection \<open>sbElem functions\<close>

text{*This function retrieves an element on channel e from the sbElem. This only works 
      if Elements are allowed on channel e and channel e is also in type c*}
definition sbegetch::"'e \<Rightarrow> 'c\<^sup>\<surd> \<Rightarrow> M"where (*works if sbe \<noteq> None* and 'e \<subseteq> 'c *)
"sbegetch c = (\<lambda> sbe. ((the (Rep_sbElem sbe)) (Abs (Rep c))))"


text{*This function Restricts the Domain of an sbElem. This works if the Domain to restrict to is 
      smaller*}
definition sbeRestrict::"'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd>"where 
"sbeRestrict = (\<lambda>sbe. Abs_sbElem(Some (\<lambda>c. sbegetch c sbe)))"


text{*This unites two sbElems. It works, if type e is a subset of the union of type c and d*}
definition sbeUnion::"'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd> \<Rightarrow> 'e\<^sup>\<surd>"where 
"sbeUnion = (\<lambda>sbe1 sbe2. Abs_sbElem (Some(\<lambda> c. if (Rep c \<in> (range (Rep ::'c \<Rightarrow> channel))) then 
                  sbegetch c sbe1 else  sbegetch c sbe2)))"

end