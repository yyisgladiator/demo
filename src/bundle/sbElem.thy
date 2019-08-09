(*<*)(*:maxLineLen=68:*)
theory sbElem
  imports Channel
begin
(*>*)

declare %invisible[[show_types]]
declare %invisible[[show_consts]]

default_sort %invisible chan
(* Move to prelude and add mono2mono rules
section \<open> mono2mono\<close>
named_theorems mono2mono "monofun intro rule"
*)
section \<open>sbElem \label{sec:sbelem}\<close>
text\<open>Before we define the \gls{sb} datatype, we define the sbElem 
type. It is a function from a @{class chan} type to a message 
@{type M} in @{const ctype} and quite useful in our later theories.
But how can we define a non partial function, if the Domain of our 
type is empty? Then the function cannot map to any message in 
@{const ctype}. To still retain the totality property in all 
possible cases, one can define sbElem to be some total function, if 
the domain is not emtpy, but else it is nothing.\<close>

subsection \<open>sbElem Definition \label{sub:sbedef}\<close>
fun sbElem_well :: "('c \<Rightarrow> M) option \<Rightarrow> bool" where
"sbElem_well None = chDomEmpty TYPE('c)" |
"sbElem_well (Some sbe) = (\<forall>c. sbe c \<in> ctype((Rep::'c\<Rightarrow>channel) c))" 
(*cbot ist leer, daher wird das nie wahr sein für das leere Bündel*)
text\<open>Predicate @{const sbElem_well} exactly describes our 
requirements. The @{type option} type in our predicate allows us to 
have nothing (@{const None}), iff the domain of our 
channel type is empty. For all non-empty domains, a total function 
is a sbElem, iff it only maps to messages in the @{const ctype} of 
the channel. With those preparations we now define the sbElem type:\<close>

typedef 'c sbElem ("(_\<^sup>\<surd>)"[1000] 999) = 
        "{f::('c \<Rightarrow> M) option. sbElem_well f}"
proof(cases "chDomEmpty(TYPE('c))")
  case True
  then show ?thesis
    apply(rule_tac x=None in exI)
    by (simp add: chDom_def)
next
  case False
  then have "\<forall>c\<in>(range (Rep::'c\<Rightarrow>channel)). ctype c \<noteq> {}"
    using cEmpty_def chDom_def chan_botsingle by blast
  then have "sbElem_well 
             (Some(\<lambda>(c::'c). (SOME m. m \<in> ctype (Rep c))))"
    apply(simp add: sbElem_well.cases,auto)
    by (simp add: some_in_eq)
  then show ?thesis
    by blast
qed
text\<open>From our different time types, we will derive the abstract 
interpretation of a @{type sbElem} with no empty domain for the 
timed cases:
  \<^item> Time synchronous: exactly one message from @{type M}
  \<^item> Timed: exactly on list of message from @{type M_pure}


Hence, the a @{type sbElem} is a time slice. It contains maximal one
message for the synchronous case and arbitrarily, but not 
infinitely many messages in the asynchronous case.\<close>

text\<open>The order of @{type sbElem}s then has to be a discrete one. 
Else it order would be inconsistent to our prefix order on streams 
and also the resulting \gls{sb} order.\<close>
instantiation  sbElem::(chan)discrete_cpo
begin
definition "below_sbElem = (\<lambda>(sbe1::'a sbElem) sbe2. (sbe1 = sbe2))"
instance
  by(standard, simp add: below_sbElem_def)
end

lemma sbe_eqI:"Rep_sbElem sbe1 = Rep_sbElem sbe2 \<Longrightarrow> sbe1 = sbe2"
  by (simp add: Rep_sbElem_inject)

lemma sbelemwell2fwell[simp]:"Rep_sbElem sbe = f \<Longrightarrow> sbElem_well f"
  using Rep_sbElem by auto

subsection\<open>sbElem properties \label{sub:sbeprop}\<close>
lemma sbtypeempty_sbewell:"chDomEmpty TYPE ('cs) 
                          \<Longrightarrow> sbElem_well (None::('cs \<Rightarrow> M) option)"
  by(simp add: chDom_def)

lemma sbtypeempty_notsbewell:"chDomEmpty TYPE ('cs) 
                           \<Longrightarrow> \<not>sbElem_well (Some (f::'cs \<Rightarrow> M))"
  apply(simp add: chDom_def)
  by (simp add: cEmpty_def image_subset_iff)

text\<open>The following three theorems describe the behaviour of the 
@{type sbElem} type for empty and non-empty domains. Hence, they 
verify the desired properties of our type.\<close>
theorem sbtypeepmpty_sbenone[simp]:
"chDomEmpty TYPE ('cs) \<Longrightarrow> (sbe::'cs\<^sup>\<surd>) = Abs_sbElem(None)"
  apply(simp add: chDom_def)
  apply(rule sbe_eqI)
  by (metis Diff_eq_empty_iff not_Some_eq Rep_sbElem mem_Collect_eq 
      chDom_def sbtypeempty_notsbewell)
text\<open>In case of the empty domain, any @{type sbElem} is 
@{const None}. Hence, we now have to look at the behaviour for 
non-empty domains.\<close>

theorem [simp]:
"\<not>(chDomEmpty TYPE ('c)) \<Longrightarrow> Rep_sbElem (sbe::'c\<^sup>\<surd>) \<noteq> None"
  using sbElem_well.simps(1) sbelemwell2fwell by blast
text\<open>First we show that a sbElem with a non-empty domain never is 
@{const None}. Thus, it is easy to show that there always exists a
total function, that is an @{type sbElem}, if the domain is empty. 
It follows directly from the non-emptiness of a type.\<close>

theorem sbtypenotempty_somesbe:
"\<not>(chDomEmpty TYPE ('c)) \<Longrightarrow> \<exists>f::'c \<Rightarrow> M. sbElem_well (Some f)"
  using sbElem_well.simps(1) sbelemwell2fwell by blast


setup_lifting %invisible type_definition_sbElem
(*<*) (*Not in pdf at the moment, because ugly*)
subsection \<open>sbElem functions \label{sub:sbefun}\<close>

text\<open>This function retrieves an element on channel e from the 
sbElem. This only works if Elements are allowed on channel e and 
channel e is also in type c.\<close>
(*works if sbe \<noteq> None* and 'e \<subseteq> 'c *)
definition sbegetch::"'e \<Rightarrow> 'c\<^sup>\<surd> \<Rightarrow> M"where 
"sbegetch c = (\<lambda> sbe. ((the (Rep_sbElem sbe)) (Abs (Rep c))))"


lemma sbtypenotempty_fex[simp]:
"\<not>(chDomEmpty TYPE ('cs)) \<Longrightarrow> \<exists>f. Rep_sbElem (sbe::'cs\<^sup>\<surd>) = (Some f)"
  apply(rule_tac x="(\<lambda>(c::'c). (THE m. m= sbegetch c sbe))" in exI)
  by(simp add: sbegetch_def)

text\<open>This function Converts the Domain of an sbElem. This works if 
the Domain it converts to, is smaller or equal\<close>
definition sbeConvert::"'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd>"where
"sbeConvert = (\<lambda>sbe. Abs_sbElem(Some (\<lambda>c. sbegetch c sbe)))"

lemma chDomEmpty2chDomEmpty:"chDomEmpty TYPE ('c) \<Longrightarrow> 
  Rep (c::'c) \<in> range(Rep::'d\<Rightarrow> channel) \<Longrightarrow> chDomEmpty TYPE ('d)"
  apply(simp add: chDom_def cEmpty_def,auto)
  by (metis (mono_tags, lifting) Int_Collect cEmpty_def 
      chan_botsingle insert_not_empty le_iff_inf mk_disjoint_insert
      repinrange)

lemma sbgetch_ctype: 
  assumes "Rep (c::'e) \<in> range(Rep::'d \<Rightarrow> channel)" 
  and "\<not>chDomEmpty(TYPE('d))"
  shows "sbegetch c (sbe2::'d\<^sup>\<surd>) \<in> ctype ((Rep::'e \<Rightarrow> channel) c)"
  using assms apply(simp add: sbegetch_def)
  by (metis (no_types, hide_lams) assms(1) assms(2) f_inv_into_f 
      option.sel sbElem_well.simps(2) sbegetch_def sbelemwell2fwell
      sbtypenotempty_fex)

lemma sberestrict_getch:
  assumes"Rep (c::'c) \<in> range(Rep::'d \<Rightarrow> channel)"
  and "\<not>(chDomEmpty TYPE('c))"
  and "range(Rep::'d \<Rightarrow> channel) \<subseteq> range(Rep::'c \<Rightarrow> channel)"
  shows "sbegetch c ((sbeConvert::'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd>) sbe) = sbegetch c sbe"
  using assms
  apply(simp add: sbeConvert_def)
  apply(simp add: sbegetch_def)
  apply(subst Abs_sbElem_inverse)
  apply (smt Rep_sbElem chDom_def f_inv_into_f mem_Collect_eq 
         option.sel rangeI sbElem_well.elims(1) sbElem_well.simps(2)
         subset_iff)
  by simp
  

text\<open>This unites two sbElems. It works, if type e is a subset of the 
     union of 
     type c and d. First sbElem has priority\<close>
definition sbeUnion::"'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd> \<Rightarrow> 'e\<^sup>\<surd>"where
"sbeUnion = (\<lambda>sbe1 sbe2. Abs_sbElem (Some(\<lambda> c. 
if (Rep c \<in> (range (Rep ::'c \<Rightarrow> channel))) 
    then sbegetch c sbe1 
    else  sbegetch c sbe2)))"

lemma sbeunion_getchfst:
  assumes "Rep (c::'c) \<in> range(Rep::'e \<Rightarrow> channel)"
  and "\<not>(chDomEmpty TYPE('c))"
  and "range(Rep::'e \<Rightarrow> channel) \<subseteq> 
       range(Rep::'c \<Rightarrow> channel) \<union> range(Rep::'d \<Rightarrow> channel)"
  shows "sbegetch c ((sbeUnion::'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd> \<Rightarrow> 'e\<^sup>\<surd>) sbe1 sbe2) 
       = sbegetch c sbe1"
  apply(simp add: sbeUnion_def sbegetch_def)
  apply(subst Abs_sbElem_inverse)
  apply (auto simp add: chDom_def assms)
  using assms(2) sbgetch_ctype apply force
  apply (smt assms(2) sbElem_well.simps(2) Un_iff assms(1) assms(3) 
         chDomEmpty2chDomEmpty chan_eq repinrange sbgetch_ctype 
         subset_eq)
  by(simp add: sbegetch_def assms)


lemma sbeunion_getchsnd:
  assumes "Rep (c::'d) \<in> range(Rep::'e \<Rightarrow> channel)"
  and "Rep c \<notin> range(Rep::'c \<Rightarrow> channel)"
  and "\<not>(chDomEmpty TYPE('d))"
  and "range(Rep::'e \<Rightarrow> channel) \<subseteq> 
       range(Rep::'c \<Rightarrow> channel) \<union> range(Rep::'d \<Rightarrow> channel)"
shows"sbegetch c ((sbeUnion::'c\<^sup>\<surd> \<Rightarrow> 'd\<^sup>\<surd> \<Rightarrow> 'e\<^sup>\<surd>) sbe1 sbe2) = 
      sbegetch c sbe2"
  apply(simp add: sbeUnion_def sbegetch_def)
  apply(subst Abs_sbElem_inverse)
  apply (auto simp add: chDom_def assms)
  apply (metis assms(1) assms(3) chDomEmpty2chDomEmpty chan_eq 
         rangeI sbgetch_ctype)
  apply (smt assms sbElem_well.simps(2) Un_iff assms(1) assms(3) 
         chDomEmpty2chDomEmpty chan_eq repinrange sbgetch_ctype 
         subset_eq)
  by(simp add: sbegetch_def assms)
(*>*)

(*<*)
end
(*>*)
