theory EinChannel

imports bundle.SB automaton.dAutomaton_causal

begin
text \<open>You need to set THIS directory as Session-Directory. NOT the root-directory of the repository\<close>

lemma cempty_empty[simp]: "cEmpty = {c3}"
  apply(auto simp add: cEmpty_def)
  by(insert ctype.elims,auto)

typedef singleChan = "{c1}"
  by blast

lemma [simp]: "range Rep_singleChan = {c1}"
  using type_definition.Rep_range type_definition_singleChan by blast

lemma "Abs_singleChan c1 = undefined"
  oops
text \<open>Macht nicht wirklich sinn, aber da wir nur den einen Channel haben...
  Normalerweise erstellt der Nutzer hier seine eigenen channels zuerst\<close>
instantiation singleChan::chan
begin
definition "Rep = Rep_singleChan"
  
  instance
    apply(intro_classes)
     apply(auto simp add: Rep_singleChan_def)
    by (meson Rep_singleChan_inject injI)

end






section\<open>Datatype Konstruktor\<close>

(* FYI: the old approach from v2 to create the datatype is not really reusable, 
  because: 
      lift_definition elem_raw_i :: "int \<Rightarrow> ndaExampleMessage sbElem" is
  Thats an old "single-channel" setter...
  One has to replace the "ndaExampleMessage" with a "chan"... but which?
  There can only be ONE channel in the replacement! ! !
  But what if the channel-datatype of the component has 2 or more channels?
*)

text \<open>Motivation: I HATE freemarker and other templates. 
  And the workflow sucks. The generator people have no idea about isabelle, 
  feature-request take FOREVER and then it might not work in every case\<close>

text\<open>Goal: Move the heavy-stuff from the Generator to Isabelle.
  Pretty much every proof should be done in Isabelle, the generator
  can still create datatypes, functions and so on\<close>

text\<open>Implementation: Is using Locales... \<close>


text \<open>\<open>'a\<close> should be interpreted as a tuple. The goal of this local is to create a
  bijective mapping from \<open>'a\<close> to \<open>'cs\<close>.
  The user can freely choose \<open>'a\<close>, hence he will not use the datatype \<open>M\<close>. 
  for example \<open>'a = (nat \<times> bool)\<close> which maps to a bundle with one bool-channel and one nat-channel\<close>
locale sbeGen =
  fixes lConstructor::"'a::countable \<Rightarrow> 'cs::chan \<Rightarrow> M"
  assumes c_well: "\<And>a. sbElem_well (Some (lConstructor a))"
      and c_inj: "inj lConstructor" 
      and c_surj: "\<And>sbe. sbElem_well (Some sbe) \<Longrightarrow> sbe\<in>range lConstructor" (* Schöner? *)
begin

lemma empty_neq: "\<not>chIsEmpty TYPE ('cs)"
  using c_well sbtypeempty_notsbewell by blast

lift_definition setter::"'a \<Rightarrow> 'cs\<^sup>\<surd>" is "Some o lConstructor"
  using c_well by auto

definition getter::"'cs\<^sup>\<surd> \<Rightarrow> 'a" where
"getter  = (inv lConstructor) o the o Rep_sbElem"

lemma get_set[simp]: "getter (setter a) = a"
  unfolding getter_def
  by (simp add: setter.rep_eq c_inj)  

lemma set_inj: "inj setter"
  by (metis get_set injI)

lemma set_surj: "surj setter"
  unfolding setter_def
  apply(cases "\<not>(chIsEmpty(TYPE('cs)))")
proof(simp add: surj_def,auto)
  fix y::"'cs\<^sup>\<surd>"
  assume chnEmpty:"\<not> chIsEmpty TYPE('cs)"
  obtain f where f_def:"Rep_sbElem y=(Some f)"
    using sbeGen.empty_neq sbeGen_axioms sbtypenotempty_fex  by auto
  then obtain x where x_def:"f = lConstructor x"
    by (metis c_inj c_surj f_the_inv_into_f sbelemwell2fwell)
  then show "\<exists>x::'a. y = Abs_sbElem (Some (lConstructor x))"
    by (metis Rep_sbElem_inverse f_def)
next
  fix x::"'cs\<^sup>\<surd>"
  assume chEmpty:"chIsEmpty TYPE('cs)"
  then have"\<And>f. \<not>sbElem_well (Some f)"
    using empty_neq by auto
  then show "chIsEmpty TYPE('cs) \<Longrightarrow> x \<in> range (\<lambda>x::'a. Abs_sbElem (Some (lConstructor x)))"
    using c_well by metis
qed 

lemma set_bij: "bij setter"
  by (metis bijI inj_onI sbeGen.get_set sbeGen_axioms set_surj)

lemma get_inv_set: "getter = (inv setter)"
  by (metis get_set set_surj surj_imp_inv_eq)

lemma set_get[simp]: "setter (getter sbe) = sbe"
  apply(simp add: get_inv_set)
  by (meson bij_inv_eq_iff set_bij)

lemma "getter A = getter B \<Longrightarrow> A = B"
  by (metis set_get)

fixrec setterSB::"'a stream \<rightarrow> 'cs\<^sup>\<Omega>" where
"setterSB\<cdot>((up\<cdot>l)&&ls) = (setter (undiscr l)) \<bullet>\<^sup>\<surd> (setterSB\<cdot>ls)" 

fixrec getterSB::"'cs\<^sup>\<Omega> \<rightarrow> 'a stream" where
"getterSB\<cdot>x = \<bottom>" 
(* Man kann auch einen getterSB definieren (mit fixrec, nachdem das klappt(über endliche bündel)).... 
    Sollte man auch, die frage ist nur wie weitflächig der einsetzbar ist. Er schneidet längere Elemente ab *)


(* TODO: lemma über setterSB und getterSB *)
end






locale sscanlGen =
  fixes da::"('state::countable, 'in::{chan, finite}, 'out::chan, 'initOut::chan) dAutomaton_weak"
  and fin::"'a::countable \<Rightarrow> 'in \<Rightarrow> M"  
  and fout::"'b::countable \<Rightarrow> 'out \<Rightarrow> M"
  assumes sbegenfin:"sbeGen fin"
      and sbegenfout:"sbeGen fout"
begin

abbreviation "stupidTransition \<equiv> (\<lambda> s a. 
  let (nextState, nextOut) = dawTransition da s (sbeGen.setter fin a) in
     (nextState, sbeGen.getter fout nextOut)
)"

lemma daut2sscanl:"dawStateSem da state\<cdot>(input::'in\<^sup>\<Omega>) = 
       sbeGen.setterSB fout\<cdot>(sscanlAsnd stupidTransition state\<cdot>(sbeGen.getterSB\<cdot>input))"
  sorry
(* Frag mich nicht, wieso "setterSB" "fout" als parameter braucht
  aber der "getterSB" nicht *)

(* TODO: semantikabbildung "dawStateSem" anlegen *)

(* TODO: initiale ausgabe ... "sscanlA" kann nichts partielles ausgben.
  dh alles oder nichts. Das kann man durch den typ abfangen!
    * weak = "chIstEmpty" als assumption (oder besser, dafür eine klasse anlegen)
    * strong = gleicher typ wie ausgabe
*)

end







locale sumChanSB = (* TODO: anpassen wie oben, z.B. reihenfolge argumente *)
  fixes lConstructor::" 'a::pcpo \<Rightarrow> 'cs::chan  \<Rightarrow> M stream"
  assumes c_type: "\<And>a c. sValues (lConstructor a c) \<subseteq> ctype (Rep c)"
    and c_inj: "inj lConstructor"
    and c_surj: "\<And>f. sb_well f \<Longrightarrow> f\<in>range lConstructor" (* Schöner? *)
begin

lift_definition setter::"'a \<Rightarrow> ('cs::chan)\<^sup>\<Omega>"is"lConstructor"
  by (simp add: c_type sb_well_def)

definition getter::"'cs\<^sup>\<Omega> \<Rightarrow> 'a" where
"getter= (inv lConstructor) o  Rep_sb"

lemma get_set[simp]: "getter (setter a) = a"
  unfolding getter_def
  by (simp add: setter.rep_eq c_inj)  

lemma set_inj: "inj setter"
  by (metis get_set injI)

lemma set_surj: "surj setter"
  unfolding setter_def
proof(simp add: surj_def,auto)
  fix y::"'cs\<^sup>\<Omega>"
 obtain f where f_def:"Rep_sb y=f"
   by simp
 then obtain x where x_def:"f = lConstructor x"
    by (metis c_inj c_surj f_the_inv_into_f sbwell2fwell)
  then show "\<exists>x::'a. y = Abs_sb (lConstructor x)" 
    by (metis Rep_sb_inverse f_def)
qed

lemma set_bij: "bij setter"
  using bij_betw_def set_inj set_surj by auto

lemma get_inv_set: "getter = (inv setter)"
  by (metis get_set set_surj surj_imp_inv_eq)

lemma set_get[simp]: "setter (getter sbe) = sbe"
  apply(simp add: get_inv_set)
  by (meson bij_inv_eq_iff set_bij)

lemma "getter A = getter B \<Longrightarrow> A = B"
  by (metis set_get)

end



section \<open>Beispiel\<close>

typedef mymy = "{c1, c2}"
  by blast

definition "mymyC1 = Abs_mymy c1"
definition "mymyC2 = Abs_mymy c2"

(* Fuck Yeah, pattern matching! *)
(* TODO: is it possible to put everything in a "bundle"? 
    eg. bundleName.c1 = mymyC1
        bundleName.setter = dudu.setter"
*)
free_constructors mymy for "mymyC1"  | "mymyC2"
   apply auto
  unfolding mymyC1_def mymyC2_def
  apply (metis Rep_mymy Rep_mymy_inverse empty_iff insert_iff)
  by (meson channel.distinct(1) insertI1 insertI2 type_definition.Abs_inject type_definition_mymy)

lemma mymy_rep_range [simp]:"range Rep_mymy = {c1, c2}"
  using type_definition.Rep_range type_definition_mymy by blast

instantiation mymy::chan
begin
definition "Rep = Rep_mymy" (* TODO: abbreviation oÄ, ich will nicht immer "Rep_mymy_def" anwenden *) 

instance
  apply(intro_classes)
  unfolding Rep_mymy_def apply simp
  by (meson Rep_mymy_inject injI)
end



lemma myc1_rep [simp]: "Rep (mymyC1) = c1"
  unfolding Rep_mymy_def mymyC1_def
  by (simp add: Abs_mymy_inverse)

lemma myc2_rep [simp]: "Rep (mymyC2) = c2"
  unfolding Rep_mymy_def mymyC2_def
  by (simp add: Abs_mymy_inverse)

(* :/ Schöner? *)
fun orderChan::"('nat::type \<Rightarrow> 'a::type) \<Rightarrow> ('bool::type \<Rightarrow> 'a) \<Rightarrow>('nat\<times>'bool) \<Rightarrow> mymy \<Rightarrow> 'a" where
"orderChan Cc1 Cc2 (port_c1, port_c2) mymyC1 = Cc1 port_c1" |
"orderChan Cc1 Cc2 (port_c1, port_c2) mymyC2 = Cc2 port_c2"

abbreviation "buildSBE \<equiv> orderChan \<N> \<B>" 

lemma build_ctype: "buildSBE a c \<in> ctype (Rep c)"
  by(cases c; cases a; simp)

lemma build_inj: "inj buildSBE"
  apply(rule injI)
  apply(case_tac x; case_tac y; simp)
  by (metis M.inject orderChan.simps)

lemma build_range: "range (\<lambda>a. buildSBE a c) = ctype (Rep c)"
  apply(cases c)
  by(auto simp add: image_iff)

lemma build_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildSBE"
proof -
  have ctypewell:"\<And>c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildSBE a c)"
    by (simp add: build_range)
  hence "\<exists>prod. sbe = buildSBE prod"
    apply(subst fun_eq_iff,auto) (*TODO: shorter proof*)
  proof -
    { fix mm :: "nat \<Rightarrow> bool \<Rightarrow> mymy"
      obtain bb :: bool where
        ff1: "(\<not> bb) = (\<forall>x2. \<B> x2 \<noteq> sbe mymyC2)"
        by moura
      then have ff2: bb
        by (metis ctype.simps(2) ctypewell myc2_rep rangeE)
      obtain bba :: bool where
        ff3: "(\<not> bba) = (\<forall>x1. \<N> x1 \<noteq> sbe mymyC1)"
        by moura
      then have bba
        by (metis ctype.simps(1) ctypewell myc1_rep rangeE)
      then have "\<exists>n b. sbe (mm n b) = buildSBE (n, b) (mm n b)"
        using ff3 ff2 ff1 by (metis (full_types) mymy.exhaust orderChan.simps(1) orderChan.simps(2)) }
    then show "\<exists>n b. \<forall>m. sbe m = buildSBE (n, b) m"
      by metis
  qed
  thus ?thesis
    by auto
qed

interpretation dudu: sbeGen "buildSBE" (*WTF Nitpick ? ? ?*)
  apply(unfold_locales)
  apply (simp add: build_ctype)
  apply (simp add: build_inj)
  using build_surj by auto

term "dudu.setter"

term "curry dudu.setter"  (* If you prefer the "old way" *)

lemma "dudu.getter (dudu.setter (1,True)) = (1,True)"
  by simp

(*buildSB interpretation*)

abbreviation "buildSB \<equiv> orderChan (Rep_cfun (smap \<N>)) (Rep_cfun (smap \<B>))" 

lemma buildSB_ctype: "sValues(buildSB a c) \<subseteq> ctype (Rep c)"
  by(cases c; cases a; simp add: sValues_def)

lemma buildSB_inj: "inj buildSB"
  apply(rule injI)
  apply(case_tac x; case_tac y; simp)
  apply(auto)
  sorry

lemma buildSB_range: "(\<Union>a. sValues (buildSB a c)) = ctype (Rep c)"
  apply(cases c)
  apply auto 
  apply (metis (no_types, lifting) in_mono sValues_def smap_sdom_range)
  apply(rule_tac x="\<up>xa" in exI) 
  apply(simp add: sValues_def)
  apply (metis (mono_tags) ctype.simps(2) image_iff range_eqI sValues_def smap_sdom)
  apply(rule_tac x="\<up>xa" in exI) 
  by(simp add: sValues_def)

lemma buildSB_surj: assumes "sb_well f"
  shows "f \<in> range buildSB"
proof -
  have ctypewell:"\<And>c. sValues (f c) \<subseteq> ctype (Rep c)"
    using assms sb_well_def by blast
  hence "\<And>c. sValues(f c) \<subseteq> range (\<lambda>a. buildSBE a c)"
    by (simp add: build_range)
  hence "\<exists>prod. f = buildSB prod"
    apply(subst fun_eq_iff,auto,simp add: sValues_def) (*TODO: shorter proof*)
    sorry
  thus ?thesis
    by auto
qed


interpretation duda: sumChanSB "buildSB"
  apply(unfold_locales)
  apply (simp add: buildSB_ctype)
  apply (simp add: buildSB_inj)
  by (simp add: buildSB_surj)

term "duda.setter"
term "duda.getter"





end