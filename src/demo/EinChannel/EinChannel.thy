theory EinChannel

imports bundle.SB automaton.dAutomaton_causal

begin
text \<open>You need to set THIS directory as Session-Directory. NOT the root-directory of the repository\<close>

lemma cempty_empty[simp]: "cEmpty = {c3}"
  apply(auto simp add: cEmpty_def)
  apply(insert ctype.elims,auto)
  by (metis channel.exhaust ctype.simps(1) ctype.simps(2) ctype.simps(4) ctype.simps(5) ctype.simps(6)
      empty_not_UNIV image_is_empty  sup_eq_bot_iff)

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
  fixes lConstructor::"'a::countable \<Rightarrow> 'cs::{chan, finite} \<Rightarrow> M"
  assumes c_well: "\<And>a. \<not>chIsEmpty TYPE ('cs) \<Longrightarrow> sbElem_well (Some (lConstructor a))"
      and c_inj: "\<not>chIsEmpty TYPE ('cs) \<Longrightarrow> inj lConstructor" 
      and c_surj: "\<And>sbe. \<not>chIsEmpty TYPE ('cs) \<Longrightarrow> sbElem_well (Some sbe) \<Longrightarrow> sbe\<in>range lConstructor" (* Schöner? *)
      and c_empty: "\<And>a b::'a. chIsEmpty TYPE ('cs) \<Longrightarrow> a=b"
begin

lift_definition setter::"'a \<Rightarrow> 'cs\<^sup>\<surd>" is 
  "if(chIsEmpty TYPE ('cs)) then (\<lambda>_. None) else Some o lConstructor"
  using c_well sbtypeempty_sbewell by auto

definition getter::"'cs\<^sup>\<surd> \<Rightarrow> 'a" where
"getter sbe = (case (Rep_sbElem sbe) of None \<Rightarrow> (SOME x. True) | 
      Some f \<Rightarrow> (inv lConstructor) f)" (* geht was anderes als "SOME x"? *)

lemma get_set[simp]: "getter (setter a) = a"
  unfolding getter_def
  by (simp add: setter.rep_eq c_inj c_empty)

lemma set_inj: "inj setter"
  by (metis get_set injI)

lemma set_surj: "surj setter"
  unfolding setter_def
  apply(cases "\<not>(chIsEmpty(TYPE('cs)))")
proof(simp add: surj_def,auto)
  fix y::"'cs\<^sup>\<surd>"
  assume chnEmpty:"\<not> chIsEmpty TYPE('cs)"
  obtain f where f_def:"Rep_sbElem y=(Some f)"
    using chnEmpty sbtypenotempty_fex by auto
  then obtain x where x_def:"f = lConstructor x"
    by (metis c_inj c_surj f_the_inv_into_f sbelemwell2fwell chnEmpty)
  then show "\<exists>x::'a. y = Abs_sbElem (Some (lConstructor x))"
    by (metis Rep_sbElem_inverse f_def)
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

lemma settersb_unfold:"setterSB\<cdot>(\<up>a \<bullet> s) = (setter a) \<bullet>\<^sup>\<surd> setterSB\<cdot>s"
  unfolding setterSB_def
  apply(subst fix_eq)
  apply simp 
  apply(subgoal_tac "\<exists>l. \<up>a \<bullet> s = (up\<cdot>l)&&s")
  apply auto 
  apply (metis (no_types, lifting) lshd_updis stream.sel_rews(4) undiscr_Discr up_inject)
  by (metis lscons_conv)

lemma settersb_emptyfix:"chIsEmpty (TYPE ('cs)) \<Longrightarrow> setterSB\<cdot>s = \<bottom>"
  by simp

lemma settersb_epsbot:"setterSB\<cdot>\<epsilon> = \<bottom>"
  apply(simp add: setterSB_def)
  apply(subst fix_eq)
  by auto

(* TODO : Dokumentireen! *)
definition getterSB::"'cs\<^sup>\<Omega> \<rightarrow> 'a stream" where
"getterSB \<equiv> fix\<cdot>(\<Lambda> h. sb_case\<cdot>(\<lambda>sbe. \<Lambda> sb. updis (getter sbe) && h\<cdot>sb))"

lemma gettersb_unfold:"getterSB\<cdot>(sbe \<bullet>\<^sup>\<surd> sb) = \<up>(getter sbe) \<bullet> getterSB\<cdot>sb"
  unfolding getterSB_def
  apply(subst fix_eq)
  apply simp
  by (simp add: lscons_conv)

lemma gettersb_emptyfix:"chIsEmpty (TYPE ('cs)) \<Longrightarrow> getterSB\<cdot>sb = \<up>(getter (Abs_sbElem None)) \<bullet> getterSB\<cdot>sb"
  by (metis(full_types) gettersb_unfold sbtypeepmpty_sbbot)

lemma gettersb_realboteps:"\<not>(chIsEmpty (TYPE ('cs))) \<Longrightarrow> getterSB\<cdot>\<bottom> = \<epsilon>"
  unfolding getterSB_def
  apply(subst fix_eq)
  by (simp add: sb_cases_bot)
(* TODO: lemma über setterSB und getterSB *)

lemma assumes "chIsEmpty (TYPE ('cs))"
  shows "\<exists>a. (getterSB\<cdot>sb) = (sinftimes(\<up>(a)))"
  apply(insert assms,subst gettersb_emptyfix,simp) 
  using gettersb_emptyfix s2sinftimes by auto
  
 (* TODO; warning entfernen. abbreviation-prioritäten für \<infinity>?*)

lemma "sbLen (setterSB\<cdot>s) = #s"
  oops(* gilt nicht für chIsEmpty *)

lemma "a \<sqsubseteq> getterSB\<cdot>(setterSB\<cdot>a)"
  apply(induction a rule: ind)
  apply(auto)
  apply (simp add: gettersb_unfold settersb_unfold)
  by (simp add: monofun_cfun_arg)

lemma getset_eq:"\<not>chIsEmpty (TYPE ('cs)) \<Longrightarrow> getterSB\<cdot>(setterSB\<cdot>a) = a"
  apply(induction a rule: ind)
  apply(auto)
  apply (simp add: gettersb_realboteps settersb_epsbot)
  by (simp add: gettersb_unfold settersb_unfold)

lemma "setterSB\<cdot>(getterSB\<cdot>sb) \<sqsubseteq> sb"
  apply(induction sb)
  apply auto
  apply(cases "chIsEmpty(TYPE('cs))")
  apply (metis (full_types)minimal sbtypeepmpty_sbbot)
  apply(simp add: sbIsLeast_def)
  oops
 

lemma setget_eq:"(\<forall>c. #(sb \<^enum> c) = k) \<Longrightarrow>setterSB\<cdot>(getterSB\<cdot>sb) = sb"
  apply(induction sb arbitrary: k)
  apply auto
  apply(rule adm_imp)
     apply auto 
  apply(rule admI)
  defer
  apply(case_tac "chIsEmpty (TYPE ('cs))")
  apply (metis (full_types)sbtypeepmpty_sbbot)
    apply(simp add: sbIsLeast_def)
  apply(subgoal_tac "k = 0",auto)
     apply (metis gettersb_realboteps sb_eqI sbgetch_bot settersb_epsbot)
    defer
    apply(subst gettersb_unfold)
    apply(subst settersb_unfold,simp)
  apply(subgoal_tac "\<And>c. #(sb \<^enum> c) \<le> #(sbe \<bullet>\<^sup>\<surd> sb  \<^enum>  c)",auto)
  oops  (* Nur für gleichlange ströme *)
end






locale sscanlGen =
  fixes da::"('state::countable, 'in::{chan, finite}, 'out::{chan,finite}, 'initOut::chan) dAutomaton_weak"
  and fin::"'a::countable \<Rightarrow> 'in \<Rightarrow> M"  
  and fout::"'b::countable \<Rightarrow> 'out \<Rightarrow> M"
  assumes sbegenfin:"sbeGen fin"
      and sbegenfout:"sbeGen fout"
begin

abbreviation "sscanlTransition \<equiv> (\<lambda> s a. 
  let (nextState, nextOut) = dawTransition da s (sbeGen.setter fin a) in
     (nextState, sbeGen.getter fout nextOut)
)"

lemma daut2sscanl:"dawStateSem da state\<cdot>(input::'in\<^sup>\<Omega>) = 
       sbeGen.setterSB fout\<cdot>(sscanlAsnd sscanlTransition state\<cdot>(sbeGen.getterSB fin\<cdot>input))"
  sorry

lemma daut2sscnalinit:"range(Rep::'out \<Rightarrow> channel) = range(Rep::'initOut\<Rightarrow> channel) \<Longrightarrow> dawSem da\<cdot>input = 
  sbeConvert(dawInitOut da) \<bullet>\<^sup>\<surd> dawStateSem da state\<cdot>(input::'in\<^sup>\<Omega>)"
  sorry

(* TODO: initiale ausgabe ... "sscanlA" kann nichts partielles ausgben.
  dh alles oder nichts. Das kann man durch den typ abfangen!
    * weak = "chIstEmpty" als assumption (oder besser, dafür eine klasse anlegen)
    * strong = gleicher typ wie ausgabe
*)

end

locale smapGen =
 fixes da::"('state::countable, 'in::{chan, finite}, 'out::{chan,finite}, 'initOut::chan) dAutomaton_weak"
  and fin::"'a::countable \<Rightarrow> 'in \<Rightarrow> M"  
  and fout::"'b::countable \<Rightarrow> 'out \<Rightarrow> M"
  assumes scscanlgenf:"sscanlGen fin fout"
  and singlestate:"is_singleton(UNIV::'state set)"
begin

abbreviation "smapTransition \<equiv> (\<lambda>a. 
  let nextOut = snd(dawTransition da (dawInitState da) (sbeGen.setter fin a)) in
     sbeGen.getter fout nextOut)"

lemma daut2smap:"dawStateSem da state\<cdot>(input::'in\<^sup>\<Omega>) = 
       sbeGen.setterSB fout\<cdot>(smap smapTransition\<cdot>(sbeGen.getterSB fin\<cdot>input))"
  sorry

end

sublocale  smapGen \<subseteq> sscanlGen
  by (simp add: scscanlgenf)





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

instance mymy::finite
  sorry

interpretation dudu: sbeGen "buildSBE" (*WTF Nitpick ? ? ?*)
  apply(unfold_locales)
  apply (simp add: build_ctype)
  apply (simp add: build_inj)
  using build_surj sorry

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