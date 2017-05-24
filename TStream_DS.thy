(*  Title:        TStream_DS.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Workspace for Development of Functions on Timed Streams
*)

theory TStream_DS
 
imports TStream

begin  

(*
lemma "ts\<noteq>\<bottom> \<Longrightarrow> s\<noteq>\<epsilon> \<Longrightarrow> ts_well (\<up>(\<M> t)\<bullet>Rep_tstream ts) \<Longrightarrow> 
  tsZip\<cdot>(Abs_tstream (\<up>(\<M> t))\<bullet>ts)\<cdot>(s\<bullet>xs) = Abs_tstream (\<up>(\<M> (t,s)) \<bullet> (Rep_tstream tsZip\<cdot>(Abs_tstream ts)\<cdot>xs))"
sorry
*)

thm strictify_def  

(* Wenn das 1. Element ein tick ist, dann bilde auf tick ab (und wende funktion auf rest an). Ansonsten wende funktion an *)
  (* Vermutlich muss man das strictify-en, damit es cont ist *)
definition ticktify  :: "('a event stream \<rightarrow> 'b event stream) \<rightarrow> 'a event stream \<rightarrow> 'b event stream" where
"ticktify \<equiv> \<Lambda> f ts. if(lshd\<cdot>ts = updis \<surd>) then updis \<surd> && f\<cdot>(srt\<cdot>ts) else f\<cdot>ts"

definition upApply :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a discr u \<rightarrow> 'b discr u" where
"upApply f \<equiv> \<Lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))"

lemma upApply_mono [simp]: "monofun (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b))))"
apply (rule monofunI, auto)
by (metis (full_types, hide_lams) discrete_cpo upE up_below)

lemma upApply_cont [simp]: "cont (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b))))"
using chfindom_monofun2cont upApply_mono by blast

lemma upApply_rep_eq [simp]: "upApply f\<cdot>(updis a) = updis (f a)"
by (simp add: upApply_def)

(* ToDo: Definition & show cont *)
definition upApplyPair :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a discr\<^sub>\<bottom> \<rightarrow> 'b discr\<^sub>\<bottom> \<rightarrow> 'c discr\<^sub>\<bottom>" where 
"upApplyPair f \<equiv> \<bottom>"

lift_definition delayIdent :: "'a event stream \<rightarrow> 'a event stream" is
  "\<lambda>s . updis \<surd> && s"
by (simp add: cfun_def)

definition msgLscons :: "'a event discr u \<rightarrow> 'a event stream \<rightarrow> 'a event stream" where
"msgLscons \<equiv> \<Lambda> t ts. lscons\<cdot>t\<cdot>ts"

  subsection \<open>Match definitions\<close>

definition 
  match_tick :: "'a event stream \<rightarrow> ('a event stream \<rightarrow> ('b :: pcpo) match) \<rightarrow> 'b match" where
  "match_tick = (\<Lambda> s k. if (lshd\<cdot>s\<noteq>updis \<surd>) then Fixrec.fail else match_lscons\<cdot>s\<cdot>(\<Lambda> x xs. k\<cdot>xs))" 

definition match_message :: "'a event stream \<rightarrow> ('a event discr u \<rightarrow> 'a event stream \<rightarrow> ('b :: pcpo) match) \<rightarrow> 'b match" where
 "match_message = (\<Lambda> s k. if (lshd\<cdot>s=updis \<surd>) then Fixrec.fail else match_lscons\<cdot>s\<cdot>(\<Lambda> x xs. k\<cdot>x\<cdot>xs))" 
(* ToDo: cont *)

  subsection \<open>Lemmata for match definitions\<close>

lemma match_tick_simps [simp]:
  "match_tick\<cdot>\<bottom>\<cdot>k = Fixrec.fail"
  "match_tick\<cdot>(lscons\<cdot>(updis (Msg m))\<cdot>ts)\<cdot>k = Fixrec.fail"
  "match_tick\<cdot>(lscons\<cdot>(updis \<surd>)\<cdot>ts)\<cdot>k = k\<cdot>ts"
  "match_tick\<cdot>(lscons\<cdot>t\<cdot>ts)\<cdot>k = Fixrec.fail"
  "match_tick\<cdot>(delayIdent\<cdot>ts)\<cdot>k = k\<cdot>ts"
apply (simp_all add: match_tick_def)
sorry (* ToDo *)

lemma match_message_simps [simp]:
  "match_message\<cdot>\<bottom>\<cdot>k = Fixrec.fail"
  "match_message\<cdot>(msgLscons\<cdot>t\<cdot>ts)\<cdot>k = k\<cdot>t\<cdot>ts"
  "match_message\<cdot>(delayIdent\<cdot>ts)\<cdot>k = Fixrec.fail"
sorry
 
setup \<open>
  Fixrec.add_matchers
    [ 
      (@{const_name delayIdent}, @{const_name match_tick}),
      (@{const_name msgLscons}, @{const_name match_message})
    ]
\<close>



fixrec tsZip :: "'a stream \<rightarrow> 'b event stream \<rightarrow> ('a \<times> 'b) event stream" where
"tsZip\<cdot>\<bottom>\<cdot>ts = \<bottom>" |
"x\<noteq>\<bottom> \<Longrightarrow> tsZip\<cdot>(lscons\<cdot>x\<cdot>xs)\<cdot>(msgLscons\<cdot>t\<cdot>ts) = (upApply Msg\<cdot>(upApplyPair Pair\<cdot>x\<cdot>(upApply inversMsg\<cdot>t))) && (tsZip\<cdot>xs\<cdot>ts)" |
"x\<noteq>\<bottom> \<Longrightarrow> tsZip\<cdot>(lscons\<cdot>x\<cdot>xs)\<cdot>(delayIdent\<cdot>ts) = delayIdent\<cdot>(tsZip\<cdot>(lscons\<cdot>x\<cdot>xs)\<cdot>ts)"


lemma "tsZip\<cdot>\<bottom>\<cdot>ts = \<bottom>"
by (simp)

(*
lemma "xs\<noteq>\<bottom> \<Longrightarrow> tsZip\<cdot>xs\<cdot>(delayIdent\<cdot>ts) = delayIdent\<cdot>(tsZip\<cdot>xs\<cdot>ts)"
by fixrec_simp
*)




(*
abbreviation
  inversDiscr ::  "'a discr\<^sub>\<bottom> \<Rightarrow> 'a"
    where "inversDiscr e \<equiv> undiscr (case e of Iup m \<Rightarrow> m)"
*)

lift_definition sTupify :: "('a discr\<^sub>\<bottom> \<times> 'b event discr\<^sub>\<bottom>) \<rightarrow> ('a \<times> 'b) event discr\<^sub>\<bottom>" is
"\<lambda> (x, t). case (x,t) of (Iup (Discr mx), Iup (Discr (Msg mt))) \<Rightarrow> Iup (Discr (Msg (mx, mt))) | _ \<Rightarrow> \<bottom>"
apply (simp add: cfun_def)
sorry



fixrec tsZip_helper :: "'a stream \<rightarrow> 'b event stream \<rightarrow>  ('a \<times> 'b) event stream" where
"tsZip_helper\<cdot>\<bottom>\<cdot>ts = \<bottom>"  |
"tsZip_helper\<cdot>xs\<cdot>\<bottom> = \<bottom>"  |
"x\<noteq>\<bottom> \<Longrightarrow> t=updis \<surd> \<Longrightarrow> 
  tsZip_helper\<cdot>(lscons\<cdot>x\<cdot>xs)\<cdot>(lscons\<cdot>t\<cdot>ts) = updis \<surd> && tsZip_helper\<cdot>(lscons\<cdot>x\<cdot>xs)\<cdot>ts" |
(unchecked) "x\<noteq>\<bottom> \<Longrightarrow> t\<noteq>\<bottom> \<Longrightarrow> t\<noteq>updis \<surd> \<Longrightarrow> 
  tsZip_helper\<cdot>(lscons\<cdot>x\<cdot>xs)\<cdot>(lscons\<cdot>t\<cdot>ts) = (sTupify\<cdot>(x, t)) && (tsZip_helper\<cdot>xs\<cdot>ts)"

lemma "tsZip_helper\<cdot>\<bottom>\<cdot>ts = \<bottom>"
by (simp)

(*
fixrec tsRemDups_helper :: "'a event stream \<Rightarrow> 'a option  \<rightarrow> 'a event stream" where
"tsRemDups_helper (inversDiscr q)\<cdot>\<bottom> = \<bottom>"  |
"x=updis \<surd> \<Longrightarrow> 
  tsRemDups_helper (inversDiscr q)\<cdot>(lscons\<cdot>x\<cdot>xs) = \<up>\<surd> \<bullet> tsRemDups_helper (inversDiscr q)\<cdot>xs" |
"x\<noteq>updis \<surd> \<Longrightarrow> x\<noteq>q \<Longrightarrow>
  tsRemDups_helper (inversDiscr q)\<cdot>(lscons\<cdot>x\<cdot>xs) = \<up>(inversDiscr x) \<bullet> tsRemDups_helper (inversDiscr x)\<cdot>xs" |
(unchecked) "x\<noteq>updis \<surd> \<Longrightarrow> x=q \<Longrightarrow> 
  tsRemDups_helper (inversDiscr q)\<cdot>(lscons\<cdot>x\<cdot>xs) = tsRemDups_helper (inversDiscr q)\<cdot>xs"
*)

end  