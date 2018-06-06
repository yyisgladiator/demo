(*  Title:        Components.thy
    Author:       Dennis Slotboom, Annika Savelsberg
    E-Mail:       dennis.slotboom@rwth-aachen.de, annika.savelsberg@rwth-aachen.de

    Description:  ABP Components on time-synchronous streams.
*)

chapter {* ABP Components on Time-synchronous Streams *}

theory Components
imports "../../tsynStream"

begin

(* ToDo: not cont.
fun tsynRecProj :: "('a \<times> bool) tsyn discr \<rightarrow> 'a tsyn discr" where
  "tsynRecProj (Discr (Msg (m, b))) = Discr (Msg m)" |
  "tsynRecProj (Discr null) = Discr null"

fixrec tsynRec_h :: "('a \<times> bool) tsyn stream \<rightarrow> bool \<rightarrow> 'a tsyn stream" where
  "tsynRec_h\<cdot>\<epsilon>\<cdot>bit = \<epsilon>" |
  "tsynRec_h\<cdot>(up\<cdot>a && as)\<cdot>bit = (
     if (undiscr a) = null then (up\<cdot>(Discr null)) && tsynRec_h\<cdot>as\<cdot>bit
     else (
       if bit = snd (invMsg (undiscr a)) then up\<cdot>(tsynRecProj a) &&  tsynRec_h\<cdot>as\<cdot>True
       else tsynRec_h\<cdot>as\<cdot>True
     )
  )"
*)

(*
rec :: bool \<rightarrow> ('a \<times> bool) tsyn stream \<rightarrow> (bool tsyn stream \<times> 'a tsyn stream)
rec b \<epsilon> = (\<epsilon>, \<epsilon>)
rec b (- \<bullet> dats) = (- \<bullet> bits, - \<bullet> msgs) where (bits, msgs) = rec(b, dats)
rec b ((m, b) \<bullet> dats) = (b \<bullet> bits, m \<bullet> msgs) where (bits, msgs) = rec(\<not>b, dats)
rec b ((m, \<not>b) \<bullet> dats) = (\<not>b \<bullet> bits, - \<bullet> msgs) where (bits, msgs) = rec(b, dats)
*)


fun rec_h :: "bool \<Rightarrow> ('a \<times> bool) tsyn \<Rightarrow> ('a tsyn \<times> bool)" where
  "rec_h b (Msg (msg,b1)) = (if b1 = b then (Msg msg, \<not>b) else (null, b))" |
  "rec_h b null = (null, b) " 

definition receiver :: "('a \<times> bool) tsyn stream \<rightarrow> 'a tsyn stream" where
  "receiver \<equiv> \<Lambda> s. sscanlA rec_h True\<cdot>s"

lemma receiver_insert: "receiver \<equiv> \<Lambda> s. sscanlA rec_h True\<cdot>s"
  by (simp add: receiver_def)

lemma receiver_test_finstream: 
  "receiver\<cdot>(<[Msg(1,False), null, Msg(2,True),Msg(1,False)]>) = <[null, null,Msg 2, Msg 1]> "
  by (simp add: receiver_insert)

lemma receiver_test_infstream: 
  "receiver\<cdot>((<[Msg(1,False), null, Msg(2,True),Msg(1,False)]>)\<infinity>) 
     = (<[null, null, Msg 2, Msg 1]>)\<infinity>"
  apply (simp add: receiver_insert)
  oops

end