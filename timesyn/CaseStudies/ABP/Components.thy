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

end