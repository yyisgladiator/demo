(*  Title:        TimedABP_DS.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Workspace for the  Definition of Alternating Bit Protocol on Timed Streams
*)

chapter {* Alternating Bit Protocol *}       
                                                            
theory TimedABP_DS
imports TimedABP

begin
default_sort countable

(* input: msg from the user, acks from the receiver, ack buffer for the expected ack 
   output: msg and expected ack for the receiver *)
fixrec tsSender :: "'a tstream \<rightarrow> bool tstream \<rightarrow> bool discr \<rightarrow> ('a \<times> bool) tstream" where
  (* bottom case *)
"tsSender\<cdot>\<bottom>\<cdot>acks\<cdot>ack = \<bottom>" |
"tsSender\<cdot>msg\<cdot>\<bottom>\<cdot>ack = \<bottom>" |

  (* if input and ack is a tick \<Longrightarrow> send tick *)
"tsSender\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack 
        = delayFun\<cdot>(tsSender\<cdot>msg\<cdot>acks\<cdot>ack)" |

  (* if an input and ack is a tick \<Longrightarrow> send msg again *)
"msg\<noteq>\<bottom> \<Longrightarrow> tsSender\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack 
  = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(tsSender\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>acks\<cdot>ack)" |

  (* if input is a tick and wrong ack from the receiver \<Longrightarrow> send tick *)
"acks\<noteq>\<bottom> \<Longrightarrow> tsSender\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack 
                    = delayFun\<cdot>(tsSender\<cdot>msg\<cdot>acks\<cdot>ack)" |

  (* if an input and ack from the receiver *)
"msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow> tsSender\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack = 
  (* ack for the current msg \<Longrightarrow> send next msg *)
  (if (a = ack) then tsSender\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>(undiscr ack)))
  (* wrong ack for the current msg \<Longrightarrow> send msg again *)
   else tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(tsSender\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>acks\<cdot>ack))"


(* lemmata for sender, see BS01, page 103 *)

(* fds = stream of transmitted messages
   fb = corresponding stream of bits
   fas = stream of received acknowledgments
   i = input stream
   as = acks stream
   ds = output stream *)

(* fds \<sqsubseteq> i where fds = map(\<alpha>.ds, \<Pi>1) *)
(* fds is a prefix of i *)
lemma "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSender\<cdot>i\<cdot>as\<cdot>ack))) \<sqsubseteq> tsAbs\<cdot>i"
oops

(* \<alpha>.fb = fb  where fb = map(\<alpha>.ds, \<Pi>2) *)
(* each new data element from i is assigned a bit different from the bit assigned to 
   the previous one *)    
lemma 
  "tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSender\<cdot>i\<cdot>as\<cdot>ack))))
    = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSender\<cdot>i\<cdot>acks\<cdot>ack)))"
oops

(* #fds = min{#i, #fas+1} where fds = map(\<alpha>.ds, \<Pi>1), fas = \<alpha>.as *)
(* when an acknowledgment is received then the next data next data element will eventually
   be transmitted given that there are more data elements to transmit *)
(*
lemma
  "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSender\<cdot>i\<cdot>as\<cdot>ack)))) = min (#(tsAbs\<cdot>i)) ((#(tsAbs\<cdot>(tsRemDups\<cdot>as)))+1)"
oops
*)

(* #i > #fas \<Longrightarrow> #ds = \<infinity> where fas = \<alpha>.as *)
(* if a data element is never acknowledged despite repetitive transmission by the sender then the
   sender never stops transmitting this data element *)
lemma "#(tsAbs\<cdot>i)>#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<Longrightarrow> #(tsAbs\<cdot>(tsSender\<cdot>i\<cdot>as\<cdot>ack)) = \<infinity>"
oops

end