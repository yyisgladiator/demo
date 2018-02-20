(*  Title:        Sender_DS.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Sender Component of the ABP on Timed Streams
*)

chapter {* Sender of the Alternating Bit Protocol *}
                                                            
theory Sender_DS
imports "../../TStream"

begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* definition *}
(* ----------------------------------------------------------------------- *)

text {* input: msg from the user, acks from the receiver, ack buffer for the expected ack 
        output: msg and expected ack for the receiver *}
fixrec tsSnd_h :: "'a tstream \<rightarrow> bool tstream \<rightarrow> bool discr \<rightarrow> ('a \<times> bool) tstream" where
  (* bottom case *)
"tsSnd_h\<cdot>\<bottom>\<cdot>acks\<cdot>ack = \<bottom>" |
"tsSnd_h\<cdot>msg\<cdot>\<bottom>\<cdot>ack = \<bottom>" |

  (* if an input and ack from the receiver *)
"msg \<noteq> \<bottom> \<Longrightarrow> acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack = 
  (* ack for the current msg \<Longrightarrow> send next msg *)
  (if (a = ack) then tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>(undiscr ack)))
  (* wrong ack for the current msg \<Longrightarrow> send msg again *)
   else tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>msg)\<cdot>acks\<cdot>ack))" |

  (* if an input and ack is a tick \<Longrightarrow> send msg again plus a tick
     if transmission starts with tick \<Longrightarrow> #\<surd> acks = \<infinity> *)
"msg \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack 
  = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(delayFun\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>msg)\<cdot>acks\<cdot>ack))" |

  (* if input and ack is a tick \<Longrightarrow> send one tick *)
"tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack
   = delayFun\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>ack)" |

  (* if input is a tick \<Longrightarrow> send tick and remove wrong ack *)
"acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack
  = delayFun\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>ack)"

definition tsSnd :: "'a tstream \<rightarrow> bool tstream \<rightarrow> ('a \<times> bool) tstream" where
"tsSnd \<equiv> \<Lambda> msg acks. delay (tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr True))"

(*
text {* input: msg from the user, acks from the receiver, ack buffer for the expected ack 
        output: msg and expected ack for the receiver *}
fixrec tsSnd_h :: "'a tstream \<rightarrow> bool tstream \<rightarrow> bool discr \<rightarrow> nat discr \<rightarrow> ('a \<times> bool) tstream" where
  (* bottom case *)
"tsSnd_h\<cdot>\<bottom>\<cdot>acks\<cdot>ack\<cdot>cou = \<bottom>" |
"tsSnd_h\<cdot>msg\<cdot>\<bottom>\<cdot>ack\<cdot>cou = \<bottom>" |

  (* if an input and ack from the receiver *)
"msg \<noteq> \<bottom> \<Longrightarrow> acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack\<cdot>cou = 
  (* ack for the current msg \<Longrightarrow> send next msg *)
  (if (a = ack) then tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>(undiscr ack)))\<cdot>cou
  (* wrong ack for the current msg \<Longrightarrow> send msg again *)
   else tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>msg)\<cdot>acks\<cdot>ack\<cdot>cou))" | 

  (* if an input and ack is a tick \<Longrightarrow> send msg again plus a tick
     if transmission starts with tick \<Longrightarrow> #\<surd> acks = \<infinity> *)
"msg \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack\<cdot>cou  = 
  (if (cou = Discr 0) then delayFun\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>msg)\<cdot>acks\<cdot>ack\<cdot>(Discr 1))
   else tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(delayFun\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>msg)\<cdot>acks\<cdot>ack\<cdot>(Discr ((undiscr cou) - 1)))))" |

  (* if input is a tick \<Longrightarrow> send tick and remove wrong ack *)
"acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack\<cdot>cou
  = delayFun\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>ack\<cdot>cou)"

definition tsSnd :: "'a tstream \<rightarrow> bool tstream \<rightarrow> ('a \<times> bool) tstream" where
"tsSnd \<equiv> \<Lambda> msg acks. delay (tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr True)\<cdot>(Discr 1))"

lemma tssnd_insert: "tsSnd\<cdot>msg\<cdot>acks = delay (tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr True)\<cdot>(Discr 1))"
  by (simp add: tsSnd_def)

lemma tssnd_h_strict [simp]:
"tsSnd_h\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>ack\<cdot>cou = \<bottom>"
"tsSnd_h\<cdot>\<bottom>\<cdot>acks\<cdot>ack\<cdot>cou = \<bottom>"
"tsSnd_h\<cdot>msg\<cdot>\<bottom>\<cdot>ack\<cdot>cou = \<bottom>"
  by (fixrec_simp)+
*)

end