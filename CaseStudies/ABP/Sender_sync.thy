chapter {* Alternating Bit Protocol *}       
                                                            
theory Sender_sync
imports "../../TStream"
begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* definition of the set of sender *}
(* ----------------------------------------------------------------------- *)

fixrec tsTakeFirstTick :: "'a tstream \<rightarrow> 'a tstream" where
"tsTakeFirstTick\<cdot>\<bottom> = \<bottom>" |
"tsTakeFirstTick\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = ts" |
"ts \<noteq> \<bottom> \<Longrightarrow> tsTakeFirstTick\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) = tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>(tsTakeFirstTick\<cdot>ts)"

fixrec tsSnd_h :: "'a tstream \<rightarrow> bool tstream \<rightarrow> bool discr \<rightarrow> nat discr \<rightarrow> ('a \<times> bool) tstream" where
  (* bottom case *)
"tsSnd_h\<cdot>\<bottom>\<cdot>acks\<cdot>ack\<cdot>cnt = \<bottom>" |
"tsSnd_h\<cdot>msg\<cdot>\<bottom>\<cdot>ack\<cdot>cnt = \<bottom>" |

"msg \<noteq> \<bottom> \<Longrightarrow> acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack\<cdot>cnt
 = (if (a = ack) then tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>(undiscr ack)))\<cdot>(Discr 0)
    else (tsSnd_h\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>msg)\<cdot>acks\<cdot>ack)\<cdot>cnt)" |

"msg \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack\<cdot>cnt
 = (if (cnt=Discr 0) then (tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(delayFun\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>(tsTakeFirstTick\<cdot>msg))\<cdot>acks\<cdot>ack\<cdot>(Discr 2))))
   else (tsSnd_h\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>(tsTakeFirstTick\<cdot>msg))\<cdot>acks\<cdot>ack\<cdot>(Discr ((undiscr cnt) -1))))" |

  (* if input is a tick \<Longrightarrow> send tick *)
"tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack\<cdot>cnt
   = delayFun\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>ack\<cdot>cnt)" |

"acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack\<cdot>cnt
  = (tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>acks\<cdot>ack\<cdot>cnt)"

definition tsSnd :: "'a tstream \<rightarrow> bool tstream \<rightarrow> ('a \<times> bool) tstream" where
"tsSnd \<equiv> \<Lambda> msg acks. delay (tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr True)\<cdot>(Discr 0))"  

(* ----------------------------------------------------------------------- *)
section {* basic properties *}
(* ----------------------------------------------------------------------- *)

lemma tssnd_insert: "tsSnd\<cdot>msg\<cdot>acks = delay (tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr True))"
  by (simp add: tsSnd_def)

lemma tssnd_h_strict [simp]:
"tsSnd_h\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>ack = \<bottom>"
"tsSnd_h\<cdot>\<bottom>\<cdot>acks\<cdot>ack = \<bottom>"
"tsSnd_h\<cdot>msg\<cdot>\<bottom>\<cdot>ack = \<bottom>"
  by (fixrec_simp)+

lemma tssnd_h_delayfun_nack:
  "msg \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(delayFun\<cdot>acks)\<cdot>(Discr ack) 
  = tsMLscons\<cdot>(updis (m, ack))\<cdot>(delayFun\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>(tsTakeFirstTick\<cdot>msg))\<cdot>acks\<cdot>(Discr ack)))"
  by (simp add: delayfun_tslscons tsmlscons_lscons)

lemma tssnd_h_delayfun_bot:
  "msg \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(delayFun\<cdot>\<bottom>)\<cdot>(Discr ack) 
     = tsMLscons\<cdot>(updis (m, ack))\<cdot>(delayFun\<cdot>\<bottom>)"
  by (simp add: tssnd_h_delayfun_nack)

lemma tssnd_h_mlscons_ack: "msg \<noteq> \<bottom> \<Longrightarrow> acks \<noteq> \<bottom> \<Longrightarrow>
   tsSnd_h\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>acks)\<cdot>(Discr a) 
     = tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>a))"
  by (simp add: tsmlscons_lscons)

lemma tssnd_h_mlscons_nack: "msg \<noteq> \<bottom> \<Longrightarrow> acks \<noteq> \<bottom> \<Longrightarrow> a \<noteq> ack \<Longrightarrow>
   tsSnd_h\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>acks)\<cdot>(Discr ack) 
     = (tsSnd_h\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>acks\<cdot>(Discr ack))"
  by (simp add: tsmlscons_lscons)

lemma tssnd_h_delayfun:
  "tsSnd_h\<cdot>(delayFun\<cdot>msg)\<cdot>(delayFun\<cdot>acks)\<cdot>ack = delayFun\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>ack)"
  by (simp add: delayfun_tslscons)
    
lemma tssnd_h_delayfun_msg:
  "acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(delayFun\<cdot>msg)\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>acks)\<cdot>ack 
                      =(tsSnd_h\<cdot>(delayFun\<cdot>msg)\<cdot>acks\<cdot>ack)"
  by (simp add: delayfun_tslscons tsmlscons_lscons)