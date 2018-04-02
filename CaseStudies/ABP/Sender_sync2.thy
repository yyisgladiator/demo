chapter {* Alternating Bit Protocol *}       
                                                            
theory Sender_sync2
imports "../../TStream"
begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* definition of the set of sender *}
(* ----------------------------------------------------------------------- *)

fixrec tsSnd_h :: "'a tstream \<rightarrow> bool tstream \<rightarrow> 'a stream \<rightarrow> bool discr \<rightarrow> ('a \<times> bool) tstream" where
  (* bottom case *)
"tsSnd_h\<cdot>\<bottom>\<cdot>acks\<cdot>buf\<cdot>ack = \<bottom>" |
"tsSnd_h\<cdot>msg\<cdot>\<bottom>\<cdot>buf\<cdot>ack = \<bottom>" |

"msg \<noteq> \<bottom> \<Longrightarrow>  tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>acks\<cdot>buf\<cdot>ack = 
   (tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(buf \<bullet> ((up\<cdot>m)&&\<epsilon>))\<cdot>ack)" |

"tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>\<epsilon>\<cdot>ack
   = delayFun\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>\<epsilon>\<cdot>ack)" |

"buf \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>(lscons\<cdot>(up\<cdot>b)\<cdot>buf)\<cdot>ack
   =  tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>b)\<cdot>(up\<cdot>ack))\<cdot>(delayFun\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(lscons\<cdot>(up\<cdot>b)\<cdot>buf)\<cdot>ack))" |

"acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>\<epsilon>\<cdot>ack
  = (tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>acks\<cdot>\<epsilon>\<cdot>ack)" |

"acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>(lscons\<cdot>(up\<cdot>b)\<cdot>buf)\<cdot>ack
  = (if (a = ack) then tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>acks\<cdot>buf\<cdot>(Discr (\<not>(undiscr ack)))
   else (tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>acks\<cdot>(lscons\<cdot>(up\<cdot>b)\<cdot>buf)\<cdot>ack))" 

definition tsSnd :: "'a tstream \<rightarrow> bool tstream \<rightarrow> ('a \<times> bool) tstream" where
"tsSnd \<equiv> \<Lambda> msg acks. delay (tsSnd_h\<cdot>msg\<cdot>acks\<cdot>\<epsilon>\<cdot>(Discr True))"  

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