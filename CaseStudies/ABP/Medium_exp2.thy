chapter {* Medium of the Alternating Bit Protocol *}
                                                            
theory Medium_exp2
imports "../../TStream"

begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* definition *}
(* ----------------------------------------------------------------------- *)

fixrec tsMed :: "'a tstream \<rightarrow> bool stream \<rightarrow> nat stream \<rightarrow> 'a stream \<rightarrow> 'a tstream" where
  (* bottom case *)
"tsMed\<cdot>\<bottom>\<cdot>ora\<cdot>del\<cdot>buf = \<bottom>" |
"tsMed\<cdot>msg\<cdot>\<bottom>\<cdot>del\<cdot>buf = \<bottom>" |
"tsMed\<cdot>msg\<cdot>ora\<cdot>\<bottom>\<cdot>buf = \<bottom>" |

"msg \<noteq> \<bottom> \<Longrightarrow> tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>ora\<cdot>del\<cdot>buf 
 = (tsMed\<cdot>msg\<cdot>ora\<cdot>del\<cdot>(buf \<bullet> ((up\<cdot>m)&&\<epsilon>)))" |

"ora \<noteq> \<bottom> \<Longrightarrow> del \<noteq> \<bottom> \<Longrightarrow> tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>ora\<cdot>del\<cdot>\<epsilon>
 = delayFun\<cdot>(tsMed\<cdot>msg\<cdot>ora\<cdot>del\<cdot>\<epsilon>)" |

"tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(lscons\<cdot>(up\<cdot>or)\<cdot>ora)\<cdot>(lscons\<cdot>(up\<cdot>d)\<cdot>del)\<cdot>(lscons\<cdot>(up\<cdot>b)\<cdot>buf)
 = (if (or =Discr False) then tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>ora\<cdot>(lscons\<cdot>(up\<cdot>d)\<cdot>del)\<cdot>buf
    else (if (d=Discr 0) then tsMLscons\<cdot>(up\<cdot>b)\<cdot>(tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>ora\<cdot>del\<cdot>buf)
          else (tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(lscons\<cdot>(up\<cdot>or)\<cdot>ora)\<cdot>(lscons\<cdot>(up\<cdot>(Discr ((undiscr d)-1)))\<cdot>del)\<cdot>(lscons\<cdot>(up\<cdot>b)\<cdot>buf))))" 

(* ----------------------------------------------------------------------- *)
section {* basic properties *}
(* ----------------------------------------------------------------------- *)

end