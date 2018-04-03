chapter {* Medium of the Alternating Bit Protocol *}
                                                            
theory Medium_imp2
imports "../../TStream"

begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* definition *}
(* ----------------------------------------------------------------------- *)

fixrec tsTakeFirstTick :: "'a tstream \<rightarrow> 'a tstream" where
"tsTakeFirstTick\<cdot>\<bottom> = \<bottom>" |
"tsTakeFirstTick\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = ts" |
"ts \<noteq> \<bottom> \<Longrightarrow> tsTakeFirstTick\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) = tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>(tsTakeFirstTick\<cdot>ts)"

fixrec tsMed :: "'a tstream \<rightarrow> bool stream \<rightarrow> nat stream \<rightarrow> 'a tstream" where
  (* bottom case *)
"tsMed\<cdot>\<bottom>\<cdot>ora\<cdot>del = \<bottom>" |
"tsMed\<cdot>msg\<cdot>\<bottom>\<cdot>del = \<bottom>" |
"tsMed\<cdot>msg\<cdot>ora\<cdot>\<bottom> = \<bottom>" |

"ora \<noteq> \<bottom> \<Longrightarrow> del \<noteq> \<bottom> \<Longrightarrow> tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>ora\<cdot>del
 = delayFun\<cdot>(tsMed\<cdot>msg\<cdot>ora\<cdot>del)" |

"msg \<noteq> \<bottom> \<Longrightarrow>  tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(lscons\<cdot>(up\<cdot>k)\<cdot>ora)\<cdot>(lscons\<cdot>(up\<cdot>d)\<cdot>del)
 = (if (k = Discr False) then tsMed\<cdot>msg\<cdot>ora\<cdot>(lscons\<cdot>(up\<cdot>d)\<cdot>del)
    else (if (d=Discr 0) then tsMLscons\<cdot>(up\<cdot>m)\<cdot>(tsMed\<cdot>msg\<cdot>ora\<cdot>del)
          else delayFun\<cdot>(tsMed\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>(tsTakeFirstTick\<cdot>msg))\<cdot>(lscons\<cdot>(up\<cdot>k)\<cdot>ora)\<cdot>(lscons\<cdot>(up\<cdot>(Discr ((undiscr d)-1)))\<cdot>del))))" 

(* ----------------------------------------------------------------------- *)
section {* basic properties *}
(* ----------------------------------------------------------------------- *)