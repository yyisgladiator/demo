chapter {* Medium of the Alternating Bit Protocol *}
                                                            
theory Medium_imp1
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

fixrec tsMed :: "'a tstream \<rightarrow> lnat stream \<rightarrow> 'a tstream" where
  (* bottom case *)
"tsMed\<cdot>\<bottom>\<cdot>ora = \<bottom>" |
"tsMed\<cdot>msg\<cdot>\<bottom> = \<bottom>" |

"tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>ora
 = delayFun\<cdot>(tsMed\<cdot>msg\<cdot>ora)" |

"msg \<noteq> \<bottom> \<Longrightarrow>  tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(lscons\<cdot>(up\<cdot>(\<infinity>))\<cdot>ora)
 = tsMed\<cdot>msg\<cdot>ora" |

"msg \<noteq> \<bottom> \<Longrightarrow>  tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(lscons\<cdot>(up\<cdot>(Fin k))\<cdot>ora)
 = (if (k=0) then tsMLscons\<cdot>(up\<cdot>m)\<cdot>(tsMed\<cdot>msg\<cdot>ora)
   else delayFun\<cdot>(tsMed\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>(tsTakeFirstTick\<cdot>msg))\<cdot>(lscons\<cdot>(up\<cdot>(Fin (k-1)))\<cdot>ora)))" 

(* ----------------------------------------------------------------------- *)
section {* basic properties *}
(* ----------------------------------------------------------------------- *)