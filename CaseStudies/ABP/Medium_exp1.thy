chapter {* Medium of the Alternating Bit Protocol *}
                                                            
theory Medium_exp1
imports "../../TStream"

begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* definition *}
(* ----------------------------------------------------------------------- *)

fixrec tsMed :: "'a tstream \<rightarrow> lnat stream \<rightarrow> 'a stream \<rightarrow> 'a tstream" where
  (* bottom case *)
"tsMed\<cdot>\<bottom>\<cdot>ora\<cdot>buf = \<bottom>" |
"tsMed\<cdot>msg\<cdot>\<bottom>\<cdot>buf = \<bottom>" |

"msg \<noteq> \<bottom> \<Longrightarrow>  tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>ora\<cdot>buf 
 = (tsMed\<cdot>msg\<cdot>ora\<cdot>(buf \<bullet> ((up\<cdot>m)&&\<epsilon>)))" |

"tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>ora\<cdot>\<epsilon>
 = delayFun\<cdot>(tsMed\<cdot>msg\<cdot>ora\<cdot>\<epsilon>)" |

"tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(lscons\<cdot>(up\<cdot>(\<infinity>))\<cdot>ora)\<cdot>(lscons\<cdot>(up\<cdot>b)\<cdot>buf)
 = tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>ora\<cdot>buf" |

"tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(lscons\<cdot>(up\<cdot>(Fin k))\<cdot>ora)\<cdot>(lscons\<cdot>(up\<cdot>b)\<cdot>buf)
 = (if (k=0) then tsMLscons\<cdot>(up\<cdot>b)\<cdot>(tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>ora\<cdot>buf)
   else (tsMed\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(lscons\<cdot>(up\<cdot>(Fin (k-1)))\<cdot>ora)\<cdot>(lscons\<cdot>(up\<cdot>b)\<cdot>buf)))"

(* ----------------------------------------------------------------------- *)
section {* basic properties *}
(* ----------------------------------------------------------------------- *)

end