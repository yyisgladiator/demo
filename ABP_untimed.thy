(*
    Author:       Sebastian Stüber  
    Description:  This is a variant of the "Alternating Bit Protocol" on untimed streams. 
                  Because timing information are not available on untimed streams messages are not 
                  lost on the medium (which would not be detectable by an component) but instead
                  they are damaged. 
*)

theory ABP_untimed (* ABP = Alternating Bit Protocol *)
imports SPF


begin
  default_sort type


(* Das sind die datentypen die übertragen werden. 
  M besteht aus diese Typen + dem Tupel (data\<times>bit) *)
datatype data = D nat
datatype bit = Zero | One | Error
  (* Error is used to describe corruption of a message. *)


(* needs to be instanciated to countables in order to use with streams *)
instantiation data::countable 
begin
  instance
  apply(intro_classes)
  by(countable_datatype)
end

(* similar to \<not> on Booleans. Doesn't change the "Error" case *)
primrec invBit :: "bit \<Rightarrow> bit" ("\<not> _") where
"invBit One   = Zero" |
"invBit Zero  = One"  |
"invBit Error = Error"

instantiation bit::countable 
begin
  instance
  apply(intro_classes)
  by(countable_datatype)
end


(* StBundles are defined with "M stream". these are converters from the "subtypes" of M to M and back *)
  (* and they are phantoms, because M is not yet defined with data/bit*)
definition m2d :: "M stream \<rightarrow> data stream" where
"m2d \<equiv> \<Lambda> s. \<epsilon>"
definition d2m :: "data stream \<rightarrow> M stream" where
"d2m \<equiv> \<Lambda> s. \<epsilon>"

definition m2b :: "M stream \<rightarrow> bit stream" where
"m2b \<equiv> \<Lambda> s. \<epsilon>"
definition b2m :: "bit stream \<rightarrow> M stream" where
"b2m \<equiv> \<Lambda> s. \<epsilon>"

definition m2db :: "M stream \<rightarrow> (data\<times>bit) stream" where
"m2db \<equiv> \<Lambda> s. \<epsilon>"
definition db2m :: "(data\<times>bit) stream \<rightarrow> M stream" where
"db2m \<equiv> \<Lambda> s. \<epsilon>"


(* this function describes the "Send" part of the Alternating Bit Protocol *)

  (* the 1. Input is the data-strem which should be transmitted *)
  (* the 2. Input is the returning bit-stream from the Receiver *)
  (* the 3. Input is the previous Message (prevM), in case this Message needs to be resend *)
definition send :: "('a::countable) stream \<Rightarrow> bit stream \<Rightarrow> ('a\<times>bit) \<Rightarrow> ('a\<times>bit) stream" where
"send \<equiv> \<mu> f. (\<lambda> data bit (prevData, prevBit) .
  if (data = \<epsilon> \<or> bit = \<epsilon>) then \<epsilon> else

      let newM = (shd data, \<not>prevBit) in 
          if  (prevBit = shd bit) then (* Previous Messages correctly send *)
              \<up>newM  \<bullet> (f (srt\<cdot>data) (srt\<cdot>bit) newM )
          else  (* error sending previous message, resend the message *)
              \<up>(prevData, prevBit) \<bullet> (f data (srt\<cdot>bit) (prevData, prevBit)))"


(* I added \<up>One and (undefined, One) to correctly handle the beginning *)
definition send_helper:: "StBundle \<rightarrow> StBundle" where
"send_helper \<equiv> \<Lambda> b. ([c3 \<mapsto> db2m\<cdot>(send (m2d\<cdot>(b . c1)) (\<up>One \<bullet> m2b\<cdot>(b . c2)) (undefined, One))]\<Omega>)"


(* Send-Component *)
  (* c1  \<rightarrow> Input,  Data *)
  (* c2  \<rightarrow> Input,  Bit  *)
  (* c3  \<rightarrow> Output, Data\<times>Bit  *)
definition Send :: SPF where
"Send \<equiv> spfSbLift send_helper {c1,c2} {c3}"



(* Medium(D,Bit) *)
  (* c3 \<rightarrow> Input,  Data\<times>Bit *)
  (* c4 \<rightarrow> Output, Data\<times>Bit *)

(* Defined below as SPS 
definition Med1 :: SPF where
"Med1 \<equiv> spfSbLift (\<Lambda> b. [c4 \<mapsto> (b . c3)]\<Omega>) {c3} {c4}"

*)

definition recv_helper :: "StBundle \<rightarrow> StBundle" where
"recv_helper \<equiv> \<Lambda> b. 
    let input = m2db\<cdot>(b. c4); (* input as (data\<times>bit) stream *)
        inputOhneError = sfilter {t |t.(snd t\<noteq>Error)}\<cdot>input  (* input without 'Error' bits *)  in
  [c5 \<mapsto> d2m\<cdot>(sprojfst\<cdot>(srcdups\<cdot>inputOhneError)), c6 \<mapsto> b2m\<cdot>(sprojsnd\<cdot>input)]\<Omega>"


(* c4 \<rightarrow> Input, Data\<times>Bit *)
(* c5 \<rightarrow> Output Data Stream *)
(* c6 \<rightarrow> Output Control Bit Stream *)
definition Recv :: SPF where
"Recv \<equiv> spfSbLift recv_helper {c4} {c5,c6}"



(* c6 \<rightarrow> Input, Bit Stream *)
(* c8 \<rightarrow> Input Oracle which Bit is corrupted *) (* ! ! ! *) (* is hidden in SPS definition *)
(* c2 \<rightarrow> Output, transmitted Bits *)

(* Das ist eine Demonstration wie ich die Mediums - SPF's definieren würde *)
(* ansonsten kann man das analog zu Med1 machen *)
definition Med2  :: SPF where
"Med2 \<equiv> Abs_SPF (\<Lambda> b. 
      let gezipt = szip\<cdot>(m2b\<cdot>(b . c6))\<cdot> (Bool_st_inv\<cdot>(b. c8));
            (* führt die 2 ströme zusammen zu einem (bit\<times>bool) strom *)
          false2error = (\<lambda>(bit, bool). if bool then bit else Error) in
            (* wenn das oracle 'False' ist wird das bit nicht übertragen \<Rightarrow> auf 'Error' gesetzt *)
    (sbDom\<cdot>b={c6,c8}) \<leadsto> ([c2 \<mapsto> b2m\<cdot>(smap false2error\<cdot>gezipt)]\<Omega>))"






setup_lifting type_definition_SPS


(* Send hat kein Oracel, ist also deterministisch *)
lift_definition SEND :: SPS is "{Send}"
by(simp add: sps_wellformed_def)


lift_definition RECV :: SPS is "{Recv}"
by(simp add: sps_wellformed_def)

  (* corrupts data if the oracle is "False" *)
  definition outswichtError:: "(data\<times>bit) stream \<rightarrow> bool stream \<rightarrow> (data\<times>bit) stream" where
  "outswichtError \<equiv> \<mu> f. \<Lambda> data oracle . let rest = f\<cdot>(srt\<cdot>data)\<cdot>(srt\<cdot>oracle) in
                              if (data=\<epsilon> \<or> oracle=\<epsilon>) then \<epsilon> else
                                    if (shd oracle) then \<up>(shd data) \<bullet> rest 
                                    else \<up>(undefined, Error) \<bullet> rest"

(* Definition of Medium using outswitch *)
lift_definition MED1 :: SPS is
"{ Abs_SPF( \<Lambda> b.((sbDom\<cdot>b = {c3}) \<leadsto> ([c4 \<mapsto> db2m\<cdot>(outswichtError\<cdot>(m2db\<cdot>(b . c3))\<cdot>oracle)]\<Omega>))) |  
      oracle . (sdom\<cdot>oracle \<subseteq> {True, False}) }"
apply(simp add: sps_wellformed_def)
sorry


  (* *)
  definition replaceChannel:: "SPF \<Rightarrow> channel \<Rightarrow> M stream \<Rightarrow> SPF" where
  "replaceChannel F c s = Abs_SPF (\<Lambda> b. (Rep_SPF F)\<cdot>(sbSetCh b c s))"

lift_definition MED2 :: SPS is
"{ replaceChannel Med2 c8 (Bool_st\<cdot>oracle) | oracle . (sdom\<cdot>oracle \<subseteq> {True, False}) }"
sorry




end
