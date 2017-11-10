(*  Title:        PFun
    Author:       Stüber, Jens, Marc
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Defines "Processing functions" 
*)

theory PFun
  imports UnivClasses


begin


default_sort usb

(* SWS: This is different from the original spf_well *)
(* But hopefully identical, better ... *)
definition uspfWell:: "('in \<rightarrow> 'out option) \<Rightarrow> bool" where
"uspfWell f \<equiv> (\<exists>In. \<forall>b. (b \<in> dom (Rep_cfun f) \<longleftrightarrow> usbDom\<cdot>b = In)) \<and> 
              (\<exists>Out. \<forall>b. (b \<in> ran (Rep_cfun f) \<longrightarrow> usbDom\<cdot>b = Out))"

(* Define the type 'm USPF (Very Universal Stream Processing Functions) as cpo *)
cpodef ('in,'out) pfun = "{f :: 'in \<rightarrow> 'out option . uspfWell f}"
  sorry

type_synonym 'm uSPF = "('m, 'm) pfun"

definition uspfDom :: "('in,'out) pfun \<rightarrow> channel set" where
"uspfDom \<equiv> \<Lambda> f. usbDom\<cdot>(SOME b. b \<in> dom (Rep_cfun (Rep_pfun f)))" 

definition uspfRan :: "('in,'out) pfun \<rightarrow> channel set" where
"uspfRan \<equiv> \<Lambda> f. usbDom\<cdot>(SOME b. b \<in> ran (Rep_cfun (Rep_pfun f)))" 

definition uspfLeast :: "channel set \<Rightarrow> channel set \<Rightarrow> ('in,'out) pfun" where
"uspfLeast cin cout = Abs_pfun (\<Lambda>  sb.  (usbDom\<cdot>sb = cin) \<leadsto> usbLeast cout)"


(* We can reuse this composition in the subtypes, for weak/strong causal stuff *)
definition uspfComp :: "'m uSPF \<rightarrow> 'm uSPF \<rightarrow> 'm uSPF" where
"uspfComp = undefined"



subsection \<open>Causal Subtype\<close>

(* return true iff tickcount holds *)
definition uspfIsWeak :: "('in,'out) pfun \<Rightarrow> bool" where
"uspfIsWeak f = (\<forall>b. (b \<in> dom (Rep_cfun (Rep_pfun f)) \<longrightarrow> usbLen b \<le> usbLen (the ((Rep_pfun f)\<cdot>b))))"

cpodef ('in,'out)  USPFw = "{f ::  ('in,'out) pfun. uspfIsWeak f}"
sorry

definition uspfIsStrong :: "('in,'out) pfun \<Rightarrow> bool" where
"uspfIsStrong f = (\<forall>b. (b \<in> dom (Rep_cfun (Rep_pfun f)) \<longrightarrow> lnsuc\<cdot>(usbLen b) \<le> usbLen (the ((Rep_pfun f)\<cdot>b))))"

cpodef ('in,'out) USPFs = "{f :: ('in,'out) pfun. uspfIsStrong f}"
sorry



end