session "uClasses" (mustWork) = "HOLCF" +
  options [quick_and_dirty = false]
  theories
    UnivClasses

session "ubundle" (mustWork) = "uClasses" +
  options [quick_and_dirty = false]
  theories
    UBundle
    UBundle_Conc
    UBundle_Pcpo

session "ufun" (mustWork) = "uClasses" +
  options [quick_and_dirty = true]
  theories
    UFun
    UFun_applyIn
    UFun_Comp

session "uspec" (mustWork) = "uClasses" +
  options [quick_and_dirty = true]
  theories
    USpec
    USpec_Comp


session "sb" (mustWork) = "ubundle" +
  options [quick_and_dirty = true]
  theories
    "untimed/SB"

session "spf" (mustWork) = "sb" +
  options [quick_and_dirty = true]
  theories
    "untimed/SPF"

session "sps" (mustWork) = "spf" +
  options [quick_and_dirty = true]
  theories
    "untimed/SPS"

session "automaton" (mustWork) = "spf" +
  options [quick_and_dirty = true]
  theories
    "untimed/CaseStudy/Automaton"

session "NDA" (mustWork) = "sps" +
  options [quick_and_dirty = true]
  theories
    "untimed/CaseStudy/NDA"


session "Streams" (mustWork) = "HOLCF" +
  options [quick_and_dirty = false]
  theories
    "untimed/Streams"
	
session "tsynStream" (mustWork) = "Streams" + 
  options [quick_and_dirty = true]
  theories
    "timesyn/tsynStream"
	"timesyn/tsynBundle"

session "ABP" (mustWork) = "tsynStream" +
  options [quick_and_dirty = true]
  theories
    "timesyn/CaseStudies/ABP/Components"
	

session "ubundle_opt" (canFail) = "uClasses" +
  options [quick_and_dirty = false]
  theories
    UBundle

session "ufun_opt" (canFail) = "uClasses" +
  options [quick_and_dirty = false]
  theories
    UFun

session "uspec_opt" (canFail) = "uClasses" +
  options [quick_and_dirty = false]
  theories
    USpec
