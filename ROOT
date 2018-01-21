session "uClasses" (mustWork) = "HOLCF" +
  options [quick_and_dirty = false]
  theories
    UnivClasses

session "ubundle" (mustWork) = "uClasses" +
  options [quick_and_dirty = false]
  theories
    UBundle
    UBundle_Conc

session "ufun" (mustWork) = "uClasses" +
  options [quick_and_dirty = false]
  theories
    UFun
    UFun_applyIn
    UFun_Comp

session "uspec" (mustWork) = "uClasses" +
  options [quick_and_dirty = false]
  theories
    USpec


session "sb" (mustWork) = "ubundle" +
  options [quick_and_dirty = false]
  theories
    "untimed/SB"

session "spf" (mustWork) = "sb" + 
  options [quick_and_dirty = false]
  theories
    "untimed/SPF"
    "untimed/SpfStep"

session "automaton" (mustWork) = "spf" + 
  options [quick_and_dirty = true]
  theories
    "untimed/CaseStudy/Automaton"
