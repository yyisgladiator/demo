session "uClasses" (mustWork) = "HOLCF" +
  options [quick_and_dirty = false]
  theories
    UnivClasses

session "ubundle" (mustWork) = "uClasses" +
  options [quick_and_dirty = true]
  theories
    UBundle
    UBundle_Conc

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


session "sb" (mustWork) = "ubundle" +
  options [quick_and_dirty = true]
  theories
    "untimed/SB"

session "spf" (mustWork) = "sb" +
  options [quick_and_dirty = true]
  theories
    "untimed/SPF"



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
