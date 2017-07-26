session "Streams" (mustWork) = "HOLCF" +
  options [quick_and_dirty = false]
  theories
    Streams

session "TStream" (mustWork) = "Streams" + 
  options [quick_and_dirty = false]
  theories
    TStream
 
session "ABP" (mustWork) = "TStream" + 
  options [quick_and_dirty = true]
  theories
    CaseStudies/ABP/Composition
    CaseStudies/ABP/Sender
    CaseStudies/ABP/Testing        
 
 
session "ABP" (canFail) = "TStream" + 
  options [quick_and_dirty = false]
  theories
    CaseStudies/ABP/Composition
    CaseStudies/ABP/Sender
    CaseStudies/ABP/Testing        

