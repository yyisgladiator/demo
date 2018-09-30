theory Channel
  imports HOLCF

begin

default_sort type
text {*This is the total set of channels. While representing an existing network of components or creating a new one, 
 one should add here all channels that occur in the whole network.*}

datatype channel = c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | \<C> string
             (* for ABP Specification*) | c_as | c_ds | c_ar | c_dr | c_abpIn | c_abpOut | c_idOut


end
