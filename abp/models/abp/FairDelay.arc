package abp;

/**
 * Delays messages in a fair way, i.e. not forever.
 */
<<nonDeterministic>>component FairDelay<E> {

  port
    in E i,
    out E o;

  int ctr;
  List<E> buffer;

  automaton FairDelay {
    state Single;
    initial Single / {ctr=rand{j.true}, buffer=new List<>()};

    Single [ctr>0 && i!=null]  / {ctr=ctr-1, buffer=buffer.prepend(i)};
    Single [ctr>0 && i==null]  / {ctr=ctr-1};

    Single [ctr==0 && i!=null && buffer.size()>0] / {ctr=rand{j.true}, o=buffer.last(), buffer=buffer.butlast().prepend(i)};
    Single [ctr==0 && i==null && buffer.size()>0] / {ctr=rand{j.true}, o=buffer.last(), buffer=buffer.butlast()};

    Single [ctr==0 && buffer.size()==0] / {ctr=rand{j.true}, o=i};
  }
}
