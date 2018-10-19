package abp;

component Sender<E> {

  port
    in boolean as,
    in E i,
    out Pair<E,boolean> ds;

  List<E> buffer;
  int c;

  automaton Sender {
    state Sf, St;
    initial St / {c=0, buffer=new List<>()};

    St -> St [buffer.size()=0 && as!=null && i==null];
    St -> Sf [buffer.size()>1 && as==true && i==null]          / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),false)};
    St -> St [buffer.size()=0 && as==null && i==null];
    St -> St [buffer.size()>0 && c>0 && as==false && i==null]  / {c=c-1};
    St -> St [buffer.size()>0 && c>0 && as==null && i==null]   / {c=c-1};
    St -> St [buffer.size()>0 && c=0 && as==false && i==null]  / {c=3, ds=new Pair<>(buffer.last(),true)};
    St -> St [buffer.size()>0 && c=0 && as==null && i==null]   / {c=3, ds=new Pair<>(buffer.last(),true)};
    St -> Sf [buffer.size()=1 && as==true && i==null]          / {buffer=buffer.butlast()};
    St -> St [buffer.size()=0 && as!=null && i!=null]          / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)};
    St -> St [buffer.size()=0 && i!=null && as==null]          / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)};
    St -> Sf [buffer.size()>1 && i!=null && as==true]          / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),false)};
    St -> St [buffer.size()>0 && c>0 && i!=null && as==false]  / {buffer=buffer.prepend(i), c=c-1};
    St -> St [buffer.size()>0 && c>0 && i!=null && as==null]   / {buffer=buffer.prepend(i), c=c-1};
    St -> St [buffer.size()>0 && c=0 && i!=null && as==false]  / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)};
    St -> St [buffer.size()>0 && c=0 && i!=null && as==null]   / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)};
    St -> Sf [buffer.size()=1 && i!=null && as==true]          / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,false)};
    Sf -> St [buffer.size()>1 && i!=null && as==false]         / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),true)};
    Sf -> St [buffer.size()>1 && as==false && i==null]         / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),true)};
    Sf -> St [buffer.size()=1 && i!=null && as==false]         / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,true)};
    Sf -> St [buffer.size()=1 && as==false && i==null]         / {buffer=buffer.butlast()};
    Sf -> Sf [buffer.size()=0 && as==null && i==null];
    Sf -> Sf [buffer.size()=0 && as!=null && i==null];
    Sf -> Sf [buffer.size()>0 && c>0 && as==null && i==null];
    Sf -> Sf [buffer.size()>0 && c>0 && as==true && i==null]   / {c=c-1};
    Sf -> Sf [buffer.size()>0 && c=0 && as==true && i==null]   / {c=3, ds=new Pair<>(buffer.last(),false)};
    Sf -> Sf [buffer.size()>0 && c=0 && as==null && i==null]   / {c=3, ds=new Pair<>(buffer.last(),false)};
    Sf -> Sf [buffer.size()=0 && as!=null && i!=null]          / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)};
    Sf -> Sf [buffer.size()=0 && i!=null && as==null]          / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)};
    Sf -> Sf [buffer.size()>0 && c>0 && i!=null && as==true]   / {buffer=buffer.prepend(i), c=c-1};
    Sf -> Sf [buffer.size()>0 && c>0 && i!=null && as==null]   / {buffer=buffer.prepend(i), c=c-1};
    Sf -> Sf [buffer.size()>0 && c=0 && i!=null && as==true]   / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)};
    Sf -> Sf [buffer.size()>0 && c=0 && i!=null && as==null]   / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)};
  }
}
