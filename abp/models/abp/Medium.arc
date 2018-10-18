package abp;

/* Unfair Medium */
<<nonDeterministic>>component Medium<E> {

  port
    in E i,
    out E o;

  automaton Medium {
    state Single;
    initial Single;

    Single / {o=null};
    Single / {o=i};
  }
}
