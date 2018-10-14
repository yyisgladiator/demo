package abp;

/* Medium that is the identity function, i.e. never drops a message */
<<nonDeterministic,refines="Fair99Medium">>component IdMedium<E> {

  port
    in E i,
    out E o;

  automaton IdMedium {
    state Single;
    initial Single;

    Single / {o=i};
  }
}
