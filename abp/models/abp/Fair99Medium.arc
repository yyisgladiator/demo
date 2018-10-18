package abp;

<<nonDeterministic,transRefines="FairMedium">>component Fair99Medium<E> {

  port
    in E i,
    out E o;

  int counter;

  automaton Fair99Medium {
    state Single;
    initial Single / {counter=rand{j. j>=0 && j<100}};

    Single [counter!=0] / {counter=counter-1};
    Single [counter==0] / {counter=rand{j. j>=0 && j<100}, o=i};
  }
}
