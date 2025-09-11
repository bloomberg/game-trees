all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf
	rm -f tictactoe.{ml,mli}
	rm -f sat.{ml,mli}

Makefile.coq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq

ttt:
	ocaml tictactoe.ml
sat:
	ocaml sat.ml

.PHONY: Makefile.coq all clean
