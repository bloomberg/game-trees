all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf
	rm -f tictactoe.{ml,mli}

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

run:
	ocaml tictactoe.ml

.PHONY: Makefile.coq all clean
