LIB_MODS    := Tactics Nonterm Esets Emaps

MODS        := Tactics ListUtil Maps Machine Pointer AndersenModel AndersenSound AndersenIter Andersen \
	$(LIB_MODS:%=lib/%)
COQ_SOURCES := $(MODS:%=%.v)

GLOBALS     := .coq_globals

include Makefile.coq

Makefile.coq: Makefile $(COQ_SOURCES)
	coq_makefile $(COQ_SOURCES) \
		COQC = "coqc -dump-glob $(GLOBALS)" \
		>Makefile.coq

.PHONY: doc publish

doc:
	-mkdir doc
	coqdoc -d doc -g --glob-from .coq_globals $(COQ_SOURCES)

Andersen.ml: Andersen.vo
	coqc AndersenExtract >Andersen.ml

publish:
	cp Makefile *.v *.ml ../html/coq/src/
	cp doc/*.html ../html/coq/

