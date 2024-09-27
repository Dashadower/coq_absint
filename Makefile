COQMODULE    := AbsInt
COQTHEORIES  := \
	theories/*.v \

all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	@rm -f _CoqProject Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	(echo "-Q theories $(COQMODULE)"; \
	echo $(COQTHEORIES)) > _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force