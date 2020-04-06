all: Makefile.coq
	$(MAKE) -f Makefile.coq

tactics: Makefile.tactics.coq
	$(MAKE) -f Makefile.tactics.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

install-tactics: Makefile.tactics.coq
	$(MAKE) -f Makefile.tactics.coq install

uninstall: Makefile.coq
	$(MAKE) -f Makefile.coq uninstall

uninstall-tactics: Makefile.tactics.coq
	$(MAKE) -f Makefile.tactics.coq uninstall

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.tactics.coq: _CoqProject.tactics
	coq_makefile -f _CoqProject.tactics -o Makefile.tactics.coq

clean: Makefile.coq Makefile.tactics.coq
	-$(MAKE) -f Makefile.coq cleanall
	-rm -f Makefile.coq
	-$(MAKE) -f Makefile.tactics.coq cleanall
	-rm -f Makefile.tactics.coq

.PHONY: all install clean tactics install-tactics uninstall uninstall-tactics
