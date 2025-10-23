all: hott std
.PHONY: all

hott:
	$(MAKE) -C hott all
	rm -f _CoqProject
	ln -s hott/_CoqProject _CoqProject
.PHONY: hott

install-hott: hott
	$(MAKE) -C hott install
.PHONY: install-hott


std:
	$(MAKE) -C std all
	rm -f _CoqProject
	ln -s std/_CoqProject _CoqProject
.PHONY: std

install-std: std
	$(MAKE) -C std install
.PHONY: install-std


test-std: std
	$(MAKE) COQPROJECTFILE=./_CoqProject.std -C tests all
	ln -s tests/_CoqProject.std tests/_CoqProject
.PHONY: test-std

test-hott: hott
	$(MAKE) COQPROJECTFILE=./_CoqProject.hott -C tests all
	ln -s tests/_CoqProject.hott tests/_CoqProject
.PHONY: test-hott

clean:
	$(MAKE) -C hott clean
	$(MAKE) -C std clean
	$(MAKE) COQPROJECTFILE=./_CoqProject.std  -C tests clean
	$(MAKE) COQPROJECTFILE=./_CoqProject.hott -C tests clean
.PHONY: clean
