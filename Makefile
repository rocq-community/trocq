all: hott std
.PHONY: all

hott:
	$(MAKE) -C hott all
	rm -f _CoqProject
	ln -s hott/_CoqProject _CoqProject
.PHONY: hott

std:
	$(MAKE) -C std all
	rm -f _CoqProject
	ln -s std/_CoqProject _CoqProject
.PHONY: std

test-std: std
	$(MAKE) COQPROJECTFILE=./_CoqProject.std -C tests all
.PHONY: test-std

install-test-std: test-std
	$(MAKE) COQPROJECTFILE=./_CoqProject.std -C tests install
.PHONY: install-test-std

test-hott: hott
	$(MAKE) COQPROJECTFILE=./_CoqProject.hott -C tests all
.PHONY: test-hott

install-test-hott: test-hott
	$(MAKE) COQPROJECTFILE=./_CoqProject.hott -C tests install
.PHONY: install-test-std

clean:
	$(MAKE) -C hott clean
	$(MAKE) -C std clean
	$(MAKE) COQPROJECTFILE=./_CoqProject.std  -C tests clean
	$(MAKE) COQPROJECTFILE=./_CoqProject.hott -C tests clean
.PHONY: clean
