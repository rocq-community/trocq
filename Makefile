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
	rm -f tests/_CoqProject
	ln -s _CoqProject.std tests/_CoqProject
	$(MAKE) -C tests all
.PHONY: test-std

test-hott: hott
	rm -f tests/_CoqProject
	ln -s _CoqProject.hott tests/_CoqProject
	$(MAKE) -C tests all
.PHONY: test-hott

clean:
	$(MAKE) -C hott clean
	$(MAKE) -C std clean
	$(MAKE) -C tests clean
.PHONY: clean
