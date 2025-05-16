all: hott std
.PHONY: all

hott:
	$(MAKE) -C hott all
.PHONY: hott

std:
	$(MAKE) -C std all
.PHONY: std

clean:
	$(MAKE) -C hott clean
	$(MAKE) -C std clean
.PHONY: clean
