all: template-coq checker pcuic safechecker erasure examples

.PHONY: all template-coq checker pcuic erasure install html clean mrproper .merlin test-suite translations

install: all
	$(MAKE) -C template-coq install
	$(MAKE) -C checker install
	$(MAKE) -C pcuic install

html: all
	"coqdoc" -toc -utf8 -interpolate -l -html \
		-R template-coq/theories MetaCoq.Template \
		-R checker/theories MetaCoq.Checker \
		-R pcuic/theories MetaCoq.PCUIC \
		-d html */theories/*.v translations/*.v

clean:
	$(MAKE) -C template-coq clean
	$(MAKE) -C checker clean
	$(MAKE) -C pcuic clean

mrproper:
	$(MAKE) -C template-coq mrproper
	$(MAKE) -C pcuic mrproper

.merlin:
	$(MAKE) -C template-coq .merlin
	$(MAKE) -C pcuic .merlin

template-coq:
	$(MAKE) -C template-coq

pcuic: template-coq
	$(MAKE) -C pcuic

checker: template-coq
	$(MAKE) -C checker

cleanplugins:
	$(MAKE) -C template-coq cleanplugin
	$(MAKE) -C pcuic cleanplugin
	$(MAKE) -C checker cleanplugin