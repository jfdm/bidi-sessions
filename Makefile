 # -- [ Makefile ]
#
# Makefile for the project.
#
# -- [ EOH ]

PROJECT=sessions
IDRIS2=idris2
KATLA=katla
BASH=bash

BUILDDIR  = ${CURDIR}/build
TARGETDIR = ${BUILDDIR}/exec

SOURCES = $(shell find src -iname "*.idr")

# [ Core Project Definition ]

.PHONY: ${PROJECT} ${PROJECT}-doc ${PROJECT}-srcs

$(PROJECT): $(strip $(SOURCES))
	$(IDRIS2) --build ${PROJECT}.ipkg

$(PROJECT)-doc:
	$(IDRIS2) --mkdoc ${PROJECT}.ipkg

$(PROJECT)-srcs: $(PROJECT)
	$(BASH) annotate.sh

# [ Artefact ]

# .PHONY: ${PROJECT}-vm artefact
#
# $(PROJECT)-vm:
#	${MAKE} -C artefact artefact
#
# artefact: archive $(PROJECT) $(PROJECT)-doc $(PROJECT)-srcs $(PROJECT)-vm
#
#	mkdir -p artefact-staging
#
#	cp $(PROJECT).tar.gz artefact-staging/$(PROJECT).tar.gz
#
#	tar -zcvf artefact-staging/$(PROJECT)_doc.tar.gz -C ${BUILDDIR} docs
#
#	tar -zcvf artefact-staging/$(PROJECT)_html.tar.gz -C ${BUILDDIR} html
#
#	cp artefact/output/$(PROJECT).box artefact-staging/
#	cp artefact/README.md artefact-staging/

# -- [ Housekeeping ]

 .PHONY: archive

 archive:
	git archive \
	  --prefix=${PROJECT}/ \
	  --format=tar.gz \
	  HEAD \
	  > $(PROJECT).tar.gz

.PHONY: clobber clean

clean:
	$(IDRIS2) --clean ${PROJECT}.ipkg

clobber: clean
	$(IDRIS2) --clean ${PROJECT}.ipkg
	find . -iname "*~" -delete
#	${RM} -rf build/ artefact-staging/
#	${RM} ${PROJECT}.tar.gz

# -- [ EOF ]
