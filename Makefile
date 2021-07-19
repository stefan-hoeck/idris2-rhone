export IDRIS2 ?= idris2

lib_pkg = rhone.ipkg

.PHONY: all lib install install-with-src clean clean-install clean-install-with-src repl develop

all: lib

clean-install: clean install

clean-install-with-src: clean install

lib:
	${IDRIS2} --build ${lib_pkg}

install:
	${IDRIS2} --install ${lib_pkg}

install-with-src:
	${IDRIS2} --install-with-src ${lib_pkg}

clean:
	${IDRIS2} --clean ${lib_pkg}
	${IDRIS2} --clean ${docs_pkg}
	${RM} -r build

# Start a REPL in rlwrap
repl:
	rlwrap -pGreen ${IDRIS2} --find-ipkg src/Data/SOP.idr

develop:
	find -name "*.idr" | entr -d idris2 --typecheck ${lib_pkg}
