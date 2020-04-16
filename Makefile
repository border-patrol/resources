# ----------------------------------------------------------------- [ Makefile ]
# Module    : Makefile
# Copyright : (c) Jan de Muijnck-Hughes
# License   : see LICENSE
# ---------------------------------------------------------------------- [ EOH ]

IDRIS := idris
LIB   := resources
OPTS  :=

.PHONY: doc cthulhu check clean build

usuage:
	@echo "Targets are:"
	@echo ""
	@echo "Build Targets"
	@echo "\t make check   -- type check only"
	@echo "\t make build   -- build package"
	@echo ""
	@echo "Clean Targets"
	@echo "\t make clean   -- build idris doc"
	@echo "\t make cthulhu -- build idris doc"
	@echo ""
	@echo ""
	@echo "Documentation"
	@echo "\t make doc       -- build idris doc"
	@echo "\t make highlight -- generate highlight files for idrishl"

build:
	${IDRIS} ${OPTS} --build ${LIB}.ipkg

highlight: cthulhu
	${IDRIS} ${OPTS} --checkpkg ${LIB}.ipkg --highlight

clean:
	${IDRIS} --clean ${LIB}.ipkg
	find . -name "*~" -delete

cthulhu: clean
	find .   \( -name "*.idh"   \
		 -or -name "*.html" \
		 -or -name "*.tex"  \
		 -or -name "*.ibc"  \
		 \)                 \
		 -delete

doc:
	${IDRIS} --mkdoc ${LIB}.ipkg

# ---------------------------------------------------------------------- [ EOF ]
