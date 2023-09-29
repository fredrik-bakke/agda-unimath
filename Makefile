
CHECKOPTS := --without-K --exact-split --guardedness
everythingOpts := $(CHECKOPTS)
AGDAVERBOSE ?= -v1
# use "$ export AGDAVERBOSE=20" if you want to see all
AGDAFILES := $(shell find src -name temp -prune -o -type f \( -name "*.lagda.md" -not -name "everything.lagda.md" \) -print)
AGDAMDFILES := $(subst src/,docs/,$(AGDAFILES:.lagda.md=.md))
CONTRIBUTORS_FILE := CONTRIBUTORS.toml

AGDAHTMLFLAGS ?= --html --html-highlight=code --html-dir=docs --css=Agda.css --only-scope-checking
AGDA ?= agda $(AGDAVERBOSE)
TIME ?= time

METAFILES := \
  ART.md \
  CITE-THIS-LIBRARY.md \
  CODINGSTYLE.md \
  CONTRIBUTING.md \
  CONTRIBUTORS.md \
  FILE-CONVENTIONS.md \
  DESIGN-PRINCIPLES.md \
  GRANT-ACKNOWLEDGEMENTS.md \
  HOME.md \
  HOWTO-INSTALL.md \
  LICENSE.md \
  MIXFIX-OPERATORS.md \
  MAINTAINERS.md \
  README.md \
  STATEMENT-OF-INCLUSION.md \
  SUMMARY.md \
  TEMPLATE.lagda.md \
  USERS.md \

.PHONY: agdaFiles
agdaFiles:
	@rm -rf $@
	@rm -rf ./src/everything.lagda.md
	@git ls-files src | grep '\.lagda.md$$' > $@
	@sort -o $@ $@
	@wc -l $@
	@echo "$(shell (git ls-files src | grep '.lagda.md$$' | xargs cat) | wc -l) LOC"

.PHONY: ./src/everything.lagda.md
src/everything.lagda.md: agdaFiles
	@echo "\`\`\`agda" > $@ ;\
	echo "{-# OPTIONS $(everythingOpts) #-}" >> $@ ;\
	echo "" >> $@ ;\
	echo "module everything where" >> $@ ;\
	cat agdaFiles \
		| cut -c 5-               \
		| cut -f1 -d'.'           \
		| sed 's/\//\./g'         \
		| awk 'BEGIN { FS = "."; OFS = "."; lastdir = "" } { if ($$1 != lastdir) { print ""; lastdir = $$1 } print "open import " $$0 }' \
		>> $@ ;\
	echo "\`\`\`" >> $@ ;

.PHONY: check
check: ./src/everything.lagda.md
	${TIME} ${AGDA} $?

AGDAMDFILES: $(AGDAMDFILES)

docs/%.md: ./src/%.lagda.md
	@echo "... $@"
	@${AGDA} ${AGDAHTMLFLAGS} $<

agda-html: ./src/everything.lagda.md
	@rm -rf ./docs/
	@mkdir -p ./docs/
	@${AGDA} ${AGDAHTMLFLAGS} ./src/everything.lagda.md

SUMMARY.md: ${AGDAFILES} ./scripts/generate_main_index_file.py
	@python3 ./scripts/generate_main_index_file.py

MAINTAINERS.md: ${CONTRIBUTORS_FILE} ./scripts/generate_maintainers.py
	@python3 ./scripts/generate_maintainers.py

CONTRIBUTORS.md: ${AGDAFILES} ${CONTRIBUTORS_FILE} ./scripts/generate_contributors.py
	@python3 ./scripts/generate_contributors.py

website/css/Agda-highlight.css: ./scripts/generate_agda_css.py ./theme/catppuccin.css
	@python3 ./scripts/generate_agda_css.py

.PHONY: website-prepare
website-prepare: agda-html ./SUMMARY.md ./CONTRIBUTORS.md ./MAINTAINERS.md ./website/css/Agda-highlight.css
	@cp $(METAFILES) ./docs/
	@mkdir -p ./docs/website
	@cp -r ./website/images ./docs/website/
	@cp -r ./website/css ./docs/website/
	@cp -r ./website/js ./docs/website/
	@cp -r ./tables ./docs

.PHONY: website
website: website-prepare
	@mdbook build

.PHONY: serve-website
serve-website: website-prepare
	@mdbook serve -p 8080 --open -d ./book/html

.PHONY: graph
graph:
	${AGDA} ${AGDAHTMLFLAGS} --dependency-graph=docs/dependency.dot ./src/README.lagda.md

.PHONY: clean
clean:
	@rm -Rf ./_build/ ./book/ ./docs/

.PHONY: pre-commit
pre-commit:
	@pre-commit run --all-files
	@echo
	@echo Typechecking library
	@make check

install-website-dev:
	@cargo install mdbook
	@cargo install mdbook-linkcheck
	@cargo install mdbook-katex
	@cargo install mdbook-pagetoc
	@cargo install mdbook-catppuccin

.PHONY: unused-imports
unused-imports:
	python3 ./scripts/remove_unused_imports.py
	python3 ./scripts/demote_foundation_imports.py
