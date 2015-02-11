.PHONY: default
.PHONY: prepare prepare-asmdex prepare-soot
.PHONY: development development-build development-package development-install
.PHONY: release release-build release-package release-install
.PHONY: install doc
.PHONY: clean test

.DEFAULT: default

NAME:=woa
SRC:=$(shell find src -type f -name '*.clj' -o -name '*.java') project.clj
SRC_MAIN:=src/woa/core.clj

# see if Grenchman Leiningen wrapper could be used
LEIN:=$(shell \
    grench lein help > /dev/null 2>&1; \
    if [ $$? = 0 ]; then \
      echo grench lein; \
    else \
      echo lein; \
    fi)

default: development 

all: release test

development: development.touch development-package development-install

development-build: development.touch

development.touch: $(SRC)
	$(LEIN) uberjar && touch $@ || { rm -f $@; false; }

development-package: bin/$(NAME) bin/$(NAME)-with-jmx bin/android.jar | development-build
	cp target/uberjar/$(NAME).jar bin/$(NAME).jar
	tar cvf $(NAME).tar bin

development-install: bin/$(NAME) bin/$(NAME)-with-jmx bin/android.jar | development-build
	cp target/uberjar/$(NAME).jar bin/$(NAME).jar
	mkdir -p ~/bin/
	cp bin/* ~/bin/
	chmod +x ~/bin/$(NAME)

release: release-build release-package release-install doc

release-build: release.touch

release.touch: $(SRC)
	perl -pli.bak -e 'BEGIN { chomp($$G=`git rev-parse HEAD`); chomp($$GC=`if \$$(git diff-index --quiet --cached HEAD); then echo clean; else echo dirty; fi`); chomp($$T=`date -u +"%a %Y%m%d %T %Z"`); chomp($$M=`uname -a`); } s/<BUILDINFO>/Buildenv: $$M\nDate: $$T\nGit commit: $$G ($$GC)/;'\
	    $(SRC_MAIN); \
	    $(LEIN) uberjar; RET=$$?;\
	    cp -f $(SRC_MAIN).bak $(SRC_MAIN);\
	    if [ $$RET -eq 0 ]; then touch $@; else rm -f $@; false; fi; 

release-package: bin/$(NAME) bin/$(NAME)-with-jmx bin/android.jar bin/neo4j-batch-import | release-build
	cp target/uberjar/$(NAME).jar bin/$(NAME).jar
	tar cvf $(NAME).tar bin

release-install: bin/$(NAME) bin/$(NAME)-with-jmx bin/android.jar bin/neo4j-batch-import | release-build
	cp target/uberjar/$(NAME).jar bin/$(NAME).jar
	mkdir -p ~/bin/
	cp bin/* ~/bin/
	chmod +x ~/bin/$(NAME)

doc: docs/uberdoc.html

docs/uberdoc.html: $(SRC)
	$(LEIN) marg

test: 
	find 01sample -type f | \
	    $(NAME) --prep-tags '{"Dataset" "my sample dataset"}' | \
	    $(NAME)-with-jmx 2014 -dsvvv

# localrepo cannot use grench wrapper, otherwise directory may be wrong
prepare: prepare-asmdex prepare-soot

prepare-asmdex: 00deps/asmdex.jar
	lein localrepo install $< asmdex/asmdex 1.0

prepare-soot: 00deps/soot-trunk.jar
	lein localrepo install $< soot/soot 1.0

00deps/asmdex.jar: 
	wget $$(cat 00deps/asmdex.url) -O $@

00deps/soot-trunk.jar: 
	wget $$(cat 00deps/soot.url) -O $@

00deps/heros.jar: 
	wget $$(cat 00deps/heros.url) -O $@

bin/android.jar: 
	wget $$(cat 00deps/android-jar.url) -O $@

clean:
	rm -rf target *.touch

# defmacro dependencies
src/woa/apk/dex/soot/parse.clj: src/woa/apk/dex/soot/util.clj src/woa/apk/dex/soot/simulator.clj
	touch $@
