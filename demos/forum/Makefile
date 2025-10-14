JACKDAWC := ../../jackdawc/dist-newstyle/build/x86_64-linux/ghc-9.6.7/jackdawc-0.1.0.0/x/jackdawc/noopt/build/jackdawc/jackdawc
STLIB := ../../jackdawc/res/stlib/
EXE := build/forum
CC ?= cc

all:
	mkdir -p build
	$(JACKDAWC) build src --add-package stlib $(STLIB) --add-package http ../../http --exe $(EXE) --cc $(CC) -lmariadbclient +RTS -N


clean:
	-rm -r build 
