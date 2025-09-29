JACKDAWC := ../jackdawc/dist-newstyle/build/x86_64-linux/ghc-9.6.7/jackdawc-0.1.0.0/x/jackdawc/noopt/build/jackdawc/jackdawc
STLIB := ../jackdawc/res/stlib/
EXE := build/http_server
CC ?= cc

all:
	mkdir -p build
	$(JACKDAWC) build src --stlib $(STLIB) --exe $(EXE) --dump-c --cc $(CC) --timings +RTS -N

