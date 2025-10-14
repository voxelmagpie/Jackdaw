JACKDAWC := ../../jackdawc/dist-newstyle/build/x86_64-linux/ghc-9.6.7/jackdawc-0.1.0.0/x/jackdawc/noopt/build/jackdawc/jackdawc
C2JD := ../../c2jd/dist-newstyle/build/x86_64-linux/ghc-9.6.7/c2jd-0.1.0.0/x/c2jd/noopt/build/c2jd/c2jd
STLIB := ../../jackdawc/res/stlib/
EXE := build/voxels
CC ?= cc

all: src/headers.jackdaw
	mkdir -p build
	$(JACKDAWC) build src --add-package stlib $(STLIB) --exe $(EXE) --dump-c $(shell pkg-config --libs glfw3) -lGLESv2 -lm --cc $(CC) --timings +RTS -N



src/headers.jackdaw: src/headers.c $(C2JD)
	$(C2JD) $< > $@

clean:
	-rm src/headers.jackdaw
	-rm -r build 
