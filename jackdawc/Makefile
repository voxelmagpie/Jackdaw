.PHONY: all
all: tests

.PHONY: tests
tests: stlib
	cabal run --disable-optimization --enable-debug-info jackdawc -- run-tests --c-warnings +RTS -N

.PHONY: tests_tcc
tests_tcc: stlib
	cabal run --disable-optimization --enable-debug-info jackdawc -- run-tests --cc tcc --single-threaded --unchecked-arithmetic +RTS -N

.PHONY: debug
debug: stlib
	cabal build --disable-optimization --enable-debug-info jackdawc

# Drag and drop the jackdawc.prof file into https://www.speedscope.app/
# The .ps file can be viewed in Inkscape
.PHONY: profile_tests
profile_tests: stlib
	cabal run --enable-optimization=2 --enable-profiling jackdawc -- run-tests --cc tcc --single-threaded --unchecked-arithmetic +RTS -N -sstderr -pj -hc -l -L100
	-hp2ps -c -M jackdawc.hp

.PHONY: release
release: stlib
	cabal build --enable-optimization=2 --disable-profiling jackdawc -- +RTS -N

.PHONY: stlib
stlib: res/stlib/primitives.jackdaw

res/stlib/primitives.jackdaw: res/stlib/primitives
	cpp -P $< -o $@
	sed -i -e 's/ _NL /\n/g' $@

.PHONY: clean
clean:
	-rm res/stlib/primitives.jackdaw
	-rm -r dist-newstyle
	-rm jackdawc.aux
	-rm jackdawc.eventlog
	-rm jackdawc.hp
	-rm jackdawc.prof
	-rm jackdawc.ps


.DELETE_ON_ERROR:
