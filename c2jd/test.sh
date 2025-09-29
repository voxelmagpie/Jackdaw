set -e
sh build.sh

mkdir -p out

./dist-newstyle/build/x86_64-linux/ghc-9.6.7/c2jd-0.1.0.0/x/c2jd/noopt/build/c2jd/c2jd test.c --dump-c > out/out.jackdaw
