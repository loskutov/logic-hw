Main: Main.hs Predicates.hs
	ghc -i.. -O2 -Wall Main.hs
profile: Main.hs
	ghc -i.. -O2 -Wall -prof -fprof-auto -rtsopts Main.hs
run: Main
	./Main tests/good1.in
clean:
	rm -f Main.hi Main.o
