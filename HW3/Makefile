all: Main.hs
	ghc -i.. -O2 -Wall Main.hs
llvm: Main.hs
	ghc -i.. -fllvm -O2 -Wall Main.hs
run: all
	./Main tests/good1.in
clean:
	rm -f Main.hi Main.o
