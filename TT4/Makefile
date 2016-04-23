all: Main.hs
	ghc -i.. -Wall -O2 Main.hs
llvm: Main.hs
	ghc -i.. -Wall -fllvm -O2 Main.hs
run: all
	./Main tests/good1.in
clean:
	rm -f Main Main.hi Main.o
