all: Main.hs
	ghc -i.. -O2 Main.hs
run: all
	./Main tests/good1.in
tests: all
	for i in tests/*; do if (./Main $i | grep Не); then echo $i; fi; done
