all:
	make -C HW1
	make -C HW2
	make -C TT1
	make -C TT2
	make -C TT3
clean:
	rm -f *.hi *.o
	make -C HW1 clean
	make -C HW2 clean
	make -C TT1 clean
	make -C TT2 clean
	make -C TT3 clean
