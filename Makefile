all:
	make -C HW1
	make -C HW2
	make -C HW3
	make -C TT1
	make -C TT2
	make -C TT3
	make -C TT4
	make -C TT5
	make -C TT6
clean:
	rm -f *.hi *.o
	make -C HW1 clean
	make -C HW2 clean
	make -C HW3 clean
	make -C TT1 clean
	make -C TT2 clean
	make -C TT3 clean
	make -C TT4 clean
	make -C TT5 clean
	make -C TT6 clean
