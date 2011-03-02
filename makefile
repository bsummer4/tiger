all:
	mllex tiger.lex
	mlyacc tiger.grm

clean:
	rm -rf *.grm.* *.lex.* .cm
