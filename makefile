all:
	mllex tiger.lex
	mlyacc tiger.grm
#	rm tiger.grm.desc

clean:
	rm -rf *.grm.* *.lex.* .cm
