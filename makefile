all:
	mllex tiger.lex
	mlyacc tiger.grm

clean:
	rm -f *.grm.*
	rm -f *.lex.*
