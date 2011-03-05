parser: grammar
	mlton -output bin/parser parser.mlb
test: grammar
	sml parser.cm
grammar:
	mllex tiger/tiger.lex; mlyacc tiger/tiger.grm
clean:
	rm -rf tiger/*.grm.* tiger/*.lex.* .cm bin/parser
