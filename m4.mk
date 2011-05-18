# TODO Use regexp patterns
%.sml: %.sml.m4
	m4 <$stem.sml.m4 >$stem.sml
tiger.lex: tiger.lex.m4
	stem=tiger
	m4 <$stem.lex.m4 >$stem.lex
