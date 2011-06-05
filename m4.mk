clean: m4clean
m4clean:V:
	rm -f *.E.*

%.E.sml: %.sml
	m4 -s $stem.sml | ./fixlines >$stem.E.sml

tiger.E.lex: tiger.lex
	stem=tiger
	m4 $stem.lex >$stem.E.lex

tiger.E.grm: tiger.grm
	stem=tiger
	m4 $stem.grm >$stem.E.grm
