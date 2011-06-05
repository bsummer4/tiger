all:V:

# General Rules
%.grm.desc %.grm.sig %.grm.sml: %.grm
	mlyacc $stem.grm
%.lex.sml: %.lex
	mllex $stem.lex
%.E.sml: %.sml
	m4 -s $stem.sml | ./util/fixlines >$stem.E.sml
%.E.lex: %.lex
	m4 $stem.lex >$stem.E.lex
%.E.grm: %.grm
	m4 $stem.grm >$stem.E.grm

# The Main Library
lib =\
 util.E.sml sym.E.sml sexp.E.sml ast.E.sml ir.E.sml cir.E.sml sa.E.sml\
 ll.E.sml toc.E.sml parseutils.E.sml tiger.E.grm.sig tiger.E.grm.sml\
 tiger.E.lex.sml

cm = @/smlnj-lib.cm @/basis.cm @/ml-yacc-lib.cm
mlb =\
 @/basis/basis.mlb @/smlnj-lib/Util/smlnj-lib.mlb\
 @/mlyacc-lib/mlyacc-lib.mlb

lib.cm: ${lib:%=src/%}
	(sed 's/ /\n/g' | sed '/^$/d;1iGroup is' | sed 's|^ *@/|$/|') >$target <<!
	$cm
	$prereq
	!

lib.mlb: ${lib:%=src/%}
	(sed 's/ /\n/g' | sed '/^$/d' | sed 's|^ *@/|$(SML_LIB)/|') >$target <<!
	$mlb
	$prereq
	!

# Executables
progs = parse lex tc
subdirs = doc
exe = ${progs:%=o.%}

all:V: $exe
clean:V:
	rm -rf .cm src/.cm
	rm -f *.mlb *.cm o.* tmp.mlb *.E.* src/*.E.*

o.%: %.E.sml lib.mlb
	cat >tmp.mlb <<!
	lib.mlb
	\$(SML_LIB)/qcheck/qcheck.mlb
	$stem.E.sml
	!
	mlton -output $target tmp.mlb
