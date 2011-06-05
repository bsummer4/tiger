# You must define $module $src $mlb and $cm before importing this.

all:V: $module.mlb $module.cm $src
clean:V: mlclean
mlclean:V:
	rm -rf .cm *.mlb *.cm

%.grm.desc %.grm.sig %.grm.sml: %.grm
	mlyacc $stem.grm

%.lex.sml: %.lex
	mllex $stem.lex

$module.cm: mkfile
	(sed 's/ /\n/g' | sed '/^$/d;1iGroup is' | sed 's|^ *@/|$/|') >$target <<!
	$cm
	$src
	!

$module.mlb: mkfile
	(sed 's/ /\n/g' | sed '/^$/d' | sed 's|^ *@/|$(SML_LIB)/|') >$target <<!
	$mlb
	$src
	!
