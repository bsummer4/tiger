ex = `{cd ex; ls}
progs = parse lex tc
subdirs = src doc

test = ${ex:%=testresults/%.parse}
exe = ${progs:%=o.%}

all:V: $exe
test:V: $test
clean:V:
	rm -rf o.* testresults tmp.mlb
	for x in $subdirs
	do cd $x; mk clean; cd ..
	done

src:V:
	cd src; mk all

testresults/%.parse: o.tc ex/%
	mkdir -p testresults
	./o.tc <ex/$stem >testresults/$stem.parse

o.%: src %.E.sml
	cat >tmp.mlb <<!
	src/tiger.mlb
	\$(SML_LIB)/qcheck/qcheck.mlb
	$stem.E.sml
	!
	mlton -output $target tmp.mlb

<ml.mk
<m4.mk
