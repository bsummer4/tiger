ex = `{cd ex; ls}
progs = parse sa lex
subdirs = src doc

test = ${ex:%=testresults/%.parse}
exe = ${progs:%=o.%}

all:V: $exe
test:V: $test
clean:V:
	rm -rf o.* testresults tmp.mlb lex.sml
	for x in $subdirs
	do cd $x; mk clean; cd ..
	done

src:V:
	cd src; mk all

testresults/%.parse: o.sa ex/%
	mkdir -p testresults
	./o.sa <ex/$stem >testresults/$stem.parse

o.%: src %.sml
	cat >tmp.mlb <<!
	src/tiger.mlb
	$stem.sml
	!
	mlton -output $target tmp.mlb

<m4.mk
