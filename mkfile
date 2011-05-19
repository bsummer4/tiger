ex = `{cd ex; ls}
progs = parse sa lex tc
progs = tc # parse
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

testresults/%.parse: o.tc ex/%
	mkdir -p testresults
	./o.tc <ex/$stem >testresults/$stem.parse

o.%: src %.sml
	cat >tmp.mlb <<!
	src/tiger.mlb
	$stem.sml
	!
	mlton -output $target tmp.mlb

<m4.mk
