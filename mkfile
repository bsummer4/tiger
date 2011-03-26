ex = `{cd ex; ls}
progs = parse irtest
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

testresults/%.parse: o.parse ex/%
	mkdir -p testresults
	./o.parse <ex/$stem >testresults/$stem.parse

o.%: src %.sml
	cat >tmp.mlb <<!
	src/tiger.mlb
	$stem.sml
	!
	mlton -output $target tmp.mlb
