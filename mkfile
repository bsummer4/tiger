# :TODO: Generate some dependency lists
#	Various dependency lists could be generate from variables.

examples = `{cd ex; ls}
progs = parse irtest

all:V: o.parse o.irtest
test:V: testresults/8queens.parse
clean:V:
	rm -rf o.* testresults tmp.mlb
	cd src; mk clean

src:V:
	cd src; mk all

testresults/%.parse: o.parse ex/%
	mkdir -p testresults
	./o.parse <ex/$stem >testresults/$stem.parse

src/tiger.mlb:
	cd src; mk tiger.mlb

o.%: src src/tiger.mlb %.sml
	cat >tmp.mlb <<!
	src/tiger.mlb
	$stem.sml
	!
	mlton -output $target tmp.mlb
