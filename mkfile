examples = `{cd ex; ls}
progs = parse irtest

# :TODO: Generate this dependency list from $progs
all:V: o.parse o.irtest
clean:V:
	rm -rf o.* testresults tmp.mlb
	cd src; mk clean

# :TODO: Generate this dependency list from $progs and $example
test:V: testresults/8queens.parse
testresults/%.parse: o.parse ex/%
	mkdir -p testresults
	./o.parse <ex/$stem >testresults/$stem.parse

src/tiger.mlb:
	cd src; mk tiger.mlb

o.%: src/tiger.mlb %.sml
	cat >tmp.mlb <<!
	src/tiger.mlb
	$stem.sml
	!
	mlton -output $target tmp.mlb
