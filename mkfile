all:V: o.parse o.irtest
clean:V:
	rm -rf o.*
	cd src; mk clean

src/tiger.mlb:
	cd src; mk tiger.mlb

o.%: src/tiger.mlb %.sml
	cat >tmp.mlb <<!
	src/tiger.mlb
	$stem.sml
	!
	{ mlton -output $target tmp.mlb; exit=$?; } || true
	rm tmp.mlb
	exit $exit

whitepaper.tr: whitepaper
	cat >$target <<!
	.TL
	Tiger
	.AU
	Benjamin Summers
	.2C
	!
	marks <$prereq >>$target
