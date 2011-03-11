all:V: o.parse o.irtest
clean:V:
	rm -rf o.*
	cd src; mk clean

grammar:V:
	cd src; mk grammar

o.%: grammar src/tiger.mlb %.sml
	cat >o.$stem.mlb <<!
	src/tiger.mlb
	$stem.sml
	!
	{ mlton o.$stem.mlb; exit=$?; } && true
	rm o.$stem.mlb
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
