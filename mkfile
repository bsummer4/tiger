all:V: whitepaper.pdf
show:V: all
	zathura whitepaper.pdf

clean:V:
	rm -f whitepaper.tr whitepaper.pdf

whitepaper.tr: whitepaper
	cat >$target <<!
	.TL
	Tiger
	.AU
	Benjamin Summers
	.2C
	!
	marks <$prereq >>$target

whitepaper.pdf: whitepaper.tr
	(9 troff -ms | 9 tr2post | 9 psfonts | ps2pdf - -) <$prereq >$target
