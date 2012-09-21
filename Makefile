RACKET="/Volumes/Racket v5.3/Racket v5.3/bin/racket"
COQ="/Volumes/coqide-8.3pl4/CoqIdE_8.3pl4.app/Contents/Resources/bin/coqc"

basic.ml: basic.v
	${COQ} $^

linearLogic-gamma.ml: roomer-ll.rkt rooms.rktd
	${RACKET} roomer-ll.rkt < rooms.rktd > $@
	