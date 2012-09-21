RACKET="/Volumes/Racket v5.3/Racket v5.3/bin/racket"
COQ="/Volumes/coqide-8.3pl4/CoqIdE_8.3pl4.app/Contents/Resources/bin/coqc"

all: linearLogic.out

basic.ml: basic.v
	${COQ} $^

INPUT=rooms.rktd
INPUT=small.rktd

linearLogic-gamma.ml: roomer-ll.rkt ${INPUT}
	${RACKET} roomer-ll.rkt < ${INPUT} > $@

linearLogic.ml: linearLogic.ml.in basic.ml linearLogic-gamma.ml
	cpp linearLogic.ml.in $@

linearLogic: linearLogic.ml
	ocamlc -o $@ $^
	
linearLogic.out: linearLogic
	./$^ 0 | tee $@