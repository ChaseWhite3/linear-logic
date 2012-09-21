#lang racket/base
(require racket/match
         racket/port)

(define Atom->nat
  (make-hash))

(define int2nat
  (match-lambda
    [0
     'O]
    [n
     `(S ,(int2nat (sub1 n)))]))

(define format-formula
  (match-lambda
   [(? string? s)
    `(F_Atom 
      ,(int2nat 
        (hash-ref! Atom->nat s
                  (λ ()
                    (hash-count Atom->nat)))))]
   [`(and ,left ,right)
    `(F_Both 
      (,(format-formula left) "," ,(format-formula right)))]
   [`(implies ,left ,right)
    `(F_Impl 
      (,(format-formula left) "," ,(format-formula right)))]))

(define format-list
  (match-lambda
   [(list)
    'Nil]
   [(list-rest car cdr)
    `(Cons ((A_Linear ,(format-formula car)) "," ,(format-list cdr)))]))

(display (format-list (port->list)))

#;(for ([(k v) (in-hash Atom->nat)])
  (printf "(* ~a = ~a *)\n"
          k v))
