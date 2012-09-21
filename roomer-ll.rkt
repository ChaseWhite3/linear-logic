#lang racket/base
(require racket/match
         racket/port)

(define Atom->nat
  (make-hash))

(define format-formula
  (match-lambda
   [(? string? s)
    `(F_Atom 
      ,(hash-ref! Atom->nat s
                  (λ ()
                    (hash-count Atom->nat))))]
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

(printf "Definition some_gamma :=\n")

(require racket/pretty)
(pretty-display (format-list (port->list)))

(printf ".\n\n")

(for ([(k v) (in-hash Atom->nat)])
  (printf "(* ~a = ~a *)\n"
          k v))
