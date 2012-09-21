#lang racket
(require "adventure.rkt"
         racket/pretty
         tests/eli-tester)

(define-syntax-rule (room-module-begin limit goal room output)
  (#%module-begin
   (define items (look->items 'room))
   (printf "~nThe items in this room are:~n")
   (pretty-print items)
   
   (define plan (items->goal-plan items goal))
   (printf "~nHere is the plan:~n")
   (pretty-print plan)
   
   (define script (plan->script limit items plan))
   (printf "~nHere is the script~n")
   (pretty-print script)
   
   (newline)
   (define pscript 
     (with-output-to-string
      (λ () 
        (print-script script))))
   (display pscript)
   (test pscript => output)))

(provide
 #%datum
 (rename-out [room-module-begin #%module-begin]))