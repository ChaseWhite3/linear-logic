#lang racket/base
(require racket/match
         racket/list)

(void (read-line))
(void (read-line))
(void (read-line))

(define format-kind
  (match-lambda
   [`(kind (name ,name) (condition ,cond))
    (format-formula cond name)]))

(define format-and
  (match-lambda
   [(list e)
    (format-kind e)]
   [(list e more)
    `(and ,(format-kind e)
          ,(format-and more))]))

(define (format-formula c n)
  (match c
    [`(broken (condition ,out)
              (missing ,in))
     `(implies ,(format-and in)
               ,(format-formula out n))]
    [`(pristine)
     n]))

(define parse-item
  (match-lambda
   [`(item (name ,name)
           (description ,_)
           (adjectives . ,_)
           (condition ,c)
           ,(or (and (list 'piled_on)
                     (app (λ _ empty) i))
                (list 'piled_on i)))
    (pretty-write (format-formula c name))
    (for-each parse-item i)]))

(require racket/pretty)

(match (read)
  [`(success
     (command
      (look
       (name ,_)
       (description ,_)
       (items ,l))))
   (for-each parse-item l)]
  [`(success
     (command
      (look
       (room
        (name ,_)
        (description ,_)
        (items ,l)))))
   (for-each parse-item l)])
