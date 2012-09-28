#lang racket/base
(require racket/match
         racket/list)

(struct A_Linear (f) #:transparent)
(struct A_Intuit (f) #:transparent)

(struct F_Atom (a) #:transparent)
(struct F_Impl (f g) #:transparent)
(struct F_Both (f g) #:transparent)
(struct F_Choo (f g) #:transparent)
(struct F_Eith (f g) #:transparent)
(struct F_OfCo (f) #:transparent)

(define all_P_L_Id
  (lambda (a)
    (match a
      ((list) (list))
      ((cons a0 l)
       (match l
         ((list)
          (match a0
            ((A_Linear f) (cons f (list)))
            ((A_Intuit f) (list))))
         ((cons y l0) (list)))))))

(define all_splits
  (lambda (a) (cons (cons (list) a)
                    (match a
                      ((list) (list))
                      ((cons f t)
                       (map (lambda (p)
                              (match p
                                ((cons x y) (cons (cons f x) y)))) (all_splits t)))))))

(define all_P_OfCoEl
  (lambda (a)
    (append-map (lambda (gamma_delta)
                  (match gamma_delta
                    ((cons gamma delta)
                     (let ((gamma_proves (all gamma)))
                       (append-map (lambda (f)
                                     (match f
                                       ((F_Atom a0) (list))
                                       ((F_Impl f0 f1) (list))
                                       ((F_Both f0 f1) (list))
                                       ((F_Choo f0 f1) (list))
                                       ((F_Eith f0 f1) (list))
                                       ((F_OfCo f_a)
                                        (all (append delta (cons (A_Intuit f_a) (list)))))))
                                   gamma_proves))))) (all_splits a))))

(define all_P_I_Id
  (lambda (a)
    (match a
      ((list) (list))
      ((cons a0 l)
       (match l
         ((list)
          (match a0
            ((A_Linear f) (list))
            ((A_Intuit f) (cons f (list)))))
         ((cons y l0) (list)))))))

(define all_P_Exc
  (lambda (a)
    (append-map (lambda (gamma_delta)
                  (match gamma_delta
                    ((cons gamma delta) (all (append delta gamma))))) (all_splits a))))

(define all_P_Contract
  (lambda (a)
    (match a
      ((list) (list))
      ((cons a0 t)
       (match a0
         ((A_Linear f) (list))
         ((A_Intuit f_a)
          (all (cons (A_Intuit f_a) (cons (A_Intuit f_a) t)))))))))

(define all_P_Weaken
  (lambda (a)
    (match a
      ((list) (list))
      ((cons a0 t)
       (match a0
         ((A_Linear f) (list))
         ((A_Intuit f_a) (all t)))))))

(define (all_intuit l)
  (andmap (lambda (a)
            (match a
              ((A_Linear f) #f)
              ((A_Intuit f) #t)))
          l))

(define all_P_OfCoId
  (lambda (a)
    (let ((gamma_proves
           (match (all_intuit a)
             (#t (all a))
             (#f (list)))))
      (append-map (lambda (f) (cons (F_OfCo f) (list))) gamma_proves))))

(define all_P_ImplEl
  (lambda (a)
    (append-map (lambda (gamma_delta)
                  (match gamma_delta
                    ((cons gamma delta)
                     (let ((gamma_proves (all gamma)))
                       (let ((delta_proves (all delta)))
                         (append-map (lambda (fd)
                                       (append-map (lambda (fg)
                                                     (match fg
                                                       ((F_Atom a0) (list))
                                                       ((F_Impl f_a f_b)
                                                        (match (equal? fd f_a)
                                                          (#t (cons f_b (list)))
                                                          (#f (list))))
                                                       ((F_Both f f0) (list))
                                                       ((F_Choo f f0) (list))
                                                       ((F_Eith f f0) (list))
                                                       ((F_OfCo f) (list)))) gamma_proves)) delta_proves))))))
                (all_splits a))))

(define all_P_BothId
  (lambda (a)
    (append-map (lambda (gamma_delta)
                  (match gamma_delta
                    ((cons gamma delta)
                     (let ((gamma_proves (all gamma)))
                       (let ((delta_proves (all delta)))
                         (append-map (lambda (fd)
                                       (append-map (lambda (fg) (cons (F_Both fg fd) (list)))
                                                   gamma_proves)) delta_proves)))))) (all_splits a))))

(define all_P_BothEl
  (lambda (a)
    (append-map (lambda (gamma_delta)
                  (match gamma_delta
                    ((cons gamma delta)
                     (let ((gamma_proves (all gamma)))
                       (append-map (lambda (f)
                                     (match f
                                       ((F_Atom a0) (list))
                                       ((F_Impl f0 f1) (list))
                                       ((F_Both f_a f_b)
                                        (all
                                         (append delta (cons (A_Linear f_a) (cons (A_Linear
                                                                                   f_b) (list))))))
                                       ((F_Choo f0 f1) (list))
                                       ((F_Eith f0 f1) (list))
                                       ((F_OfCo f0) (list)))) gamma_proves))))) (all_splits a))))

(define all_P_ChooId
  (lambda (a)
    (let ((gamma_proves (all a)))
      (append-map (lambda (f_a)
                    (append-map (lambda (f_b) (cons (F_Choo f_a f_b) (list)))
                                gamma_proves)) gamma_proves))))

(define all_P_ChooEl1
  (lambda (a)
    (let ((gamma_proves (all a)))
      (append-map (lambda (fChoo)
                    (match fChoo
                      ((F_Atom a0) (list))
                      ((F_Impl f f0) (list))
                      ((F_Both f f0) (list))
                      ((F_Choo f_a f_b) (cons f_a (list)))
                      ((F_Eith f f0) (list))
                      ((F_OfCo f) (list)))) gamma_proves))))

(define all_P_ChooEl2
  (lambda (a)
    (let ((gamma_proves (all a)))
      (append-map (lambda (fChoo)
                    (match fChoo
                      ((F_Atom a0) (list))
                      ((F_Impl f f0) (list))
                      ((F_Both f f0) (list))
                      ((F_Choo f_a f_b) (cons f_b (list)))
                      ((F_Eith f f0) (list))
                      ((F_OfCo f) (list)))) gamma_proves))))

(define all_P_EithEl
  (lambda (a)
    (append-map (lambda (gamma_delta)
                  (match gamma_delta
                    ((cons gamma delta)
                     (let ((gamma_proves (all gamma)))
                       (append-map (lambda (f)
                                     (match f
                                       ((F_Atom a0) (list))
                                       ((F_Impl f0 f1) (list))
                                       ((F_Both f0 f1) (list))
                                       ((F_Choo f0 f1) (list))
                                       ((F_Eith f_a f_b)
                                        (let ((delta_a_proves
                                               (all (append delta (cons (A_Linear f_a) (list))))))
                                          (let ((delta_b_proves
                                                 (all (append delta (cons (A_Linear f_b) (list))))))
                                            (append-map (lambda (f_c1)
                                                          (append-map (lambda (f_c2)
                                                                        (match (equal? f_c1 f_c2)
                                                                          (#t (cons f_c1 (list)))
                                                                          (#f (list)))) delta_b_proves))
                                                        delta_a_proves))))
                                       ((F_OfCo f0) (list)))) gamma_proves))))) (all_splits a))))

(define all-core
  (lambda (a)
    (append (all_P_L_Id a)
            (append (all_P_I_Id a)
                    (append (all_P_Exc a)
                            (append (all_P_Contract a)
                                    (append (all_P_Weaken a)
                                            (append (all_P_OfCoId a)
                                                    (append (all_P_OfCoEl a)
                                                            (append (all_P_ImplEl a)
                                                                    (append (all_P_BothId a)
                                                                            (append (all_P_BothEl a)
                                                                                    (append (all_P_ChooId a)
                                                                                            (append (all_P_ChooEl1 a)
                                                                                                    (append (all_P_ChooEl2 a)
                                                                                                            (all_P_EithEl a))))))))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define CACHE
  (make-hash))
(define (all a)
  (define how-deep
    (length
     (continuation-mark-set->list
      (current-continuation-marks)
      'all)))
  (cond
    [(how-deep . > . LIMIT)
     empty]
    [(hash-has-key? CACHE a)
     (or (hash-ref CACHE a)
         empty)]
    [else
     (with-continuation-mark
      'all #t
      (let ()
        (hash-set! CACHE a #f)
        (define r (all-core a))
        (hash-set! CACHE a r)
        r))]))

(define LIMIT 5)

(require racket/pretty
         racket/file)

(define convert
  (match-lambda
   [(list 'and f g)
    (F_Impl
     (convert f)
     (convert g))]
   [(list 'implies f g)
    (F_Choo
     (convert f)
     (convert g))]
   [(? string? s)
    (F_Atom s)]))

(all
 (map A_Linear
      (map convert
           (file->list "rooms.rktd"))))
