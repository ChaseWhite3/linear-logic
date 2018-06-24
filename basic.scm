;; This extracted scheme code relies on some additional macros
;; available at http://www.pps.univ-paris-diderot.fr/~letouzey/scheme
(load "macros_extr.scm")


(define app (lambdas (l m)
  (match l
     ((Nil) m)
     ((Cons a l1) `(Cons ,a ,(@ app l1 m))))))
  
(define map (lambdas (f l)
  (match l
     ((Nil) `(Nil))
     ((Cons a t) `(Cons ,(f a) ,(@ map f t))))))
  
(define flat_map (lambdas (f l)
  (match l
     ((Nil) `(Nil))
     ((Cons x t) (@ app (f x) (@ flat_map f t))))))
  
(define forallb (lambdas (f l)
  (match l
     ((Nil) `(True))
     ((Cons a l0) (match (f a)
                     ((True) (@ forallb f l0))
                     ((False) `(False)))))))
  
(define atom_eq_dec (error "AXIOM TO BE REALIZED"))

(define formula_eq_dec (lambdas (f x0)
  (match f
     ((F_Atom a)
       (match x0
          ((F_Atom a0)
            (match (@ atom_eq_dec a a0)
               ((Left) `(Left))
               ((Right) `(Right))))
          ((F_Impl _ _) `(Right))
          ((F_Both _ _) `(Right))
          ((F_Choo _ _) `(Right))
          ((F_Eith _ _) `(Right))
          ((F_OfCo _) `(Right))))
     ((F_Impl f0 f1)
       (match x0
          ((F_Atom _) `(Right))
          ((F_Impl f2 f3)
            (match (@ formula_eq_dec f0 f2)
               ((Left)
                 (match (@ formula_eq_dec f1 f3)
                    ((Left) `(Left))
                    ((Right) `(Right))))
               ((Right) `(Right))))
          ((F_Both _ _) `(Right))
          ((F_Choo _ _) `(Right))
          ((F_Eith _ _) `(Right))
          ((F_OfCo _) `(Right))))
     ((F_Both f0 f1)
       (match x0
          ((F_Atom _) `(Right))
          ((F_Impl _ _) `(Right))
          ((F_Both f2 f3)
            (match (@ formula_eq_dec f0 f2)
               ((Left)
                 (match (@ formula_eq_dec f1 f3)
                    ((Left) `(Left))
                    ((Right) `(Right))))
               ((Right) `(Right))))
          ((F_Choo _ _) `(Right))
          ((F_Eith _ _) `(Right))
          ((F_OfCo _) `(Right))))
     ((F_Choo f0 f1)
       (match x0
          ((F_Atom _) `(Right))
          ((F_Impl _ _) `(Right))
          ((F_Both _ _) `(Right))
          ((F_Choo f2 f3)
            (match (@ formula_eq_dec f0 f2)
               ((Left)
                 (match (@ formula_eq_dec f1 f3)
                    ((Left) `(Left))
                    ((Right) `(Right))))
               ((Right) `(Right))))
          ((F_Eith _ _) `(Right))
          ((F_OfCo _) `(Right))))
     ((F_Eith f0 f1)
       (match x0
          ((F_Atom _) `(Right))
          ((F_Impl _ _) `(Right))
          ((F_Both _ _) `(Right))
          ((F_Choo _ _) `(Right))
          ((F_Eith f2 f3)
            (match (@ formula_eq_dec f0 f2)
               ((Left)
                 (match (@ formula_eq_dec f1 f3)
                    ((Left) `(Left))
                    ((Right) `(Right))))
               ((Right) `(Right))))
          ((F_OfCo _) `(Right))))
     ((F_OfCo f0)
       (match x0
          ((F_Atom _) `(Right))
          ((F_Impl _ _) `(Right))
          ((F_Both _ _) `(Right))
          ((F_Choo _ _) `(Right))
          ((F_Eith _ _) `(Right))
          ((F_OfCo f1)
            (match (@ formula_eq_dec f0 f1)
               ((Left) `(Left))
               ((Right) `(Right)))))))))
  
(define all_P_L_Id (lambda (a)
  (match a
     ((Nil) `(Nil))
     ((Cons a0 l)
       (match l
          ((Nil)
            (match a0
               ((A_Linear f) `(Cons ,f ,`(Nil)))
               ((A_Intuit _) `(Nil))))
          ((Cons _ _) `(Nil)))))))

(define all_splits (lambda (a) `(Cons ,`(Pair ,`(Nil) ,a)
  ,(match a
      ((Nil) `(Nil))
      ((Cons f t)
        (@ map (lambda (p) (match p
                              ((Pair x y) `(Pair ,`(Cons ,f ,x) ,y))))
          (all_splits t)))))))
  
(define all_P_OfCoEl (lambdas (all a)
  (@ flat_map (lambda (gamma_delta)
    (match gamma_delta
       ((Pair gamma delta)
         (let ((gamma_proves (all gamma)))
           (@ flat_map (lambda (f)
             (match f
                ((F_Atom _) `(Nil))
                ((F_Impl _ _) `(Nil))
                ((F_Both _ _) `(Nil))
                ((F_Choo _ _) `(Nil))
                ((F_Eith _ _) `(Nil))
                ((F_OfCo f_a)
                  (all (@ app delta `(Cons ,`(A_Intuit ,f_a) ,`(Nil)))))))
             gamma_proves))))) (all_splits a))))

(define all_P_I_Id (lambda (a)
  (match a
     ((Nil) `(Nil))
     ((Cons a0 l)
       (match l
          ((Nil)
            (match a0
               ((A_Linear _) `(Nil))
               ((A_Intuit f) `(Cons ,f ,`(Nil)))))
          ((Cons _ _) `(Nil)))))))

(define all_P_Exc (lambdas (all a)
  (@ flat_map (lambda (gamma_delta)
    (match gamma_delta
       ((Pair gamma delta) (all (@ app delta gamma))))) (all_splits a))))

(define all_P_Contract (lambdas (all a)
  (match a
     ((Nil) `(Nil))
     ((Cons a0 t)
       (match a0
          ((A_Linear _) `(Nil))
          ((A_Intuit f_a)
            (all `(Cons ,`(A_Intuit ,f_a) ,`(Cons ,`(A_Intuit ,f_a) ,t)))))))))

(define all_P_Weaken (lambdas (all a)
  (match a
     ((Nil) `(Nil))
     ((Cons a0 t) (match a0
                     ((A_Linear _) `(Nil))
                     ((A_Intuit _) (all t)))))))

(define all_intuit
  (forallb (lambda (a)
    (match a
       ((A_Linear _) `(False))
       ((A_Intuit _) `(True))))))

(define all_P_OfCoId (lambdas (all a)
  (let ((gamma_proves
    (match (all_intuit a)
       ((True) (all a))
       ((False) `(Nil)))))
    (@ flat_map (lambda (f) `(Cons ,`(F_OfCo ,f) ,`(Nil))) gamma_proves))))

(define all_P_ImplEl (lambdas (all a)
  (@ flat_map (lambda (gamma_delta)
    (match gamma_delta
       ((Pair gamma delta)
         (let ((gamma_proves (all gamma)))
           (let ((delta_proves (all delta)))
             (@ flat_map (lambda (fd)
               (@ flat_map (lambda (fg)
                 (match fg
                    ((F_Atom _) `(Nil))
                    ((F_Impl f_a f_b)
                      (match (@ formula_eq_dec fd f_a)
                         ((Left) `(Cons ,f_b ,`(Nil)))
                         ((Right) `(Nil))))
                    ((F_Both _ _) `(Nil))
                    ((F_Choo _ _) `(Nil))
                    ((F_Eith _ _) `(Nil))
                    ((F_OfCo _) `(Nil)))) gamma_proves)) delta_proves))))))
    (all_splits a))))

(define all_P_BothId (lambdas (all a)
  (@ flat_map (lambda (gamma_delta)
    (match gamma_delta
       ((Pair gamma delta)
         (let ((gamma_proves (all gamma)))
           (let ((delta_proves (all delta)))
             (@ flat_map (lambda (fd)
               (@ flat_map (lambda (fg) `(Cons ,`(F_Both ,fg ,fd) ,`(Nil)))
                 gamma_proves)) delta_proves)))))) (all_splits a))))

(define all_P_BothEl (lambdas (all a)
  (@ flat_map (lambda (gamma_delta)
    (match gamma_delta
       ((Pair gamma delta)
         (let ((gamma_proves (all gamma)))
           (@ flat_map (lambda (f)
             (match f
                ((F_Atom _) `(Nil))
                ((F_Impl _ _) `(Nil))
                ((F_Both f_a f_b)
                  (all
                    (@ app delta `(Cons ,`(A_Linear ,f_a) ,`(Cons ,`(A_Linear
                      ,f_b) ,`(Nil))))))
                ((F_Choo _ _) `(Nil))
                ((F_Eith _ _) `(Nil))
                ((F_OfCo _) `(Nil)))) gamma_proves))))) (all_splits a))))

(define all_P_ChooId (lambdas (all a)
  (let ((gamma_proves (all a)))
    (@ flat_map (lambda (f_a)
      (@ flat_map (lambda (f_b) `(Cons ,`(F_Choo ,f_a ,f_b) ,`(Nil)))
        gamma_proves)) gamma_proves))))

(define all_P_ChooEl1 (lambdas (all a)
  (let ((gamma_proves (all a)))
    (@ flat_map (lambda (fChoo)
      (match fChoo
         ((F_Atom _) `(Nil))
         ((F_Impl _ _) `(Nil))
         ((F_Both _ _) `(Nil))
         ((F_Choo f_a _) `(Cons ,f_a ,`(Nil)))
         ((F_Eith _ _) `(Nil))
         ((F_OfCo _) `(Nil)))) gamma_proves))))

(define all_P_ChooEl2 (lambdas (all a)
  (let ((gamma_proves (all a)))
    (@ flat_map (lambda (fChoo)
      (match fChoo
         ((F_Atom _) `(Nil))
         ((F_Impl _ _) `(Nil))
         ((F_Both _ _) `(Nil))
         ((F_Choo _ f_b) `(Cons ,f_b ,`(Nil)))
         ((F_Eith _ _) `(Nil))
         ((F_OfCo _) `(Nil)))) gamma_proves))))

(define all_P_EithEl (lambdas (all a)
  (@ flat_map (lambda (gamma_delta)
    (match gamma_delta
       ((Pair gamma delta)
         (let ((gamma_proves (all gamma)))
           (@ flat_map (lambda (f)
             (match f
                ((F_Atom _) `(Nil))
                ((F_Impl _ _) `(Nil))
                ((F_Both _ _) `(Nil))
                ((F_Choo _ _) `(Nil))
                ((F_Eith f_a f_b)
                  (let ((delta_a_proves
                    (all (@ app delta `(Cons ,`(A_Linear ,f_a) ,`(Nil))))))
                    (let ((delta_b_proves
                      (all (@ app delta `(Cons ,`(A_Linear ,f_b) ,`(Nil))))))
                      (@ flat_map (lambda (f_c1)
                        (@ flat_map (lambda (f_c2)
                          (match (@ formula_eq_dec f_c1 f_c2)
                             ((Left) `(Cons ,f_c1 ,`(Nil)))
                             ((Right) `(Nil)))) delta_b_proves))
                        delta_a_proves))))
                ((F_OfCo _) `(Nil)))) gamma_proves))))) (all_splits a))))

(define all_theorems (lambdas (n a)
  (match n
     ((O) `(Nil))
     ((S n0)
       (@ app (all_P_L_Id a)
         (@ app (all_P_I_Id a)
           (@ app (@ all_P_Exc (all_theorems n0) a)
             (@ app (@ all_P_Contract (all_theorems n0) a)
               (@ app (@ all_P_Weaken (all_theorems n0) a)
                 (@ app (@ all_P_OfCoId (all_theorems n0) a)
                   (@ app (@ all_P_OfCoEl (all_theorems n0) a)
                     (@ app (@ all_P_ImplEl (all_theorems n0) a)
                       (@ app (@ all_P_BothId (all_theorems n0) a)
                         (@ app (@ all_P_BothEl (all_theorems n0) a)
                           (@ app (@ all_P_ChooId (all_theorems n0) a)
                             (@ app (@ all_P_ChooEl1 (all_theorems n0) a)
                               (@ app (@ all_P_ChooEl2 (all_theorems n0) a)
                                 (@ all_P_EithEl (all_theorems n0) a))))))))))))))))))
  
