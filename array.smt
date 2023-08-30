(declare-fun sum ((Array Int Real)) Real)

(define-fun I ((b Bool)) Real
  (ite b 1.0 0.0))

(assert (forall ((e Int)) (= 1.0 (sum (lambda ((t Int)) (I (= e t)))))))

(assert (forall ((x Real) (a (Array Int Real))) (= (* x (sum a)) (sum (lambda ((i Int)) (* x (select a i)))))))

(declare-const e Int)
(declare-fun f (Int) Real)

(define-fun w () Real (f e))
(define-fun z () Real (* (f e) (sum (lambda ((t Int)) (I (= e t))))))
(define-fun y () Real (sum (lambda ((t Int)) (* (f e) (I (= t e))))))
(define-fun x () Real (sum (lambda ((t Int)) (* (f t) (I (= t e))))))

; (assert (not (= x w)))

(define-fun a () Real (sum (lambda ((t Int)) (I (= e t)))))

(assert (not (= a 1.0)))

(check-sat)
; (get-model)
