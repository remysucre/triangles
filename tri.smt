(define-sort Idx () Int)
(declare-datatypes (T) ((Exp (mk (val T) (var (Set Idx))))))
(declare-datatypes () ((Var (mk (val Int) (var Idx)))))

(declare-fun sig (Int Real) Real)

(define-fun mul ((x (Exp Real)) (y (Exp Real))) (Exp Real)
  (mk (* (val x) (val y)) (union (var x) (var y))))

(define-fun add ((x (Exp Real)) (y (Exp Real))) (Exp Real)
  (mk (+ (val x) (val y)) (union (var x) (var y))))

(define-fun sum ((i Var) (e (Exp Real))) (Exp Real)
  (mk (sig (val i) (val e)) (store (var e) (var i) false)))

(define-fun I ((c (Exp Bool))) (Exp Real)
  (mk (ite (val c) 1.0 0.0) (var c)))

(define-fun eq ((i Var) (j Var)) (Exp Bool)
  (mk (= (val i) (val j)) (lambda ((x Idx)) (or (= x (var i)) (= x (var j))))))

(assert (forall ((t Idx) (e Idx)) (= 1.0 (val (sum (mk t 1) (I (eq (mk t 1) (mk e 2))))))))

(declare-const i Idx)
(declare-const j Idx)
(declare-fun fi (Idx) Real)
(declare-fun f (Var) (Exp Real))

(assert (forall ((i Var)) (= (val (f i)) (fi (val i)))))

(declare-const e Idx)
(declare-const t Idx)

(define-fun l () (Exp Real) (f (mk e 1)))
(define-fun r () (Exp Real) (mul (f (mk e 1)) (sum (mk t 2) (I (eq (mk t 2) (mk e 1))))))

(assert (not (= (val l) (val r))))

(check-sat)
; (get-model)
