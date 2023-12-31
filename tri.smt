; SMT encoding of UDP
; [1](https://arxiv.org/pdf/1802.02229.pdf)

; use ints as symbols for now
(define-sort Sym () Int)
; annotate each expression with set of fvs
(declare-datatypes (T) ((Exp (mk (val T) (var (Set Sym))))))
; annotate each variable with its symbol
(declare-datatypes () ((Var (mk (val Int) (var Sym)))))

(declare-fun sigma (Int Real) Real)

(define-fun mul ((x (Exp Real)) (y (Exp Real))) (Exp Real)
  (mk (* (val x) (val y)) (union (var x) (var y))))

(define-fun add ((x (Exp Real)) (y (Exp Real))) (Exp Real)
  (mk (+ (val x) (val y)) (union (var x) (var y))))

(define-fun sum ((i Var) (e (Exp Real))) (Exp Real)
  (mk (sigma (val i) (val e)) (store (var e) (var i) false)))

; indicator maps true to 1 and false to 0
(define-fun I ((b (Exp Bool))) (Exp Real)
  (mk (ite (val b) 1.0 0.0) (var b)))

; equality over variables
(define-fun eq ((i Var) (j Var)) (Exp Bool)
  (mk (= (val i) (val j)) (lambda ((x Sym)) (or (= x (var i)) (= x (var j))))))

; Eq 14 from [1]
; sum_t[t=e] = 1
(assert (forall ((t Sym) (e Sym)) (= 1.0 (val (sum (mk t 1) (I (eq (mk t 1) (mk e 2))))))))

; (assert (forall ((x (Exp Real)) (e (Exp Real)) (t Var)) 
;  (=> (not (select (var x) (var t))) (= (mul x (sum t e)) (sum t (mul x e))))))

(assert (forall ((x (Exp Real)) (e (Exp Real)) (t Var)) 
 (= (mul x (sum t e)) (sum t (mul x e)))))

(declare-const e Sym)
(declare-const t Sym)

(declare-fun fa (Int Int) Real)
(define-fun A ((i Var) (j Var)) (Exp Real)
  (mk (fa (val i) (val j)) (lambda ((x Sym)) (or (= x (var i)) (= x (var j))))))

; Eq 15 from [1]
(define-fun l () (Exp Real) (A (mk e 1) (mk t 2)))
; (define-fun r () (Exp Real) (mul (A (mk e 1) (mk t 2)) (sum (mk t 2) (I (eq (mk t 2) (mk e 1))))))

(define-fun r () (Exp Real) (sum (mk t 2) (mul (A (mk e 1) (mk t 2)) (I (eq (mk t 2) (mk e 1))))))

(assert (not (= (val l) (val r))))

(check-sat)
; (get-model)
