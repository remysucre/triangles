; SMT encoding of UDP
; [1](https://arxiv.org/pdf/1802.02229.pdf)

; U-semirings
(declare-sort U)

; Use ints as symbols for now
; should probably use union type / naturals
(define-sort Sym () Int)

; Annotate each expression with set of fvs
(declare-datatypes (T) ((Exp (mk (val T) (var (Set Sym))))))

; Annotate each variable with its symbol
(declare-datatypes () ((Var (mk (val Int) (var Sym)))))

; Uninterpreted operations over U-semirings
(declare-fun mul (U U) U)
(declare-fun add (U U) U)
(declare-fun sigma (Int U) U)

(declare-const one U)
(declare-const zero U)

; Propagation of free variables
(define-fun u* ((x (Exp U)) (y (Exp U))) (Exp U)
  (mk (mul (val x) (val y)) (union (var x) (var y))))

(define-fun u+ ((x (Exp U)) (y (Exp U))) (Exp U)
  (mk (add (val x) (val y)) (union (var x) (var y))))

(define-fun sum ((i Var) (e (Exp U))) (Exp U)
  (mk (sigma (val i) (val e)) (store (var e) (var i) false)))

; Indicator maps true to 1 and false to 0
(define-fun I ((b (Exp Bool))) (Exp U)
  (mk (ite (val b) one zero) (var b)))

; equality over variables
(define-fun eq ((i Var) (j Var)) (Exp Bool)
  (mk (= (val i) (val j)) (lambda ((x Sym)) (or (= x (var i)) (= x (var j))))))

; +,* assoc., comm., dist.
(assert (forall ((x U) (y U) (z U)) (= (add (add x y) z) (add x (add y z)))))
(assert (forall ((x U) (y U) (z U)) (= (mul (mul x y) z) (mul x (mul y z)))))
(assert (forall ((x U) (y U)) (= (add x y) (add y x))))
(assert (forall ((x U) (y U)) (= (mul x y) (mul y x))))
(assert (forall ((x U) (y U) (z U)) (= (mul x (add y z)) (add (mul x y) (mul x z)))))

; 0,1 id.
(assert (forall ((x U)) (= x (add x zero))))
(assert (forall ((x U)) (= x (mul x one))))
(assert (forall ((x U)) (= zero (mul x zero))))

; Summation rules
(assert (forall ((t Int) (x U) (y U)) (= (sigma t (add x y)) (add (sigma t x) (sigma t y)))))
(assert (forall ((t1 Int) (t2 Int) (x U)) (= (sigma t1 (sigma t2 x)) (sigma t2 (sigma t1 x)))))
; TODO fix this (or maybe fv analysis solves it?)
(assert (forall ((x U) (e U) (t Int)) (= (mul x (sigma t e)) (sigma t (mul x e)))))

; Indicator rules

; Eq 14 from [1]
; sum_t[t=e] = 1
; (assert (forall ((t Sym) (e Sym)) (= one (val (sum (mk t 1) (I (eq (mk t 1) (mk e 2))))))))

; (assert (forall ((x (Exp U)) (e (Exp U)) (t Var)) 
;  (=> (not (select (var x) (var t))) (= (u* x (sum t e)) (sum t (u* x e))))))

; (assert (forall ((x (Exp U)) (e (Exp U)) (t Var)) 
;  (= (u* x (sum t e)) (sum t (u* x e)))))

; (declare-const e Sym)
; (declare-const t Sym)

; (declare-fun fa (Int Int) U)
; (define-fun A ((i Var) (j Var)) (Exp U)
;   (mk (fa (val i) (val j)) (lambda ((x Sym)) (or (= x (var i)) (= x (var j))))))

; Eq 15 from [1]
; (define-fun l () (Exp U) (A (mk e 1) (mk t 2)))
; (define-fun r () (Exp U) (u* (A (mk e 1) (mk t 2)) (sum (mk t 2) (I (eq (mk t 2) (mk e 1))))))

; (define-fun r () (Exp U) (sum (mk t 2) (u* (A (mk e 1) (mk t 2)) (I (eq (mk t 2) (mk e 1))))))

; (assert (not (= (val l) (val r))))

(check-sat)
; (get-model)
