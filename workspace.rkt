#lang plai-typed

;; TODO
;; - warn on incorrect number of arguments to all expressions e.g. now (+ 1 2 3) => 3
;; - add conditionals
;; - more tests

(require 
 (typed-in racket/base [findf : (('a -> boolean) (listof 'a) -> 'a)])
 (rename-in 
  (typed-in racket/base [foldl : (('a 'b 'c -> 'c) 'c (listof 'a) (listof 'b) -> 'c)])
  [foldl foldl2]))
                                                              

(define-type ExprC
  [idC (s : symbol)]
  [numC (n : number)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)]
  [appC (fun : ExprC) (args : (listof ExprC))]
  [lamC (args : (listof symbol)) (body : ExprC)]
  [boxC (arg : ExprC)]
  [unboxC (arg : ExprC)]
  [setboxC (b : ExprC) (v : ExprC)]
  [seqC (b1 : ExprC) (b2 : ExprC)])

(define-type Value
  [numV (n : number)]
  [clsV (names : (listof symbol)) (body : ExprC) (env : Env)]
  [boxV (v : Location)])

(define-type BindingS
  [bindingS (id : symbol) (expr : ExprS)])

(define-type ExprS
  [numS (n : number)]
  [plusS (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [multS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [idS (id : symbol)]
  [letS (bindings : (listof BindingS)) (body : ExprS)]
  [appS (fun : ExprS) (exprs : (listof ExprS))]
  [lamS (args : (listof symbol)) (expr : ExprS)])

(define-type-alias Location number)

(define new-loc
  (let ([b (box 0)])
    (λ () : Location
      (begin (set-box! b (+ (unbox b) 1))
           (unbox b)))))

(define-type Binding
  [bind (name : symbol) (val : Location)])

(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)

(define-type Storage
  [cell (location : Location) (val : Value)])

(define-type-alias Store (listof Storage))
(define mt-store empty)
(define override-store cons)

(define (lookup [for : symbol] [env : Env]) : Location
  (cond
    [(empty? env) (error 'lookup "name not found")]
    [else (cond
            [(symbol=? for (bind-name (first env)))
             (bind-val (first env))]
            [else (lookup for (rest env))])]))

(define (fetch [loc : Location] [sto : Store]) : Value
  (cond
    [(empty? sto) (error 'fetch "loc not found")]
    [else (cond
            [(= loc (cell-location (first sto)))
             (cell-val (first sto))]
            [else (fetch loc (rest sto))])]))

(test/exn (fetch 1 mt-store) "not found")
(test/exn (fetch 1 (override-store (cell 2 (numV 3)) mt-store))
      "not found")
(test (fetch 1 (override-store (cell 1 (numV 3)) mt-store))
      (numV 3))
(test (fetch 1 (override-store (cell 1 (numV 3))
                               (override-store
                                (cell 1 (numV 2)) mt-store)))
      (numV 3))

(define (parse-binding-pairs [bindings : (listof s-expression)]) : (listof BindingS)
  (map
   (λ ([binding-form : s-expression]) : BindingS
     (if (s-exp-list? binding-form)
         (let ([binding-form* (s-exp->list binding-form)])
           (bindingS (s-exp->symbol (first binding-form*))
                     (parse (second binding-form*))))
         (error 'let "invalid binding form. expected symbol, expr pair")))
   bindings))

(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))]
    [(s-exp-list? s)
       (let ([s1 (s-exp->list s)])
         (cond 
           [(s-exp-list? (first s1)) (appS (parse (first s1)) (map parse (rest s1)))] 
           [else  
            (case (s-exp->symbol (first s1))
              ['+ (plusS (parse (second s1)) (parse (third s1)))]
              ['* (multS (parse (second s1)) (parse (third s1)))]
              ['- (if (= (length s1) 2) (uminusS (parse (second s1)))
                      (bminusS (parse (second s1)) (parse (third s1))))]
              ['let (if (s-exp-list? (second s1))
                        (let ([binding-pairs (s-exp->list (second s1))])
                          (letS (parse-binding-pairs binding-pairs)
                                (parse (third s1))))
                        (error 'let "invalid binding syntax. expected list"))]
              ['λ (lamS (map s-exp->symbol (s-exp->list (second s1))) (parse (third s1)))]
              [else (appS (parse (first s1))
                          (map parse (rest s1)))])]))]))


(test (parse '(+ (* 1 2) (+ 2 3)))
      (plusS (multS (numS 1) (numS 2)) (plusS (numS 2) (numS 3))))


(define (lift-op [op : (number number -> number)]) : (Value Value -> Value)
  (λ ([l : Value] [r : Value]) : Value
    (cond
      [(and (numV? l) (numV? r))
       (numV (op (numV-n l) (numV-n r)))]
      [else
       (error 'num+ "non-number argument")])))

(define num+ (lift-op +))
(define num* (lift-op *))


(define (desugar [as : ExprS]) : ExprC
  (type-case ExprS as
    [numS (n) (numC n)]
    [plusS (l r) (plusC (desugar l)
                        (desugar r))]
    [multS (l r) (multC (desugar l) 
                        (desugar r))]
    [bminusS (l r) (plusC (desugar l) 
                          (multC (numC -1) 
                                 (desugar r)))]
    [uminusS (e) (multC (numC -1)
                        (desugar e))]
    [idS (id) (idC id)]
    [appS (f a) (appC (desugar f) (map desugar a))]
    [lamS (a b) (lamC a (desugar b))]
    [letS (bindings body) 
          (let ([names (map bindingS-id bindings)]
                [exprs (map bindingS-expr bindings)])
            (desugar (appS (lamS names body)
                           exprs)))]))

(define-type Result
  [v*s (v : Value) (s : Store)])

(define (interp [a : ExprC] [env : Env] [sto : Store] ) : Result
  (type-case ExprC a
    [numC (n) (v*s (numV n) sto)]
    [plusC (l r) (type-case Result (interp l env sto)
                   [v*s (v-l s-l)
                        (type-case Result (interp r env s-l)
                          [v*s (v-r s-r)
                               (v*s (num+ v-l v-r) s-r)])])]
    [multC (l r) (type-case Result (interp l env sto)
                   [v*s (v-l s-l)
                        (type-case Result (interp r env s-l)
                          [v*s (v-r s-r)
                               (v*s (num* v-l v-r) s-r)])])]
    [idC (n) (v*s (fetch (lookup n env) sto) sto)]
    [appC (f args) (local ([define fV (interp f env)])
                     (interp 
                      (clsV-body fV)
                      (foldl2 (λ ([name : symbol] [expr : ExprC] [env : Env]) : Env
                                (extend-env (bind name
                                                  (interp expr env))
                                            env))
                              (clsV-env fV)
                              (clsV-names fV)
                              args)))]
    [lamC (args b) (v*s (clsV args b env) sto)]
    
    [boxC (val-expr) (type-case Result (interp val-expr env sto)
                       [v*s (v-a s-a)
                            (let ([where (new-loc)])
                              (v*s (boxV where)
                                   (override-store (cell where v-a)
                                                   s-a)))])]
    [unboxC (box-expr) (type-case Result (interp box-expr env sto)
                         [v*s (v-expr s-expr)                              
                              [numV (_) (error 'unbox "Can't unbox a number")]
                              [clsV (a b c) (error 'unbox "Can't unbox a closure")]
                              [boxV (val) val]))]
    [setboxC (box-expr val-expr) (numV 2)]
    [seqC (expr1 expr2) (type-case Result (interp expr1 env sto)
                          [v*s (v-expr1 s-expr1)
                               (interp expr2 env s-expr1)])]))
    
(test (interp (boxC (numC 2)) mt-env)
      (boxV (numV 2)))
(test (interp (unboxC (boxC (numC 2))) mt-env)
      (numV 2))
(test/exn (interp (unboxC (numC 2)) mt-env)
          "Can't unbox")

(define test-expr
  (appC 
   (lamC (list 'b)
         (seqC
          (seqC
           (setboxC (idC 'b) (plusC (numC 1) (unboxC (idC 'b))))
           (setboxC (idC 'b) (plusC (numC 1) (unboxC (idC 'b)))))
          (unboxC (idC 'b))))
   (list (boxC (numC 0)))))
  
;; interpreter test cases
(define (evaluate* [form : s-expression] [env : Env]) : Value
  (interp (desugar (parse form))
          env))

(define (evaluate [form : s-expression]) : number
  (numV-n (evaluate* form mt-env)))


(test (evaluate '2) 2)
(test (evaluate '(- 1 2)) -1)
(test (evaluate '(+ 1 2)) 3)
(test (evaluate '(- (+ 1 2))) -3)
(test (evaluate '(* 2 3)) 6)
(test (evaluate '(* (+ (* 2 3) (+ 1 2)) 2)) 18)
(test (evaluate '(+ 10 ((λ (x y) (- x y)) 10 20))) 0) 
(test (evaluate* '(+ 10 (f 10 20)) (extend-env (bind 'f (evaluate* '(λ (x y) (- x y)) mt-env))
                                              mt-env))
      (numV 0))
(test (evaluate '(let ((a 5)) a)) 5)
(test (evaluate '(let ((a 5)
                       (b (λ (x) (+ x x))))
                   (b a)))
      10)

;(define f (def-fd 'f 'x '(* x 2)))
;(define z (def-fd 'z 'x '(+ x 3)))
;(define g (def-fd 'g 'x '(+ x y)))
;(define h (def-fd 'h 'y '(g 2)))
;(test (evaluate* '(f 2) (list f)) 4)
;(test (evaluate* '(f (f 2)) (list f z)) 8)
;(test (evaluate* '(f (z 2)) (list f z)) 10)
;(test (evaluate* '(f (z 2)) (list z f)) 10)
;(test (evaluate* '(f (z (+ (f 3) (z (* (f 3) 2))))) (list z f)) 48)
;(test/exn (evaluate* '(h 3) (list z g f h)) "name not found")
