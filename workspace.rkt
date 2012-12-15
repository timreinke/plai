#lang plai-typed

(require (typed-in racket/base [findf : (('a -> boolean) (listof 'a) -> 'a)]))

(define-type MisspelledAnimal
    [caml (humps : number)]
    [yacc (height : number)])

(define (good? [ma : MisspelledAnimal]) : boolean
    (type-case MisspelledAnimal ma
      [caml (humps) (>= humps 2)]
      [yacc (height) (> height 2.1)]))


(define hey : MisspelledAnimal (caml 2))

(test (good? hey) #t)
(test (good? (yacc 2)) #f)

(define-type ExprC
  [idC (s : symbol)]
  [appC (fun : symbol) (arg : ExprC)]
  [numC (n : number)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)])

(define-type ExprS
  [numS (n : number)]
  [plusS (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [multS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [idS (id : symbol)]
  [appS (name : symbol) (expr : ExprS)])

(define-type FunDefC
  (fdC (name : symbol) (arg : symbol) (body : ExprC)))

(define-type Binding
  [bind (name : symbol) (val : number)])

(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)

(define (lookup [for : symbol] [env : Env]) : number
  (cond
    [(empty? env) (error 'lookup "name not found")]
    [else (cond
            [(symbol=? for (bind-name (first env)))
             (bind-val (first env))]
            [else (lookup for (rest env))])]))

(define (get-fundef [name : symbol] [fds : (listof FunDefC)]) : FunDefC
  (findf (λ ([fd : FunDefC]) : boolean
           (eq? name (fdC-name fd)))
         fds))

(define (parse [s : s-expression])
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))]
    [(s-exp-list? s) 
       (let ([s1 (s-exp->list s)])
         (case (s-exp->symbol (first s1))
           ['+ (plusS (parse (second s1)) (parse (third s1)))]
           ['* (multS (parse (second s1)) (parse (third s1)))]
           ['- (if (= (length s1) 2) (uminusS (parse (second s1)))
                   (bminusS (parse (second s1)) (parse (third s1))))]
           ;; otherwise, just assume it's function application
           ;; if it's not, it's not a valid program anyway (though
           ;; a friendly parser may catch the error here e.g. a number
           ;; in the function application position).  
           ;; at this point, only functions of one argument are
           ;; supported
           [else (appS (s-exp->symbol (first s1))
                       (parse (second s1)))]))]))


(test (parse '(+ (* 1 2) (+ 2 3)))
      (plusS (multS (numS 1) (numS 2)) (plusS (numS 2) (numS 3))))


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
    [appS (f a) (appC f (desugar a))]))
     
(define (interp [a : ExprC] [env : Env] [fds : (listof FunDefC)]) : number
  (type-case ExprC a
    [numC (n) n]
    [plusC (l r) (+ (interp l env fds) (interp r env fds))]
    [multC (l r) (* (interp l env fds) (interp r env fds))]
    [idC (n) (lookup n env)]
    [appC (f a) (local ([define fd (get-fundef f fds)])
                  (interp (fdC-body fd)
                          (extend-env 
                           (bind (fdC-arg fd)
                                 (interp a env fds))
                           mt-env)
                          fds))]))

;; TODO add conditionals
;(define-type CondE
;  [condE (test-exp : ExprS) (
; (test ...)
       

;; interpreter test cases
(define (evaluate* [form : s-expression]
                   [fndefs : (listof FunDefC)]) : number
  (interp (desugar (parse form))
          mt-env
          fndefs))

(define (evaluate [form : s-expression]) : number
  (evaluate* form (list)))


(test (evaluate '2) 2)
(test (evaluate '(- 1 2)) -1)
(test (evaluate '(+ 1 2)) 3)
(test (evaluate '(- (+ 1 2))) -3)
(test (evaluate '(* 2 3)) 6)
(test (evaluate '(* (+ (* 2 3) (+ 1 2)) 2)) 18)

;; utility function to define FunDefC from a s-expression
(define (def-fd [name : symbol] [arg : symbol] [e : s-expression]) : FunDefC
  (fdC name arg (desugar (parse e))))

(define f (def-fd 'f 'x '(* x 2)))
(define z (def-fd 'z 'x '(+ x 3)))
(define g (def-fd 'g 'x '(+ x y)))
(define h (def-fd 'h 'y '(g 2)))
(test (evaluate* '(f 2) (list f)) 4)
(test (evaluate* '(f (f 2)) (list f z)) 8)
(test (evaluate* '(f (z 2)) (list f z)) 10)
(test (evaluate* '(f (z 2)) (list z f)) 10)
(test (evaluate* '(f (z (+ (f 3) (z (* (f 3) 2))))) (list z f)) 48)
(test/exn (evaluate* '(h 3) (list z g f h)) "name not found")
