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


;; to convert this to support signed 32-bit arithmetic,
;; the numC type would have to wrap a 32-bit racket type
;; (assuming one exists) and the '+ and '* functions would
;; have to work on racket's 32-bit types in a 32-bit manner
;; or other functions would have to be found.
;; Alternatively, the numC type could remain a wrapper of
;; the number type.  '+ and '* would then be redefined to
;; simulate 32-bit arithmetic in terms of racket's number
;; type.  However, this would shift type-error manifestiations
;; further away from the input layer.

(define-type ExprS
  [numS (n : number)]
  [plusS (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [multS (l : ExprS) (r : ExprS)]
  [uminusS (e : ExprS)]
  [idS (id : symbol)]
  [appS (name : symbol) (expr : ExprS)])

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


(define-type FunDefC
  (fdC (name : symbol) (arg : symbol) (body : ExprC)))

(define (get-fundef [name : symbol] [fds : (listof FunDefC)]) : FunDefC
  (findf (λ ([fd : FunDefC]) : boolean
           (eq? name (fdC-name fd)))
         fds))
      
(define (subst [what : ExprC] [for : symbol] [in : ExprC]) : ExprC
        (type-case ExprC in
          [idC (id) (if (eq? id for) 
                        what 
                        in)]
          [appC (f a) (appC f (subst what for a))]
          [numC (n) in]
          [plusC (l r) (plusC (subst what for l)
                              (subst what for r))]
          [multC (l r) (multC (subst what for l)
                              (subst what for r))]))



(define (interp [a : ExprC] [fds : (listof FunDefC)]) : number
  (type-case ExprC a
    [numC (n) n]
    [plusC (l r) (+ (interp l fds) (interp r fds))]
    [multC (l r) (* (interp l fds) (interp r fds))]
    [idC (s) (error 'interpreter "unbound identifier")]
    [appC (f a) (local ([define fd (get-fundef f fds)])
                  (interp (subst a
                                 (fdC-arg fd)
                                 (fdC-body fd))
                          fds))]))

;; TODO add conditionals
;(define-type CondE
;  [condE (test-exp : ExprS) (
; (test ...)
       

;; interpreter test cases
(define (evaluate [form : s-expression]) : number
  (interp (desugar (parse form))
          (list)))


(test (evaluate '2) 2)
(test (evaluate '(- 1 2)) -1)
(test (evaluate '(+ 1 2)) 3)
(test (evaluate '(- (+ 1 2))) -3)
(test (evaluate '(* 2 3)) 6)
(test (evaluate '(* (+ (* 2 3) (+ 1 2)) 2)) 18)
