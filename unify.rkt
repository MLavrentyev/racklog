#lang racket/base
(require (for-syntax racket/base)
         racket/list
         racket/match
         racket/function
         racket/vector
         racket/set
         racket/stream
         racket/string
         "control.rkt")
(provide (all-defined-out))

; same hash
(define (make-immutable-hash*) (make-immutable-hash empty))
(define (make-immutable-hasheqv*) (make-immutable-hasheqv empty))
(define (make-immutable-hasheq*) (make-immutable-hasheq empty))
(define (same-hash-make ht)
  (match ht
    [(? immutable?)
     (match ht
       [(? hash-equal?) make-immutable-hash*]
       [(? hash-eqv?) make-immutable-hasheqv*]
       [(? hash-eq?) make-immutable-hasheq*])]
    [(? hash-weak?)
     (match ht
       [(? hash-equal?) make-weak-hash]
       [(? hash-eqv?) make-weak-hasheqv]
       [(? hash-eq?) make-weak-hasheq])]
    [_
     (match ht
       [(? hash-equal?) make-hash]
       [(? hash-eqv?) make-hasheqv]
       [(? hash-eq?) make-hasheq])]))
(define (same-hash-kind? x y)
  (eq? (same-hash-make x) (same-hash-make y)))
(define (same-hash-map f ht)
  (define new-ht ((same-hash-make ht)))
  (if (immutable? ht)
      (for/fold ([new-ht new-ht])
        ([(k v) (in-hash ht)])
        (hash-set new-ht k (f v)))
      (begin
        (for ([(k v) (in-hash ht)])
          (hash-set! new-ht k (f v)))
        new-ht)))

; compound structs
(require racket/sequence)
(define (in-compound-struct s)
  (define-values (stype _) (struct-info s))
  (let loop ([stype stype])
    (define-values (name init-field-cnt auto-field-cnt accessor-proc mutator-proc immutable-k-list super-type skipped?) (struct-type-info stype))
    (sequence-append
     (if super-type (loop super-type) '())
     (sequence-map (curry accessor-proc s) (in-range init-field-cnt)))))

(define (compound-struct-map f s)
  (define-values (stype _) (struct-info s))
  (define make (struct-type-make-constructor stype))
  (apply make
         (for/list ([e (in-compound-struct s)])
           (f e))))
(define (compound-struct-ormap f s)
  (for/or ([e (in-compound-struct s)])
    (f e)))
(define (compound-struct-andmap f s)
  (for/and ([e (in-compound-struct s)])
    (f e)))
(define (compound-struct-same? x y)
  (define-values (xtype xskipped?) (struct-info x))
  (define-values (ytype yskipped?) (struct-info y))
  (and ((struct-type-make-predicate xtype) y)
       ((struct-type-make-predicate ytype) x)))
(define (compound-struct-cmp x y =)
  (and (compound-struct-same? x y)
       (for/and ([ex (in-compound-struct x)]
                 [ey (in-compound-struct y)])
         (= ex ey))))

(define-struct logic-var
  (var-name)
  #:transparent
  #:property prop:procedure
  (lambda (v . args)
    ; Coerce (v arg ...) to a goal, equivalent to %fail if v is not a procedure of the correct arity
    (lambda (sk)
      (lambda (fk)
        (let ([pred (if (unbound-logic-var? v)
                        (fk (reason-formula 'todo-logic-var-app))
                        (logic-var-val* v))])
          (if (and (procedure? pred) (procedure-arity-includes? pred (length args)))
              (((apply pred args) sk) fk)
              (fk (reason-formula 'todo-logic-var-app2))))))))

(define *unbound* (string->uninterned-symbol "_"))

(define (logic-var-val r)
  (continuation-mark-set-first #f r *unbound* racklog-prompt-tag))

(define-syntax-rule (let/logic-var ([r v]) e ...)
  (begin
    (let ([sub-chp (choice-point curr-choice-point empty r v)])
      (add-sub-choice-point curr-choice-point sub-chp)
      (set! curr-choice-point sub-chp))
    (with-continuation-mark r v (begin e ...))))

(define _ make-logic-var)
(define (unbound-logic-var? r)
  (and (logic-var? r) (eq? (logic-var-val r) *unbound*)))

(define-struct frozen (val))
(define (freeze-ref r)
  (make-frozen r))
(define (thaw-frozen-ref r)
  (frozen-val (logic-var-val r)))
(define (frozen-logic-var? r)
  (frozen? (logic-var-val r)))

(define-syntax (uni-match stx)
  (syntax-case
      stx (? logic-var? cons mcons box vector? hash? compound-struct? atom? else)
    [(_ v
        [(? logic-var? lv) logic-var-expr ...]
        [(config-expr name val chld calc) cfg-var-expr ...]
        [(cons cl cr) cons-expr ...]
        [(mcons mcl mcr) mcons-expr ...]
        [(box bv) box-expr ...]
        [(? vector? vec) vector-expr ...]
        [(? hash? hash) hash-expr ...]
        [(? compound-struct? cs) cs-expr ...]
        [(? atom? x) atom-expr ...])
     (syntax/loc stx
       (match v
         [(? logic-var? lv) logic-var-expr ...]
         [(config-expr name val chld calc) cfg-var-expr ...]
         [(cons cl cr) cons-expr ...]
         [(mcons mcl mcr) mcons-expr ...]
         [(box bv) box-expr ...]
         [(? vector? vec) vector-expr ...]
         [(? hash? hash) hash-expr ...]
         [(? compound-struct? cs) cs-expr ...]
         [(? atom? x) atom-expr ...]))]
    [(_ v
        [(? logic-var? lv) logic-var-expr ...]
        [(config-expr name val chld calc) cfg-var-expr ...]
        [(cons cl cr) cons-expr ...]
        [(mcons mcl mcr) mcons-expr ...]
        [(box bv) box-expr ...]
        [(? vector? vec) vector-expr ...]
        [(? hash? hash) hash-expr ...]
        [(? compound-struct? cs) cs-expr ...]
        [(? atom? x) atom-expr ...]
        [else else-expr ...])
     (syntax/loc stx
       (match v
         [(? logic-var? lv) logic-var-expr ...]
         [(config-expr name val chld calc) cfg-var-expr ...]
         [(cons cl cr) cons-expr ...]
         [(mcons mcl mcr) mcons-expr ...]
         [(box bv) box-expr ...]
         [(? vector? vec) vector-expr ...]
         [(? hash? hash) hash-expr ...]
         [(? compound-struct? cs) cs-expr ...]
         [(? atom? x) atom-expr ...]
         [else else-expr ...]))]))

(define (logic-var-val* v)
  (uni-match
   v
   [(? logic-var? s)
    (cond [(unbound-logic-var? s) '_]
          [(frozen-logic-var? s) s]
          [else (logic-var-val* (logic-var-val s))])]
   [(config-expr name val chld calc) v]
   [(cons l r)
    (cons (logic-var-val* l) (logic-var-val* r))]
   [(mcons l r)
    (mcons (logic-var-val* l) (logic-var-val* r))]
   [(box v) (box (logic-var-val* v))]
   [(? vector? v)
    (vector-map logic-var-val* v)]
   [(? hash? v) (same-hash-map logic-var-val* v)]
   [(? compound-struct? v) (compound-struct-map logic-var-val* v)]
   [(? atom? s) s]))

(define use-occurs-check? (make-parameter #f))

(define (occurs-in? var term)
  (and (use-occurs-check?)
       (let loop ([term term])
         (or (eqv? var term)
             (uni-match
              term
              [(? logic-var? term)
               (cond [(unbound-logic-var? term) #f]
                     [(frozen-logic-var? term) #f]
                     [else (loop (logic-var-val term))])]
              [(config-expr name val chld calc) (loop val)]
              [(cons l r)
               (or (loop l) (loop r))]
              [(mcons l r)
               (or (loop l) (loop r))]
              [(box v) (loop v)]
              [(? vector? v)
               (for/or ([e (in-vector v)]) (loop e))]
              [(? hash? ht)
               (for/or ([(k v) (in-hash ht)]) (or (loop k) (loop v)))]
              [(? compound-struct? cs) (compound-struct-ormap loop cs)]
              [(? atom? x) #f])))))

(define (constant? x)
  (uni-match
   x
   [(? logic-var? x)
    (cond [(unbound-logic-var? x) #f]
          [(frozen-logic-var? x) #t]
          [else (constant? (logic-var-val x))])]
   [(config-expr name val chld calc) (constant? val)]
   [(cons l r) #f]
   [(mcons l r) #f]
   [(box v) #f]
   [(? vector? v) #f]
   [(? hash? v) #f]
   [(? compound-struct? v) #f]
   [(? atom? x) #t]))

(define (is-compound? x)
  (uni-match
   x
   [(? logic-var? x)
    (cond [(unbound-logic-var? x) #f]
          [(frozen-logic-var? x) #f]
          [else (is-compound? (logic-var-val x))])]
   [(config-expr name val chld calc) (is-compound? val)]
   [(cons l r) #t]
   [(mcons l r) #t]
   [(box v) #t]
   [(? vector? v) #t]
   [(? hash? v) #t]
   [(? compound-struct? v) #t]
   [(? atom? x) #f]))

(define (var? x)
  (uni-match
   x
   [(? logic-var? x)
    (cond [(unbound-logic-var? x) #t]
          [(frozen-logic-var? x) #f]
          [else (var? (logic-var-val x))])]
   [(config-expr name val chld calc) (var? val)]
   [(cons l r) (or (var? l) (var? r))]
   [(mcons l r) (or (var? l) (var? r))]
   [(box v) (var? v)]
   [(? vector? v)
    (for/or ([e (in-vector v)]) (var? e))]
   [(? hash? ht)
    (for/or ([(k v) (in-hash ht)]) (var? v))]
   [(? compound-struct? cs) (compound-struct-ormap var? cs)]
   [(? atom? x) #f]))

(define (freeze v)
  (define dict (make-hasheq))
  (define (loop s)
    (uni-match
     s
     [(? logic-var? s)
      (if (or (unbound-logic-var? s) (frozen-logic-var? s))
          (hash-ref! dict s
                     (lambda ()
                       (freeze-ref s)))
          (loop (logic-var-val s)))]
     [(config-expr name val chld calc) (config-expr name (loop val) chld calc)]
     [(cons l r)
      (cons (loop l) (loop r))]
     [(mcons l r)
      (mcons (loop l) (loop r))]
     [(box v) (box (loop v))]
     [(? vector? v)
      (vector-map loop v)]
     [(? hash? v)
      (same-hash-map loop v)]
     [(? compound-struct? cs) (compound-struct-map loop cs)]
     [(? atom? s) s]))
  (loop v))

(define (melt f)
  (uni-match
   f
   [(? logic-var? f)
    (cond [(unbound-logic-var? f) f]
          [(frozen-logic-var? f) (thaw-frozen-ref f)]
          [else (melt (logic-var-val f))])]
   [(config-expr name val chld calc) (config-expr name (melt val) chld calc)]
   [(cons l r)
    (cons (melt l) (melt r))]
   [(mcons l r)
    (mcons (melt l) (melt r))]
   [(box v) (box (melt v))]
   [(? vector? v)
    (vector-map melt v)]
   [(? hash? v)
    (same-hash-map melt v)]
   [(? compound-struct? cs) (compound-struct-map melt cs)]
   [(? atom? s) s]))

(define (melt-new f)
  (define dict (make-hasheq))
  (define (loop s)
    (uni-match
     s
     [(? logic-var? f)
      (cond [(unbound-logic-var? f) f]
            [(frozen-logic-var? f)
             (hash-ref! dict f (_ (gensym)))]
            [else (loop (logic-var-val f))])]
     [(config-expr name val chld calc) (config-expr name (loop val) chld calc)]
     [(cons l r)
      (cons (loop l) (loop r))]
     [(mcons l r)
      (mcons (loop l) (loop r))]
     [(box v) (box (loop v))]
     [(? vector? v)
      (vector-map loop v)]
     [(? hash? v)
      (same-hash-map loop v)]
     [(? compound-struct? cs)
      (compound-struct-map loop cs)]
     [(? atom? s) s]))
  (loop f))

(define (copy s)
  (let ([f (_ (gensym))])
    (let/logic-var ([f (freeze s)])
      (melt-new f))))

(define (ident? x y)
  (uni-match
   x
   [(? logic-var? x)
    (cond [(unbound-logic-var? x)
           (cond [(logic-var? y)
                  (cond [(unbound-logic-var? y) (eq? x y)]
                        [(frozen-logic-var? y) #f]
                        [else (ident? x (logic-var-val y))])]
                 [else #f])]
          [(frozen-logic-var? x)
           (cond [(logic-var? y)
                  (cond [(unbound-logic-var? y) #f]
                        [(frozen-logic-var? y) (eq? x y)]
                        [else (ident? x (logic-var-val y))])]
                 [else #f])]
          [else (ident? (logic-var-val x) y)])]
   [(config-expr x-name x-val x-chld x-calc)
    (uni-match
     y
     [(? logic-var? y)
      (cond [(unbound-logic-var? y) #f]
            [(frozen-logic-var? y) #f]
            [else (ident? x (logic-var-val y))])]
     [(config-expr y-name y-val y-chld y-calc) (ident? x-val y-val)]
     [(cons yl yr) (ident? x-val (cons yl yr))]
     [(mcons yl yr) (ident? x-val (mcons yl yr))]
     [(box yv) (ident? x-val (box yv))]
     [(? vector? y) (ident? x-val y)]
     [(? hash? y) (ident? x-val y)]
     [(? compound-struct? y) (ident? x-val y)]
     [(? atom? y) (ident? x-val y)])]
   [(cons xl xr)
    (uni-match
     y
     [(? logic-var? y)
      (cond [(unbound-logic-var? y) #f]
            [(frozen-logic-var? y) #f]
            [else (ident? x (logic-var-val y))])]
     [(config-expr name yv ycs yc) (ident? x yv)]
     [(cons yl yr)
      (and (ident? xl yl) (ident? xr yr))]
     [(mcons yl yr) #f]
     [(box v) #f]
     [(? vector? y) #f]
     [(? hash? y) #f]
     [(? compound-struct? y) #f]
     [(? atom? y) #f])]
   [(mcons xl xr)
    (uni-match
     y
     [(? logic-var? y)
      (cond [(unbound-logic-var? y) #f]
            [(frozen-logic-var? y) #f]
            [else (ident? x (logic-var-val y))])]
     [(config-expr name yv ycs yc) (ident? x yv)]
     [(cons yl yr) #f]
     [(mcons yl yr)
      (and (ident? xl yl) (ident? xr yr))]
     [(box v) #f]
     [(? vector? y) #f]
     [(? hash? y) #f]
     [(? compound-struct? y) #f]
     [(? atom? y) #f])]
   [(box xv)
    (uni-match
     y
     [(? logic-var? y)
      (cond [(unbound-logic-var? y) #f]
            [(frozen-logic-var? y) #f]
            [else (ident? x (logic-var-val y))])]
     [(config-expr name yv ycs yc) (ident? x yv)]
     [(cons yl yr) #f]
     [(mcons yl yr) #f]
     [(box yv) (ident? xv yv)]
     [(? vector? y) #f]
     [(? hash? y) #f]
     [(? compound-struct? y) #f]
     [(? atom? y) #f])]
   [(? vector? x)
    (uni-match
     y
     [(? logic-var? y)
      (cond [(unbound-logic-var? y) #f]
            [(frozen-logic-var? y) #f]
            [else (ident? x (logic-var-val y))])]
     [(config-expr name yv ycs yc) (ident? x yv)]
     [(cons yl yr) #f]
     [(mcons yl yr) #f]
     [(box v) #f]
     [(? vector? y)
      (if (= (vector-length x)
             (vector-length y))
          (for/and ([xe (in-vector x)]
                    [ye (in-vector y)])
            (ident? xe ye))
          #f)]
     [(? hash? y) #f]
     [(? compound-struct? y) #f]
     [(? atom? y) #f])]
   [(? hash? x)
    (uni-match
     y
     [(? logic-var? y)
      (cond [(unbound-logic-var? y) #f]
            [(frozen-logic-var? y) #f]
            [else (ident? x (logic-var-val y))])]
     [(config-expr name yv ycs yc) (ident? x yv)]
     [(cons yl yr) #f]
     [(mcons yl yr) #f]
     [(box v) #f]
     [(? vector? y) #f]
     [(? hash? y)
      (and (same-hash-kind? x y)
           (= (hash-count x) (hash-count y))
           (for/and ([(xk xv) (in-hash x)])
             ; XXX not using ident? for key comparison
             (and (hash-has-key? y xk)
                  (ident? xv (hash-ref y xk)))))]
     [(? compound-struct? y) #f]
     [(? atom? y) #f])]
   [(? compound-struct? x)
    (uni-match
     y
     [(? logic-var? y)
      (cond [(unbound-logic-var? y) #f]
            [(frozen-logic-var? y) #f]
            [else (ident? x (logic-var-val y))])]
     [(config-expr name yv ycs yc) (ident? x yv)]
     [(cons yl yr) #f]
     [(mcons yl yr) #f]
     [(box v) #f]
     [(? vector? y) #f]
     [(? hash? y) #f]
     [(? compound-struct? y)
      (compound-struct-cmp x y ident?)]
     [(? atom? y) #f])]
   [(? atom? x)
    (uni-match
     y
     [(? logic-var? y)
      (cond [(unbound-logic-var? y) #f]
            [(frozen-logic-var? y) #f]
            [else (ident? x (logic-var-val y))])]
     [(config-expr name yv ycs yc) (ident? x yv)]
     [(cons yl yr) #f]
     [(mcons yl yr) #f]
     [(box v) #f]
     [(? vector? y) #f]
     [(? hash? y) #f]
     [(? compound-struct? y) #f]
     [(? atom? y) (eqv? x y)])]))

(define ((unify t1 t2) sk)
  (lambda (fk sreas)
    ; note: t1, t2 may be config-exprs
    (define (unify1 t1 t2 next)
      (define t1-v (expr-value t1))
      (define t2-v (expr-value t2))
      (cond [(eqv? t1-v t2-v) (next)]
            [(logic-var? t1-v)
             (cond [(unbound-logic-var? t1-v)
                    (cond [(occurs-in? t1-v t2-v)
                           (fk (reason-formula 'occurs-in? t1 t2))]
                          [else
                           (let/logic-var ([t1-v t2])
                             (next))])]
                   [(frozen-logic-var? t1-v)
                    (cond [(logic-var? t2-v)
                           (cond [(unbound-logic-var? t2-v)
                                  (unify1 t2 t1 next)]
                                 [(frozen-logic-var? t2-v)
                                  (fk (neg-formula (reason-formula '= t1 t2)))]
                                 [else
                                  (unify1 t1 (logic-var-val t2-v) next)])]
                          [else (fk (neg-formula (reason-formula '= t1 t2)))])]
                   [else
                    (unify1 (logic-var-val t1-v) t2 next)])]
            [(logic-var? t2-v) (unify1 t2 t1 next)]

            [(and (pair? t1-v) (pair? t2-v))
             (unify1 (app-expr car t1) (app-expr car t2)
                     (λ () (unify1 (app-expr cdr t1) (app-expr cdr t2) next)))]
            [(and (mpair? t1-v) (mpair? t2-v))
             (unify1 (app-expr mcar t1) (app-expr mcar t2)
                     (λ () (unify1 (app-expr mcdr t1) (app-expr mcdr t2) next)))]
            [(and (box? t1-v) (box? t2-v))
             (unify1 (app-expr unbox t1) (app-expr unbox t2) next)]
            [(and (vector? t1-v) (vector? t2-v))
             (if (= (vector-length t1-v)
                    (vector-length t2-v))
                 (let loop ([v1s (app-expr sequence->stream (app-expr in-vector t1))]
                            [v2s (app-expr sequence->stream (app-expr in-vector t2))])
                   (if (expr-value (app-expr stream-empty? v1s))
                       (next)
                       (unify1 (app-expr stream-first v1s)
                               (app-expr stream-first v2s)
                               (λ () (loop (app-expr stream-rest v1s)
                                           (app-expr stream-rest v2s))))))
                 (fk (neg-formula (reason-formula '= (reason-formula 'vector-length t1)
                                                     (reason-formula 'vector-length t2)))))]
            [(and (hash? t1-v) (hash? t2-v))
             (if (and (same-hash-kind? t1-v t2-v)
                      (= (hash-count t1-v) (hash-count t2-v)))
                 (let loop ([xs (app-expr sequence->stream (app-expr in-hash-pairs t1))])
                   (if (expr-value (app-expr stream-empty? xs))
                       (next)
                       (let ([xk (app-expr car (app-expr stream-first xs))]
                             [xv (app-expr cdr (app-expr stream-first xs))])
                         (if (expr-value (app-expr hash-has-key? t2 xk))
                             (unify1 xv
                                     (app-expr hash-ref t2 xk)
                                     (λ () (loop (app-expr stream-rest xs))))
                             (fk (reason-formula 'and (reason-formula 'hash-has-key? t1 xk)
                                                      (neg-formula (reason-formula 'hash-has-key? t2 xk))))))))
                 (fk (reason-formula 'or (neg-formula (reason-formula 'same-hash-kind? t1 t2))
                                         (neg-formula (reason-formula '= (reason-formula 'hash-count t1)
                                                                         (reason-formula 'hash-count t2))))))]
            [(and (compound-struct? t1-v) (compound-struct? t2-v))
             (if (compound-struct-same? t1-v t2-v)
                 (let loop ([e1s (app-expr sequence->stream (app-expr in-compound-struct t1))]
                            [e2s (app-expr sequence->stream (app-expr in-compound-struct t2))])
                   (if (expr-value (app-expr stream-empty? e1s))
                       (next)
                       (unify1 (app-expr stream-first e1s)
                               (app-expr stream-first e2s)
                               (λ () (loop (app-expr stream-rest e1s)
                                           (app-expr stream-rest e2s))))))
                 (fk (neg-formula (reason-formula 'compound-struct-same? t1 t2))))]
            [(and (atom? t1-v) (atom? t2-v))
             (if (equal? t1-v t2-v) (next) (fk (neg-formula (reason-formula '= t1 t2))))]
            [else (fk (reason-formula 'todo-unify-else))])) ; TODO: reason here (it's because of constructor mismatch)
    (unify1 t1 t2 (λ (sreas2) (sk fk (reason-formula 'and sreas sreas2))))))

(define-syntax-rule (or* x f ...)
  (or (f x) ...))

(define (atomic-struct? v)
  (not (compound-struct? v)))
(define (compound-struct? v)
  (let-values ([(stype skipped?) (struct-info v)])
    (and stype (not skipped?)
         (let loop ([stype stype])
           (define-values (name init-field-cnt auto-field-cnt accessor-proc mutator-proc immutable-k-list super-type skipped?) (struct-type-info stype))
           (and (not skipped?) (or (not super-type) (loop super-type)))))))

(define (atom? x)
  (or* x boolean? number? string? bytes? char? symbol?
       regexp? pregexp? byte-regexp? byte-pregexp?
       keyword? null? procedure? void? generic-set?
       atomic-struct?))
(define (compound? x)
  (or* x pair? vector? mpair? box? hash? compound-struct?))

(define (answer-value? x)
  (uni-match
   x
   [(? logic-var? x) #f]
   [(config-expr name val chld calc) (answer-value? val)]
   [(cons l r) (and (answer-value? l) (answer-value? r))]
   [(mcons l r) (and (answer-value? l) (answer-value? r))]
   [(box v) (answer-value? v)]
   [(? vector? v) (for/and ([e (in-vector v)]) (answer-value? e))]
   [(? hash? ht) (for/and ([(k v) (in-hash ht)]) (and (answer-value? k) (answer-value? v)))]
   [(? compound-struct? cs) (compound-struct-andmap answer-value? cs)]
   [(? atom? x) #t]
   [else #f]))
(define answer?
  (match-lambda
    [#f #t]
    [(list (cons (? symbol?) (? answer-value?)) ...) #t]
    [_ #f]))
(define (unifiable? x)
  (uni-match
   x
   [(? logic-var? x) #t]
   [(config-expr name val chld calc) (unifiable? val)]
   [(cons l r) (and (unifiable? l) (unifiable? r))]
   [(mcons l r) (and (unifiable? l) (unifiable? r))]
   [(box v) (unifiable? v)]
   [(? vector? v) (for/and ([e (in-vector v)]) (unifiable? e))]
   [(? hash? ht) (for/and ([(k v) (in-hash ht)]) (and #;(answer-value? k) ; No constraint, but won't be used XXX
                                                      (unifiable? v)))]
   [(? compound-struct? cs) (compound-struct-andmap unifiable? cs)]
   [(? atom? x) #t]
   [else #f]))

; provenance recording
(struct choice-point
        (parent
         [children #:mutable]
         key value
         [reason #:mutable #:auto]
         [fail-return-point #:mutable #:auto]
         [choice-type #:mutable #:auto])
        #:auto-value #f
        #:transparent)
(define top-choice-point (choice-point #f empty #f #f))
(define curr-choice-point top-choice-point)
(define (reset-choice-points)
  (set! top-choice-point (choice-point #f empty #f #f))
  (set! curr-choice-point top-choice-point))
(define (add-sub-choice-point curr-chp sub-chp)
  (set-choice-point-children! curr-chp (cons sub-chp (choice-point-children curr-chp))))
(define (set-curr-choice-point new-chp)
  (set! curr-choice-point new-chp)
  new-chp)
(define (get-logic-var-name lvar)
  (if lvar
      (if (logic-var? lvar)
          (logic-var-var-name lvar)
          lvar)
      'top))
(define (set-as-fail-return-point! chp is-fail-return-point choice-type)
  (set-choice-point-fail-return-point! chp is-fail-return-point)
  (set-choice-point-choice-type! chp choice-type))
(define (print-hrule)
  (printf "--------------------------\n"))
(define (print-search-tree-from-node choice-node indent var-mapping)
  (printf "~a(~a: ~a)~a~a\n"
          indent
          (get-logic-var-name (choice-point-key choice-node))
          (if (config-expr? (choice-point-value choice-node))
              (config-expr->string (choice-point-value choice-node))
              (get-logic-var-name (choice-point-value choice-node)))
          (if (choice-point-fail-return-point choice-node)
              " <choice>"
              "")
          (if (choice-point-choice-type choice-node)
              (format " <type:~a>" (choice-point-choice-type choice-node))
              ""))
  (map (λ (child) (print-search-tree-from-node child (string-append "| " indent) var-mapping))
       (reverse (choice-point-children choice-node))))
(define (print-search-tree var-mapping)
  (print-hrule)
  (print-search-tree-from-node top-choice-point "" var-mapping)
  (print-hrule))

; failure reasons
(struct reason-formula (op args) #:transparent #:name formula #:constructor-name make-reason-formula)
(define false-formula (make-reason-formula 'false empty))
(define true-formula (make-reason-formula 'true empty))
(define (is-false-formula? formula) (equal? formula false-formula))
(define (is-true-formula? formula) (equal? formula true-formula))
(define (and-reasons r-list)
  (make-reason-formula 'and r-list))
(define (or-reasons r-list)
  (make-reason-formula 'or r-list))
(define (reason-formula op . args)
  (make-reason-formula op args))
(define (get-child-reasons chp)
  (map choice-point-reason (choice-point-children chp)))
(define (neg-formula reason)
  (reason-formula 'not reason))
(define (simplify-reason reason)
  (if (not (reason-formula? reason)) reason
    (let ()
      (define simple-subformulas (map simplify-reason (reason-formula-args reason)))
      (match (reason-formula-op reason)
        ['and
         (let ([non-true-sfs (filter (negate is-true-formula?) simple-subformulas)])
           (cond
             [(empty? non-true-sfs) true-formula]
             [(= 1 (length non-true-sfs)) (first non-true-sfs)]
             [(ormap is-false-formula? non-true-sfs) false-formula]
             [else (make-reason-formula 'and non-true-sfs)]))]
        ['or
         (let ([non-false-sfs (filter (negate is-false-formula?) simple-subformulas)])
           (cond
             [(empty? non-false-sfs) false-formula]
             [(= 1 (length non-false-sfs)) (first non-false-sfs)]
             [(ormap is-true-formula? non-false-sfs) true-formula]
             [else (make-reason-formula 'or non-false-sfs)]))]
        ['not
         (cond
          [(not (= (length simple-subformulas) 1)) (error "not must have exactly one subformula")]
          [(is-true-formula? (first simple-subformulas)) false-formula]
          [(is-false-formula? (first simple-subformulas)) true-formula]
          [else (make-reason-formula 'not simple-subformulas)])]
        ['=
         (cond
          [(not (= (length simple-subformulas) 2)) (error "= must have exactly two subformulas")]
          [(equal? (first simple-subformulas) (second simple-subformulas)) true-formula]
          [(andmap (negate config-expr?) simple-subformulas) false-formula]
          [(equal? (first simple-subformulas) #t) (second simple-subformulas)]
          [(equal? (first simple-subformulas) #f) (neg-formula (second simple-subformulas))]
          [(equal? (second simple-subformulas) #t) (first simple-subformulas)]
          [(equal? (second simple-subformulas) #f) (neg-formula (first simple-subformulas))]
          [else (make-reason-formula '= simple-subformulas)])]
        [else (make-reason-formula (reason-formula-op reason) simple-subformulas)]))))
(define (reason->string var-mapping reason)
  (define sub-formula-strs
    (map (λ (sf) (cond [(reason-formula? sf) (reason->string var-mapping sf)]
                       [(logic-var? sf) (format "<lv:~a>" (logic-var-var-name sf))]
                       [(config-expr? sf) (config-expr->string sf)]
                       [else (format "~a" sf)]))
         (reason-formula-args reason)))
  (format "(~a~a)"
          (reason-formula-op reason)
          (foldl (λ (sfs res) (format " ~a~a" sfs res)) "" sub-formula-strs)))

(define (print-failure-reason var-mapping reason)
  (printf "~a\n" (reason->string var-mapping (simplify-reason reason)))
  (print-hrule))

; config vars
(struct config-expr (name value children calculator) #:transparent)
(define (format-list lst)
  (apply format (string-join (make-list (length lst) "~a") " ") lst))
(define (config-expr->string ce)
  (cond
   [(config-expr? ce)
    (begin
      (define children (map config-expr->string (config-expr-children ce)))
      (define name (config-expr-name ce))
      (if (empty? children)
        (format "<cv:~a>" name)
        (format "(~a~a)"
                (if (or (equal? name '#%app) (equal? name '#%plain-app)) "" (format "~a " name))
                (format-list children))))]
   [(procedure? ce) (object-name ce)]
   [else ce]))

(define (expr-name expr)
  (cond
   [(config-expr? expr) (config-expr-name expr)]
   [(procedure? expr) (object-name expr)]
   [else expr]))
(define (expr-value expr)
  (if (config-expr? expr)
      (config-expr-value expr)
      expr))

(define-syntax (build-expr stx)
  (syntax-case stx ()
    [(_ op child ...)
     (with-syntax ([(calc-param ...) (generate-temporaries #'(child ...))])
       #'(if (ormap config-expr? (list child ...))
             (config-expr
               'op
               (op (expr-value child) ...)
               (list child ...)
               (λ (calc-param ...) (op calc-param ...)))
             (op child ...)))]))

(define-syntax-rule (app-expr child ...)
  (build-expr #%app child ...))