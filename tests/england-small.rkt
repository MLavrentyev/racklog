#lang racket

(require racklog
         rackunit)

;The following is a simple database about a certain family in England.
;Should be a piece of cake, but given here so that you can hone
;your ability to read the syntax.

;This file is written using `%rel' for a more Prolog-like syntax.
;The file england2.scm uses a Scheme-like syntax.

(define %male
  (%rel ()
    (('philip)) (('charles))))

(define %female
  (%rel ()))

(define %husband-of
  (%rel ()))

(define %wife-of
  (%rel (w h)
    ((w h) (%husband-of h w))))

(define %married-to
  (%rel (x y)
    ((x y) (%husband-of x y))
    ((x y) (%wife-of x y))))

(define %father-of
  (%rel ()
   (('philip 'charles))))

(define %mother-of
  (%rel (m c f)
    ((m c) (%wife-of m f) (%father-of f c))))

(define %child-of
  (%rel (c p)
    ((c p) (%father-of p c))
    ((c p) (%mother-of p c))))

(define %parent-of
  (%rel (p c)
    ((p c) (%child-of c p))))

(define %brother-of
  (%rel (b x f)
    ((b x) (%male b) (%father-of f b) (%father-of f x) (%/= b x))))

; example with proper negation
(define %married-no-children
  (%rel (w h c)
    ((w) (%husband-of h w) (%not (%father-of h c)))))

; example with choice between relation definitions
(define %no-children
  (%rel (w h c)
    ((w) (%married-no-children w))
    ((w) (%female w) (%not (%married-to w h)))))

; example with unification order =/= order of introduction (doesn't seem to be possible)
(define %parent-of-brother-sister
  (%rel (pbs mc fc)
    ((pbs) (%brother-of mc fc) (%parent-of pbs fc) (%female fc))))

; example with negated recursion
(define %person
  (%rel (p)
    ((p) (%male p))
    ((p) (%female p))))

(define %descendant-of
  (%rel (d a i)
    ((d a) (%child-of d a))
    ((d a) (%child-of d i) (%descendant-of i a))))

(define %not-descendant-of
  (%rel (nd na)
    ((nd na) (%person nd) (%not (%descendant-of nd na)))))

; example with a configuration variable
(define generations 2)

(define %nth-descendant-of
  (%rel (d a n n-1 pd)
    ((a a 0))
    ((d a n) (%is n-1 (- n 1)) (%parent-of pd d) (%nth-descendant-of pd a n-1))))

(define %recent-descendant-of
  (%rel (d a)
    ((d a) (%nth-descendant-of d a generations))))
