#lang racket

(require racklog
         rackunit)

;The following is a simple database about a certain family in England.
;Should be a piece of cake, but given here so that you can hone
;your ability to read the syntax.

;This file is written using `%rel' for a more Prolog-like syntax.
;The file england2.scm uses a Scheme-like syntax.

; Fictional world with simple transitivity (no wife relations, etc.)

(define %male
  (%rel ()
    (('philip)) (('charles))))

(define %father-of
  (%rel ()
   (('philip 'charles))))

(define %child-of
  (%rel (c p)
    ((c p) (%father-of p c))))

; example with a configuration variable
(define generations 2)

(define %nth-descendant-of
  (%rel (d a n n-1 pd)
    ((a a 0))       ; TODO: change to check/fail for <= 0
    ((d a n) (%is n-1 (- n 1)) (%father-of pd d) (%nth-descendant-of pd a n-1))))

(define %recent-descendant-of
  (%rel (d a)
    ((d a) (%nth-descendant-of d a generations))))
