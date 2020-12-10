#lang racket/base
(provide (all-defined-out))

; struct for recording provenance
(struct choice-point
        (parent
         [children #:mutable]
         key value
         [cut-failure #:mutable #:auto]
         [fail-return-point #:mutable #:auto]
         [choice-type #:mutable #:auto])
        #:auto-value #f)
(define top-choice-point (choice-point #f empty #f #f))
(define curr-choice-point top-choice-point)
(define (reset-choice-points)
  (set! top-choice-point (choice-point #f empty #f #f))
  (set! curr-choice-point top-choice-point))
(define (add-sub-choice-point curr-chp sub-chp)
  #;(printf "moving down: <~a:~a> -> <~a:~a>\n"
         (if (choice-point-key curr-chp) (logic-var-var-name (choice-point-key curr-chp)) 'top)
         (if (logic-var? (choice-point-value curr-chp)) (if (choice-point-value curr-chp) (logic-var-var-name (choice-point-value curr-chp)) 'top) 'value)
         (if (choice-point-key sub-chp) (logic-var-var-name (choice-point-key sub-chp)) 'top)
         (if (logic-var? (choice-point-value sub-chp)) (if (choice-point-value sub-chp) (logic-var-var-name (choice-point-value sub-chp)) 'top) 'value))
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
(define (print-provenance-from-node choice-node indent var-mapping)
  (printf "~a(~a: ~a)~a~a\n"
          indent
          (get-logic-var-name (choice-point-key choice-node))
          (get-logic-var-name (choice-point-value choice-node))
          (if (choice-point-fail-return-point choice-node)
              " #<fail-return-point>"
              "")
          (if (choice-point-choice-type choice-node)
              (format " #<type:~a>" (choice-point-choice-type choice-node))
              ""))
          ;(choice-point-success choice-node))
  (map (λ (child) (print-provenance-from-node child (string-append "| " indent) var-mapping))
       (reverse (choice-point-children choice-node))))
(define (print-provenance var-mapping)
  (printf "--------------------------\n")
  (print-provenance-from-node top-choice-point "" var-mapping)
  (printf "--------------------------\n"))