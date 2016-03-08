; the direct style fac
(define fac
  (lambda (n)
    (call/cc (lambda (k) (set! cont k)))
    (cond 
      [(zero? n) 1]
      [else (* n (fac (sub1 n)))])))

; cps style
(define fac-cps
  (lambda (n k)
    (cond
      [(zero? n) (begin (set! cont-cps k) (k 1))]
      [else (fac-cps (sub1 n) (lambda (v) (k (* n v))))])))

; (fac-cps 5 empty-k)   => 120
; (+ 1 (cont-cps 1))    => 121

; with call/cc 
(define fac-cc
  (lambda (n)
    (cond
      [(zero? n) (call/cc (lambda (k) (set! cont-cc k) (k 1)))]
      [else (* n (fac-cc (sub1 n)))])))

; (fac-cps 5)           => 120
; (+ 1 (cont-cc 1))     => 120 : this is what we expected
; But, my question is if continuations are represented as functions then how
; will they not return to the caller?

; My answer for this:
;--------------------
; "return to the caller", what is return? I think it is the first entry into the
; current continuation pile (think of a nested lambdas representing the 
; current continuation). So when evaluating (a b) if 'a evaluates to what
; is identified as a procedure then scheme will evaluate its body against
; an extended environment containing 'b and then will call the current 
; continuation pile with the result. This is why we get 121 in the first case.
; second case, if 'a evaluates to what is identified as a continuation then 
; scheme will evaluate the body against the same extended environment, but will
; not apply the current continuation pile, instead it may apply it to something
; like (lambda (x) x). 

; this is not an exact clarification as I don't know how actually scheme works,
; but my point is when evaluating something of the form (a b) scheme should
; identify whether 'a is a procedure or a continuation. Am I right here? 
; 
; Ans.Um, noop. Scheme doesn't have to distinguish. See how you made call/cc work
; in the interpreter (see lec notes). That's the same way. To understand this
; first try to CPS the original interpreter without any helpers, i.e. just using
; higher order functions
; 

(define empty-k
  (lambda (x)
    x))