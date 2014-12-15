;-----------------------------------------------------------------------------------------
; Multiplying elements of a vector
;-----------------------------------------------------------------------------------------

; a simple implementation with letrec
(define product
  (lambda (v)
    (letrec ([loop (lambda (v init-acc)
                     (cond
                       [(null? v) init-acc]
                       [else (loop (cdr v) (* (car v) init-acc))]))])
      (loop v 1))))

; now let's trace how many times we invoke the multiplication
; to do this let's define a function to do the multiplication
(define asterisk
  (trace-lambda * (x y)
    (* x y)))

; now change the original definition to use asterisk instead of built-in *
(define product2
  (lambda (v)
    (letrec ([loop (lambda (v init-acc)
                     (cond
                       [(null? v) init-acc]
                       [else (loop (cdr v) (asterisk (car v) init-acc))]))])
      (loop v 1))))

; great! we saw that multiplication is wasted 6 times when our vector is (1 2 3 4 0 5)
; let's see if we can improve this by adding a zero check for the (car v)
(define product3
  (lambda (v)
    (letrec ([loop (lambda (v init-acc)
                     (cond
                       [(null? v) init-acc]
                       [(zero? (car v)) 0]
                       [else (loop (cdr v) (asterisk (car v) init-acc))]))])
      (loop v 1))))

; nice, we reduced the number calls to asterisk to 4
; what would happen if we forget all the crap and use the direct style to implement this?
(define product4
  (lambda (v)
    (cond
      [(null? v) 1]
      [else (asterisk (car v) (product4 (cdr v)))])))

; same story as in product2, i.e. wasted 6 asterisk calls
; let's see the effect or zero check for (car v)
(define product5
  (lambda (v)
    (cond
      [(null? v) 1]
      [(zero? (car v)) 0]
      [else (asterisk (car v) (product5 (cdr v)))])))

; again the same story as in product3, i.e. wasted 4 asterisk calls
; also the calculation happened in the reverse order w.r.t that of product3
; now, let's try to CPS this and see
(define product6-cps
  (lambda (v k)
    (cond
      [(null? v) (k 1)]
      [(zero? (car v)) (k 0)]
      [else (product6-cps (cdr v) (lambda (w) (asterisk-cps (car v) w k)))])))

(define asterisk-cps
  (trace-lambda * (m n k)
    (k (* m n))))

; okay, this style cps simply wasted 4 asterisk calls
; the order was reverse as same as in product5
; let's try to write a cps version where we remember the initial continuation
; to be used for our zero case and a use a growing continuation for other work
; but I want to first check k-grow for the zero case as well
(define product7-cps
  (lambda (v k-init)
    (letrec ([loop (lambda (v k-grow)
                     (cond
                       [(null? v) (k-grow 1)]
                       [(zero? (car v)) (k-grow 0)]
                       [else (loop (cdr v) (lambda (w) (asterisk-cps (car v) w k-grow)))]))])
      (loop v k-init))))

; aha! as I expected it too wasted 4 asterisk calls :)
; it's time to use k-init to avoid this in zero check
(define product8-cps
  (lambda (v k-init)
    (letrec ([loop (trace-lambda cps-loop (v k-grow)
                     (cond
                       [(null? v) (k-grow 1)]
                       [(zero? (car v)) (k-init 0)]
                       [else (loop (cdr v) (lambda (w) (asterisk-cps (car v) w k-grow)))]))])
      (loop v k-init))))

; wonderful! as expected this time it didn't call the asterisk
; it's now time to play with call/cc
; I will use the good-old direct style with call/cc
; hmm I think i know the reason for this thing below, i.e. everytime we call the product9 a completely new thing
; pops up
(define product9
  (lambda (v)
    (call/cc
      (lambda (k-init)
        (cond
          [(null? v) 1]
          [(zero? (car v)) (k-init 0)]
          [else (asterisk (car v) (product9 (cdr v)))])))))

; let's see if what I am thinking is correct, i.e. this should show some fat stack
(define product10
  (lambda (v)
    (call/cc
      (lambda (k-init)
        (letrec ([loop (trace-lambda loop (v)
                         (cond
                           [(null? v) 1]
                           [(zero? (car v)) (k-init 0)]
                           [else (asterisk (car v) (loop (cdr v)))]))])
          (loop v))))))

; yep, it showed a fat stack
; let's dig down deep into the following usual cps version
(define product11
  (lambda (v)
    (call/cc
      (lambda (k-init)
        (letrec ([loop (trace-lambda loop (v k-grow)
                         (cond
                           [(null? v) (k-grow 1)]
                           [(zero? (car v)) (k-init 0)]
                           [else (loop (cdr v) (lambda (w) (k-grow (* (car v) w))))]))])
          (loop v k-init))))))

; yea, this is a flat stack
; let's see if we can get the same out of product10 with another call/cc
; this seems to have some weirdness
(define product12
  (lambda (v)
    (call/cc
      (lambda (k-init)
        (letrec ([loop (trace-lambda loop (v k)
                         (cond
                           [(null? v) (k 1)]
                           [(zero? (car v)) (k-init 0)]
                           [else (asterisk (car v) (call/cc (lambda (t) (loop (cdr v) t))))]))])
          (loop v k-init))))))
                           


                

                     