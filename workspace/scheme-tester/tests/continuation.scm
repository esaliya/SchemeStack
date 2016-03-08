;the normal fib
(define fib
  (lambda (n)
    (cond
      [(zero? n) 0]
      [(= n 1) 1]
      [else (+ (fib (sub1 n)) (fib (sub1 (sub1 n))))])))

(define fib-cps
  (lambda (n k)
    (cond
      [(zero? n) (k 0)]
      [(zero? (sub1 n)) (k 1)]
      [else (fib-cps (sub1 n) (lambda (v) (fib-cps (sub1 (sub1 n)) (lambda (x) (k (+ v x))))))])))  

(define fac
  (lambda (n)
    (cond
      [(zero? n) 1]
      [else (* n (fac (sub1 n)))])))

(define fac-cps
  (lambda (n k)
    (cond
      [(zero? n) (k 1)]
      [else (fac-cps (sub1 n) (lambda (v) (k(* n v))))])))

(define map
  (lambda (f l)
    (cond
      [(null? l) '()]
      [else (cons (f (car l)) (map f (cdr l)))])))

(define map-cps
  (lambda (f l k)
    (cond
      [(null? l) (k '())]
      [else (map-cps f (cdr l) (trace-lambda new-k (v) (k (cons (f (car l)) v))))])))
;-----------------------------------------------------------------------------------------
; cps -> cps -> cps ... test
;-----------------------------------------------------------------------------------------
    
(define !
  (lambda (n)
    (if (zero? n)
      1
      (* n (! (sub1 n))))))

(define !^
  (lambda (n k)
    (if (zero? n)
      (k 1)
      (!^ (sub1 n) (lambda (v) (k (* n v)))))))

(define !^^
    (lambda (n c k)
        (if (zero? n)
              (c 1 k)
                    (!^^ (sub1 n) (lambda (v k) (c (* n v) k )) k))))

; test this with
; (!^^ 5 (lambda (v k)(k v)) (lambda(q) q))
; it works :-)


; let's think we want something like
; (!^^^ 5  (lambda (v2 k1 k0) (k1 v2 k0)) (lambda (v1 k0) (k0 v1)) (lambda (v0) v0))
(define !^^^
  (lambda (n k2 k1 k0)
    (cond
      [(zero? n) (k2 1 k1 k0)]
      [else (!^^^ (sub1 n) (lambda (v2^ k1^ k0^) (k2 (* n v2^) k1 k0)) k1 k0)])))
;-----------------------------------------------------------------------------------------
; some tests on call/cc

(define (f return)
  (return 2))

(define func
    (lambda ()
      (+ 1 (call/cc (lambda (k) (set! cont k) 2)))))

; (func) => 3
; (cont 4) => 5

; a good example, output is 31
(+ 1 (call/cc (lambda (k) 20 (k 30) 40)))

; another good one from wiki (http://en.wikipedia.org/wiki/Continuation)
 (define the-continuation #f)
 
 (define (test)
   (let ((i 0))
     ; call/cc calls its first function argument, passing 
     ; a continuation variable representing this point in
     ; the program as the argument to that function. 
     ;
     ; In this case, the function argument assigns that
     ; continuation to the variable the-continuation. 
     ;
     (call/cc (lambda (k) (set! the-continuation k)))
     ;
     ; The next time the-continuation is called, we start here.
     (set! i (+ i 1))
     i))

 ;;> (test)
 ;;1
 ;;> (the-continuation)
 ;;2
 ;;> (the-continuation)
 ;;3
 ;;> (define another-continuation the-continuation) ; stores the current continuation (which will print 4 next) away
 ;;> (test) ; resets the-continuation
 ;;1
 ;;> (the-continuation)
 ;;2
 ;;> (another-continuation) ; uses the previously stored continuation
 ;;4
 
 ;-----------------------------------------------------------------------------------------
 ; an attempt to use call/cc with good-old stuff, but these may not resemble a cps version
 ;-----------------------------------------------------------------------------------------
 
; good-old fac
;; (define fac
;;  (lambda (n)
;;    (cond
;;      [(zero? n) 1]
;;      [else (* n (fac (sub1 n)))])))
 
; this cont and set! things were added later 
(define cont #f)

(define fac-callcc
  (lambda (n)
    (cond
      [(zero? n) 1]
      [else (* n (call/cc (lambda (k) (if (not cont) (set! cont k)) (k (fac-callcc (sub1 n))))))])))

; call (fac-callcc 4) => 24
; now call (cont 3) => 12

;-----------------------------------------------------------------------------------------
"another small call/cc test"
;;> (+ (call/cc (lambda (k) (k 1))) 3)
;;4
;;> (+ (call/cc (lambda (k) (set! cont k)(k 1))) 3)
;;4
;;> (cont 2)
;;5
;;> (let ([x 2])
;;    (set! x 3)
;;    (call/cc (lambda (k) (set! cont k)))
;;    x)
;;3
;;> (cont)
;;3
;;> (+ (call/cc (lambda (k) (set! cont k)(k 1))) 3)
;;4
;;> (cont 2)
;;5
;;> (let ([x 2])
;;    (set! x 3)
;;    (call/cc (lambda (k) (cont 3)))
;;    x)
;;6
;;> (let ([x 2])
;;    (set! x 3)
;;    (call/cc (lambda (k) (k 7)))
;;    x)
;;3
;;> (let ([x 2])
;;    (set! x 3)
;;    (set! x (call/cc (lambda (k) (cont 5))))
;;    x)
;;8
;;> 
;; 

;---------------------------------------------------------
; Hmm, how does a continuation do something like  in ******* ===== hmm, I think I understand this when
;                                                                  thinking related with 

;;> (+ 1 (call/cc (lambda (k) (set! cont k) 2)))
;;|(call/cc #<procedure>)
;;|2
;;|(+ 1 2)
;;|3
;;3
;;> (cont 3)
;;|3
;;|(+ 1 3)
;;|4
;;4
;;> (trace cont)
;;(cont)
;;> (add (call/cc (trace-lambda procedure (k) (cont 5))) 7)
;;|(call/cc #<procedure>)
;;|(procedure #<system continuation>)
;;|(cont 5)
;;|5                         <===================******
;;|(+ 1 5)
;;|6
;;6








