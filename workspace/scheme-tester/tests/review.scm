;----------------------------------------------------------------------------------------------------------
; A simple function to reverse a list
(define reverse
  (lambda (l)
    (cond
      [(null? l) '()]
      [(pair? (car l)) (append (reverse (cdr l)) (cons (reverse (car l)) '()))]
      [else (append (reverse (cdr l)) (cons (car l) '()))])))
;----------------------------------------------------------------------------------------------------------

(define fac
  (lambda (n)
    (if (zero? n)
      1
      (* n (fac (sub1 n))))))

; Registerizing the direct version (instead of the CPSed version)
(define *n*)

(define fac-reg
  (lambda () ; remember we had n
    (if (zero? *n*)
      1
      (let ([n *n*]) ; we need to get the current value of *n* register to n. May be this is what dereferencing means
        (begin
          (set! *n* (sub1 n))
          (* n (fac-reg)))))))

(define fac-main
  (lambda ()
    (begin
      (set! *n* 6)
      (fac-reg))))
;----------------------------------------------------------------------------------------------------------

; I will play with rem8 making it direct, CPSed, registerized, reg and tramped using PC, pure trampolined

; Direct rem8
(define rem8
  (lambda (l)
    (cond
      [(null? l) '()]
      [(pair? (car l)) (cons (rem8 (car l)) (rem8 (cdr l)))]
      [(eq? (car l) 8) (rem8 (cdr l))]
      [else (cons (car l) (rem8 (cdr l)))])))


; CPSed rem8, i.e. rem8-cps
(define rem8-cps
  (lambda (l k)
    (cond
      [(null? l) (k '())]
      [(pair? (car l)) (rem8-cps (car l) (lambda (u) (rem8-cps (cdr l) (lambda (w) (k (cons u w))))))]
      [(eq? (car l) 8) (rem8-cps (cdr l) k)]
      [else (rem8-cps (cdr l) (lambda (u) (k (cons (car l) u))))])))


; Registerized rem8-cps, i.e. rem8-cps-reg
; Note. I didn't use R.I. w.r.t. continuations
(define *l* *)
(define *k* *)
(define rem8-cps-reg
  (lambda () ; remember we had l and k
    (cond
      [(null? *l*) (begin
                     (set! *k* *k*) ; useless
                     (set! *l* '()) ; useless
                     (*k* *l*))]
      [(pair? (car *l*)) (begin
                           (set! *k* (let ([l *l*] [k *k*]) ; if I used R.I. constructors then the current values will
                                                            ; will be captured there removing the need for 'let'
                                       (lambda (u) (begin
                                                     (set! *k* (lambda (w) (k (cons u w))))
                                                     (set! *l* (cdr l))
                                                     (rem8-cps-reg)))))
                           (set! *l* (car *l*))
                           (rem8-cps-reg))]
      [(eq? (car *l*) 8) (begin
                           (set! *k* *k*) ; useless
                           (set! *l* (cdr *l*))
                           (rem8-cps-reg))]
      [else (begin
              (set! *k* (let ([k *k*] [l *l*]) ; if I used R.I. constructors then the current values will
                                               ; will be captured there removing the need for 'let'
                          (lambda (u) (k (cons (car l) u)))))
              (set! *l* (cdr *l*))
              (rem8-cps-reg))])))

(define rem8-cps-reg-main
  (lambda ()
    (begin
      (set! *k* (lambda (x) x))
      (set! *l* '((1 8) 3 8))
      (rem8-cps-reg))))


; Now, let's trampoline this version using a PC
(define *pc*)

(define rem8-cps-reg-tramp
  (lambda () ; remember we had l and k
    (cond
      [(null? *l*) (begin
                     (set! *k* *k*) ; useless
                     (set! *l* '()) ; useless
                     (set! *pc* (lambda () (*k* *l*))))]
      [(pair? (car *l*)) (begin
                           (set! *k* (let ([l *l*] [k *k*]) ; if I used R.I. constructors then the current values will
                                                            ; will be captured there removing the need for 'let'
                                       (lambda (u) (begin
                                                     (set! *k* (lambda (w) (k (cons u w))))
                                                     (set! *l* (cdr l))
                                                     (set! *pc* rem8-cps-reg-tramp)))))
                           (set! *l* (car *l*))
                           (set! *pc* rem8-cps-reg-tramp))]
      [(eq? (car *l*) 8) (begin
                           (set! *k* *k*) ; useless
                           (set! *l* (cdr *l*))
                           (set! *pc* rem8-cps-reg-tramp))]
      [else (begin
              (set! *k* (let ([k *k*] [l *l*]) ; if I used R.I. constructors then the current values will
                                               ; will be captured there removing the need for 'let'
                          (lambda (u) (k (cons (car l) u)))))
              (set! *l* (cdr *l*))
              (set! *pc* rem8-cps-reg-tramp))])))

(define rem8-cps-reg-tramp-main
  (lambda ()
    (call/cc (lambda (exit)
               (begin
                 (set! *k* (lambda (x) (exit x)))
                 (set! *l* '((1 8) 3 8))
                 (set! *pc* rem8-cps-reg-tramp)
                 (trampoline))))))

(define pc-trampoline
  (lambda ()
    (begin
      (*pc*)
      (pc-trampoline))))


; Now let's trampoline the just CPSed version
(define rem8-cps-tramp
  (lambda (l k)
    (cond
      [(null? l) (lambda () (k '()))]
      [(pair? (car l)) (lambda () (rem8-cps-tramp (car l) (lambda (u) (rem8-cps-tramp (cdr l) (lambda (w) (k (cons u w)))))))]
      [(eq? (car l) 8) (lambda () (rem8-cps-tramp (cdr l) k))]
      [else (lambda () (rem8-cps-tramp (cdr l) (lambda (u) (k (cons (car l) u)))))])))

(define rem8-cps-tramp-main
  (lambda()
    (call/cc (lambda (exit)
               (trampoline (rem8-cps-tramp '((1 (8) 3 8) (8)) exit))))))

(define trampoline
  (lambda (th)
    (trampoline (th))))
;----------------------------------------------------------------------------------------------------------

; Next I will move on to ParantheC

; To start with here's the CPSed version of rem8
; CPSed rem8, i.e. rem8-cps
(define rem8-cps
  (lambda (l k)
    (cond
      [(null? l) (k '())]
      [(pair? (car l)) (rem8-cps (car l) (lambda (u) (rem8-cps (cdr l) (lambda (w) (k (cons u w))))))]
      [(eq? (car l) 8) (rem8-cps (cdr l) k)]
      [else (rem8-cps (cdr l) (lambda (u) (k (cons (car l) u))))])))

; R.I. version
(define rem8-cps-ri
  (lambda (l k)
    (cond
      [(null? l) (apply-k k '())]
      [(pair? (car l)) (rem8-cps (car l) (outer-k k l))]
      [(eq? (car l) 8) (rem8-cps (cdr l) k)]
      [else (rem8-cps (cdr l) (inner-k k (car l)))])))

; continuation observers
(define apply-k
  (lambda (k v)
    (k v)))

; continuation constructors
(define inner-k
  (lambda (k u)
    (lambda (w) (k (cons u w)))))

(define outer-k
  (lambda (k l)
    (lambda (u) (rem8-cps (cdr l) (inner-k k u)))))

; Now let's remove the higher order functions from observers and constructors using define-union and union-case

; define-union continuation constructors
(define-union kt
  (empty_k)
  (inner_k k u)
  (outer_k k l))

; R.I. CPSed version w/ union types
(define rem8-cps-ri2
  (lambda (l k)
    (cond
      [(null? l) (apply-k2 k '())]
      [(pair? (car l)) (rem8-cps-ri2 (car l) (kt_outer_k k l))]
      [(eq? (car l) 8) (rem8-cps-ri2 (cdr l) k)]
      [else (rem8-cps-ri2 (cdr l) (kt_inner_k k (car l)))])))

(define apply-k2
  (lambda (k^ v)
    (union-case k^ kt
      [(empty_k) v]
      [(outer_k k l) (rem8-cps-ri2 (cdr l) (kt_inner_k k v))]
      [(inner_k k u) (apply-k2 k (cons u v))])))
      




    
  




  
 
  
