; This is totally dedicated in converting rem8-cps-ri2 into C

; introduce registers
(define-registers l k k^ v)
(define-program-counter pc)


; define-union continuation constructors
(define-union kt
  (empty_k dismount) ; Note. dismount is added here
  (inner_k k u)
  (outer_k k l))

;;; R.I. CPSed version w/ union types
;;(define rem8-cps-ri3
;;  (lambda () ; remember we had l and k
;;    (cond
;;      [(null? l) (begin
;;                   (set! k k) ; useless 
;;                   (set! v '())
;;                   (set! pc apply-k3))]
;;                   
;;      [(pair? (car l)) (begin
;;                         (set! k (kt_outer_k k l))
;;                         (set! l (car l))
;;                         (set! pc rem8-cps-ri3))]
;;                         
;;      [(eq? (car l) 8) (begin
;;                         (set! k k) ; useless
;;                         (set! l (cdr l))
;;                         (set! pc rem8-cps-ri3))]
;;                         
;;      [else (begin
;;              (set! k (kt_inner_k k (car l)))
;;              (set! l (cdr l))
;;              (set! pc rem8-cps-ri3))])))

;;(define apply-k3
;;  (lambda () ; remember we had k and v
;;    (union-case k kt
;;      [(empty_k dismount) (dismount-trampoline dismount)]
;;      [(outer_k k^ l) (begin
;;                        (set! k (kt_inner_k k^ v))
;;                        (set! l (cdr l))
;;                        (set! pc rem8-cps-ri3))]
;;                        
;;      [(inner_k k^ u) (begin
;;                        (set! k k^)
;;                        (set! v (cons u v))
;;                        (set! pc apply-k3))])))

;;(define main
;;  (lambda ()
;;    (begin
;;      (set! l '(1 (8)))
;;      (set! pc rem8-cps-ri3)
;;      (mount-trampoline kt_empty_k k pc)
;;      (printf "~s" v))))
;----------------------------------------------------------------------------------------------------------
; GREAT! I have to find a way to deal with lists when converting into C. Without the conversion this works
; fine in Scheme using just paranthec

; Next simply convert thunks into define-label

; R.I. CPSed version w/ union types
(define-label rem8-cps-ri3
  (cond
    [(null? l) (begin
                 (set! k k) ; useless 
                 (set! v '())
                 (set! pc apply-k3))]

    [(pair? (car l)) (begin
                       (set! k (kt_outer_k k l))
                       (set! l (car l))
                       (set! pc rem8-cps-ri3))]

    [(eq? (car l) 8) (begin
                       (set! k k) ; useless
                       (set! l (cdr l))
                       (set! pc rem8-cps-ri3))]

    [else (begin
            (set! k (kt_inner_k k (car l)))
            (set! l (cdr l))
            (set! pc rem8-cps-ri3))]))

(define-label apply-k3
  (union-case k kt
    [(empty_k dismount) (dismount-trampoline dismount)]
    [(outer_k k^ l) (begin
                      (set! k (kt_inner_k k^ v))
                      (set! l (cdr l))
                      (set! pc rem8-cps-ri3))]

    [(inner_k k^ u) (begin
                      (set! k k^)
                      (set! v (cons u v))
                      (set! pc apply-k3))]))

(define-label main
  (begin
    (set! l '(1 (8)))
    (set! pc rem8-cps-ri3)
    (mount-trampoline kt_empty_k k pc)
    (printf "~s" v)))