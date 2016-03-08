; converting into C
;--------------------------------------------------------------------------------------
; direct style factorial with main
;;(define factorial
;;  (lambda (n)
;;    (cond
;;      [(zero? n) 1]
;;      [else (* n (factorial (sub1 n)))])))
;;; main
;;(define main
;;  (lambda ()
;;    (factorial 5)))
;--------------------------------------------------------------------------------------
; cps 
;;(define factorial-cps 
;;  (lambda (n k)
;;    (cond
;;      [(zero? n) (k 1)]
;;      [else (factorial-cps (sub1 n) (lambda (v) (k (* n v))))])))

;;(define main
;;  (lambda ()
;;    (factorial-cps 5 (lambda (v) v))))
;--------------------------------------------------------------------------------------
;;; R.I. w.r.t. continuations
;;(define factorial-cps 
;;  (lambda (n k)
;;    (cond
;;      [(zero? n) (apply_k  k 1)]
;;      [else (factorial-cps (sub1 n) (kt_extend n k))])))
   
;;(define kt_empty_k
;;  (lambda ()
;;    (lambda (v)
;;      v)))

;;(define kt_extend
;;  (lambda (n k)
;;    (lambda (v) (apply_k  k (* n v)))))

;;(define apply_k
;;  (lambda (k^ v)
;;    (k^ v)))

;;(define main
;;  (lambda ()
;;    (factorial-cps 6 (kt_empty_k))))
;--------------------------------------------------------------------------------------
; R.I. w.r.t. continuations, using define_union and union_case
;;(define factorial-cps 
;;  (lambda (n k)
;;    (cond
;;      [(zero? n) (apply_k  k 1)]
;;      [else (factorial-cps (sub1 n) (kt_extend n k))])))

;;(define-union kt
;;  (empty_k)
;;  (extend n k))

;;(define apply_k
;;  (lambda (k^ v)
;;    (union-case k^ kt
;;      [(empty_k) v]
;;      [(extend n k) (apply_k k (* n v))])))

;;(define main
;;  (lambda ()
;;    (factorial-cps 4 (kt_empty_k))))
;--------------------------------------------------------------------------------------
; introduce registers, we used an implicit set of registers n k k^ and v
; Note. 1. We need a seperate k^ for the union case
;       2. The order of the set! in the else case of factorial-cps
;;(define factorial-cps 
;;  (lambda () ; we had n and k
;;    (cond
;;      [(zero? n) (begin
;;                   (set! k^ k)
;;                   (set! v 1)
;;                   (apply_k))]
;;      [else (begin
;;              (set! k (kt_extend n k))
;;              (set! n (sub1 n))
;;              (factorial-cps))])))

;;(define-union kt
;;  (empty_k)
;;  (extend n k))

;;(define apply_k
;;  (lambda () ; we had k^ and v
;;    (union-case k^ kt
;;      [(empty_k) v]
;;      [(extend n k) (begin
;;                      (set! k^ k)
;;                      (set! v (* n v))
;;                      (apply_k))])))

;;(define main
;;  (lambda ()
;;    (begin
;;      (set! k (kt_empty_k))
;;      (set! n 4)
;;      (factorial-cps))))
;--------------------------------------------------------------------------------------
; we will now introduce mount-trampoline and dismount-trampoline along with proper
; register definitions
;;(define-registers n k k^ v)
;;(define-program-counter pc)

;;(define factorial-cps 
;;  (lambda () ; we had n and k
;;    (cond
;;      [(zero? n) (begin
;;                   (set! k^ k)
;;                   (set! v 1)
;;                   (set! pc apply_k))]
;;      [else (begin
;;              (set! k (kt_extend n k))
;;              (set! n (sub1 n))
;;              (set! pc factorial-cps))])))

;;(define-union kt
;;  (empty_k dismount)
;;  (extend n k))

;;(define apply_k
;;  (lambda () ; we had k^ and v
;;    (union-case k^ kt
;;      [(empty_k dismount) (dismount-trampoline dismount)]
;;      [(extend n k) (begin
;;                      (set! k^ k)
;;                      (set! v (* n v))
;;                      (set! pc apply_k))])))

;;(define main
;;  (lambda ()
;;    (begin      
;;      (set! n 5)
;;      (set! pc factorial-cps)
;;      (mount-trampoline kt_empty_k k pc)
;;      (printf "factorial 5: ~d\n" v))))
;--------------------------------------------------------------------------------------
; Remove thunks with define label
; register definitions
(define-registers n k k^ v)
(define-program-counter pc)

(define-label factorial-cps
  (cond
    [(zero? n) (begin
                 (set! k k)
                 (set! v 1)
                 (set! pc apply_k))]
    [else (begin
            (set! k (kt_extend n k))
            (set! n (sub1 n))
            (set! pc factorial-cps))]))

(define-union kt
  (empty_k dismount)
  (extend n k))

(define-label apply_k
  (union-case k kt
    [(empty_k dismount) (dismount-trampoline dismount)]
    [(extend n k^) (begin
                    (set! k k^)
                    (set! v (* n v))
                    (set! pc apply_k))]))

(define-label main
  (begin
    (set! n 5)
    (set! pc factorial-cps)
    (mount-trampoline kt_empty_k k pc)
    (printf "factorial 5: ~d\n" v)))