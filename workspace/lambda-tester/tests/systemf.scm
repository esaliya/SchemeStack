;;[ ]≡Λα.λe:α.λc:(β→α→α).e
;;[ ]:∀α.α→(β→α→α)→α

;;cons≡λx:β.λl:∀α.(α→(β→α→α)→α).Λγ.λe:γ.λc:(β→γ→γ).((c x)  ((l[γ]  e)c))
;;cons:β→(∀α.α→(β→α→α)→α)→(∀γ.γ→(β→γ→γ)→γ)

;;Note. (∀α.α→(β→α→α)→α) is equivalent in type to (∀γ.γ→(β→γ→γ)→γ). Let’s name it List β for future reference.

;;insert≡λcmp:∀α.(α→α→bool).λl:List α.λx:α.((l[List α]  [ ])   c)

;;where c≡λy:α.λu:List α.if (cmp x y)   (cons y u)   (cons y (cons x u))
;; 

(define pair
  (lambda (b)
    (lambda (c)
      (lambda (s)
        ((s b) c)))))

(define fstp
  (lambda (p)
    (p (lambda (x) (lambda (y) x)))))

(define sndp
  (lambda (p)
    (p (lambda (x) (lambda (y) y)))))

(define true
  (lambda (t)
    (lambda (f)
      t)))

(define false
  (lambda (t)
    (lambda (f)
      f)))

(define IF
  (lambda (e1)
    (lambda (e2)
      (lambda (e3)
        (((e1 (lambda (x) e2)) (lambda (x) e3)) (lambda (x) x))))))

(define emptyl
  (lambda (e)
    (lambda (c)
      e)))

(define consl
  (lambda (b)
    (lambda (lb)
      (lambda (e)
        (lambda (c)
          ((c b) ((lb e) c)))))))

(define printl
  (lambda (lb)
    ((lb '())
     (lambda (xi)
       (lambda (ei)
         (cons xi ei))))))

(define addonel
  (lambda (lint)
    ((lint emptyl)
          (lambda (xi)
            (lambda (ei)
              ((consl (add1 xi)) ei))))))

;; for simplicity I will not encode numbers and relational operators
(define cmpint
  (lambda (x)
    (lambda (y)
      (if (< x y) true false)))) ;; If I had an encoding for numbers and "<" then this extra "if" wouldn't be needed

(define insertl
  (lambda (cmpb)
    (lambda (lb)
      (lambda (b)
        ((lambda (p)
           (((IF (fstp p))
             (sndp p))
            ((consl b) (sndp p))))
         ((lb ((pair false) emptyl))
          (lambda (bi)
            (lambda (pi)
              (((IF ((cmpb b) bi))
                ((pair false) ((consl bi) (sndp pi))))
               (((IF (fstp pi))
                 ((pair true) ((consl bi) (sndp pi))))
                ((pair true) ((consl bi) ((consl b) (sndp pi))))))))))))))

(define sortl
  (lambda (lb)
    (lambda (cmpb)
      ((lb emptyl)
       (lambda (bi)
         (lambda (ei)
           (((insertl cmpb) ei) bi)))))))
    


;;------------------------------

(define lint 
  ((consl 1) ((consl 3) ((consl 5) emptyl))))

(define unsortedlint
  ((consl 12) ((consl 3) ((consl 5) emptyl))))


;;(printl (((insertl cmpint) lint) 2)))
    
