(load "a15-main.ss")

(define input
  '(let ([p (cons 3 ())])
     (letrec ([f (lambda (p) (if (eq? (car p) 3) p (g)))]
              [g (lambda () (f p))])
       (g)))
  )

;;(define input
;;  '(letrec ([vector-scale!.0 (lambda (vect.1 scale.2)
;;                                 (let ([size.3 (vector-length vect.1)])
;;                                   (vector-scale!.12
;;                                     size.3
;;                                     vect.1
;;                                     scale.2)))]
;;              [vector-scale!.12 (lambda (offset.4 vect.5 scale.6)
;;                                  (if (< offset.4 '1)
;;                                      '0
;;                                      (begin
;;                                        (vector-set!
;;                                          vect.5
;;                                          (- offset.4 '1)
;;                                          (* (vector-ref
;;                                               vect.5
;;                                               (- offset.4 '1))
;;                                             scale.6))
;;                                        (vector-scale!.12
;;                                          (- offset.4 '1)
;;                                          vect.5
;;                                          scale.6))))]
;;              [vector-sum.13 (lambda (vect.7)
;;                               (vector-sum.14
;;                                 (vector-length vect.7)
;;                                 vect.7))]
;;              [vector-sum.14 (lambda (offset.9 vect.10)
;;                               (if (< offset.9 '1)
;;                                   '0
;;                                   (+ (vector-ref vect.10 (- offset.9 '1))
;;                                      (vector-sum.14
;;                                        (- offset.9 '1)
;;                                        vect.10))))])
;;       (let ([vect.11 (make-vector '5)])
;;         (begin
;;           (vector-set! vect.11 '0 '123)
;;           (vector-set! vect.11 '1 '10)
;;           (vector-set! vect.11 '2 '7)
;;           (vector-set! vect.11 '3 '12)
;;           (vector-set! vect.11 '4 '57)
;;           (vector-scale!.0 vect.11 '10)
;;           (vector-sum.13 vect.11))))
;;  )

(printf "\n------input ------\n")
(pretty-print input)
(printf "\n------ output------\n")
(pretty-print
 (convert-closures
  (uncover-free
   (sanitize-binding-forms
    (remove-anonymous-lambda
     (convert-assignments
      (purify-letrec
       (uncover-assigned
        (convert-complex-datum
         (parse-scheme input))))))))))
(printf "--------------------------------------------------\n")
(pretty-print
 (introduce-procedure-primitives
  (convert-closures
   (uncover-free
    (sanitize-binding-forms
     (remove-anonymous-lambda
      (convert-assignments
       (purify-letrec
        (uncover-assigned
         (convert-complex-datum
          (parse-scheme input)))))))))))
;;(pretty-print
;;  (optimize-source
;;   (introduce-procedure-primitives
;;    (optimize-self-reference
;;     (optimize-free
;;      (uncover-well-known
;;       (optimize-known-call
;;        (convert-closures
;;         (uncover-free input)))))))))

;;(pretty-print
;;  (expose-basic-blocks
;;   (expose-memory-operands
;;    (expose-frame-var
;;     (finalize-locations
;;      (discard-call-live
;;       (assign-frame
;;        (assign-registers
;;         (uncover-register-conflict
;;          (select-instructions
;;           (finalize-frame-locations
;;            (assign-new-frame
;;             (pre-assign-frame
;;              (uncover-frame-conflict
;;               (expose-allocation-pointer
;;                (impose-calling-conventions
;;                 (flatten-set!
;;                  (remove-complex-opera* input))))))))))))))))))
  

;;(define input
;;  '(letrec ([f.4 (lambda (z.3) z.3)])
;;     (let ([x.1 (f.4 '3)])
;;       (begin
;;         (f.4 '4)
;;         (let ([y.2 (+ x.1 '3)])
;;           (+ y.2 x.1))
;;         '7)))
;;  )

;;(define input
;;  '(letrec ([z.1 (lambda (x.2) (= x.2 '0))])
;;     (letrec ([e.3 (lambda (x.4) (if (z.1 x.4) '#t (o.5 (- x.4 '1))))]
;;              [o.5 (lambda (x.6) (if (z.1 x.6) '#f (e.3 (- x.6 '1))))])
;;       (e.3 '3)))
;;  )



;;(let ([input (purify-letrec (uncover-assigned (convert-complex-datum input)))])
;;  (printf "input-to-convert-assignments\n~s\n" input)
;;  (pretty-print
;;   (convert-assignments input)))

;;(pretty-print
;; (uncover-well-known
;;  (optimize-known-call
;;   (convert-closures
;;    (uncover-free 
;;     input)
;;    )
;;   )
;;  )
;; )

;;(pretty-print (optimize-self-reference input))
 
;;(pretty-print 
;; (introduce-procedure-primitives
;;  (convert-closures
;;   (uncover-free
;;    (verify-scheme input)
;;    )
;;   )
;;  )
;;)



;;(convert-assignments 
;; '(procedure? (lambda (x.495) (assigned (x.495) x.495))))
 
;;(pretty-print (optimize-source input))
