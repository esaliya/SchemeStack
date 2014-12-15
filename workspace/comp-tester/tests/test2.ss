; Saliya Ekanayake
; sekanaya
; Assignment 2 - test2.ss

; Fibonacci calculator
;--------------------------
; Calculates Fib(n), where n is set in rcx in the body of letrec.
;
; The original fv0 holds the address referred by label loop$1, 
; fv1 holds the return address given by r15.
; Controller performs a computed goto based on the value
; of rcx. The rule is if rcx is positive or zero jump to loop$1.
; If negative jump to exit (return). The trick here is to 
; shift/reduce rbp based on a computer value of 0 or 8.
; Controller reduces rcx each time it is called to guarantee
; the jump to exit. The register rax will hold the final answer.
(letrec ([loop$1 (lambda () (begin 
                             (set! rax (+ rax rbx)) 
                             (set! rbx r11) 
                             (set! r11 rax) 
                             (controller$2)))]
         [controller$2 (lambda () (begin                              
                              (set! rdx rcx)
                              ; shift rdx righ by 63
                              ; output of this is (in 2's comp.)
                              ; 0 if rdx is zero or positive
                              ; else -1. 
                              (set! rdx (sra rdx 63))
                              ; this will result either 0 or 8
                              ; 8 if rdx was negative
                              (set! rdx (logand rdx 8))
                              (set! rbp (+ rbp rdx))
                              ; fv0 may either be the original fv0
                              ; or original fv1 (if rdx was neg.).
                              ; original fv1 has the exit address.
                              (set! r15 fv0)
                              ; reset rbp
                              (set! rbp (- rbp rdx))
                              ; reduce rcx by 1
                              (set! rcx (- rcx 1))
                              (r15)))])
  (begin
    ; set initial values
    (set! rax 1)
    (set! rbx 0)
    (set! r11 0)
    ; keep the address referred by label loop$1 in fv0
    (set! rdx loop$1)
    (set! fv0 rdx)
    ; keep the return address in fv1
    (set! rdx r15)
    (set! fv1 rdx)
    ; the number we are interested in (e.g.Fib(10))
    (set! rcx 10)  
    ; jump to the controller
    (controller$2)))
    