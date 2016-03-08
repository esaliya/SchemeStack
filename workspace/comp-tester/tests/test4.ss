; Fibonacci calculator
;--------------------------
; Calculates Fib(n), where n is set in rcx in the body of letrec
;
; The fv0 holds the return address given by r15.
; controller$2 sets jump-to.2 to either loop$1 or fv0 
; dependeing on the value of n.1 (in controller$2)
; if n.1 > 0 then jump-to.2 is set to loop$1, else fv0.
; The acc.0 in loop$1 holds the final answer.
(letrec ([loop$1 (lambda () (locals (acc.0 prev.1 temp.2)
                              (begin
                                (set! acc.0 rax)
                                (set! prev.1 rbx)
                                (set! temp.2 acc.0)
                                (set! acc.0 (+ acc.0 prev.1))
                                (set! prev.1 temp.2)
                                (set! rax acc.0)
                                (set! rbx prev.1)
                                (controller$2 rax rbx rcx fv0 rbp))))]
         [controller$2 (lambda () (locals (n.1 jump-to.2)
                                    (begin
                                      (set! n.1 rcx)
                                      (if (> n.1 0)
                                          (set! jump-to.2 loop$1)
                                          (set! jump-to.2 fv0))
                                      ; reduce n.1 by 1
                                      (set! n.1 (- n.1 1))
                                      (set! rcx n.1)
                                      (jump-to.2 rax rbx rcx fv0 rbp))))])
  (locals ()
    (begin
      ; set initial values
      (set! rax 1)
      (set! rbx 0)      
      ; keep the return address in fv0
      (set! fv0 r15)
      ; the number we are interested in (e.g.Fib(10))
      (set! rcx 10)
      ; jump to the controller
      (controller$2 rax rbx rcx fv0 rbp))))