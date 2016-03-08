; Fibonacci calculator
;--------------------------
; Calculates Fib(n), where n is set in n.3 in the body of letrec.
;
; The fv0 holds the return address given by r15.
; controller$2 sets r15 to either loop$1 or fv0 
; dependeing on the value of n.1 (in controller$2)
; if n.1 >= 0 then r15 is set to loop$1, else fv0.
; The acc.0 in loop$1 holds the final answer.
(letrec ([loop$1 (lambda () (locate ([acc.0 rax] [current.1 r11] [prev.2 rbx])
                              (begin
                                (set! acc.0 (+ acc.0 prev.2))
                                (set! prev.2 current.1)
                                (set! current.1 acc.0)
                                (controller$2))))]
         [controller$2 (lambda () (locate ([n.1 rcx])
                                    (begin
                                      (if (>= n.1 0)
                                          (set! r15 loop$1)
                                          (set! r15 fv0))
                                      ; reduce n.1 by 1
                                      (set! n.1 (- n.1 1))
                                      (r15))))])
  (locate ([acc.0 rax] [current.1 r11] [prev.2 rbx] [n.3 rcx] [temp.4 rdx])
    (begin
      ; set initial values
      (set! acc.0 1)
      (set! current.1 0)
      (set! prev.2 0)      
      ; keep the return address in fv0
      (set! temp.4 r15)
      (set! fv0 temp.4)
      ; the number we are interested in (e.g.Fib(10))
      (set! n.3 10)
      ; jump to the controller
      (controller$2))))