;; A test with no useful work done, except to mess 
;; around register allocation. It causes spills
;; by having unnecessarily long list of active registers.
;; It also exercises the select-instructions pass by
;; forcing several rewrites.
(letrec ([f$1 (lambda ()
                (locals()
                  (begin
                    (set! rdx fv0)
                    (set! r11 (* rdx 1))
                    (set! fv2 r11)
                    (set! fv3 (+ fv2 fv0))
                    (set! rax fv3)
                    (r15 rax rbp rdx rdi rsi r9 r10 r11 r12 r13 r14))))])
  (locals (a.1 b.2 c.3 d.4 e.5 f.6 g.7)
    (begin
      (set! fv0 1)
      (set! a.1 0)
      (set! b.2 (+ 1 a.1)) 
      (set! c.3 (+ a.1 b.2))
      (set! d.4 (+ c.3 b.2))
      (if (< b.2 d.4)
          (begin 
            (set! e.5 (- a.1 a.1))
            (set! f.6 (+ e.5 fv0))
            (set! g.7 f.6)
            (f$1 rbp rax fv0 rcx fv1 r15 rbx rdx rdi rsi r9 r10 r11 r12 r13 r14)) ;; force a spill
          (begin 
            (set! g.7 (+ a.1 b.2))
            (set! rcx b.2)
            (set! fv1 (+ a.1 fv0))
            (f$1 rbp rax rcx fv1 r15 rbx rdx rdi rsi r9 r10 r11 r12 r13 r14)))))) ;; force a spill
      
                  
      
          
        
  