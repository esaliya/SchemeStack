(eval-when (compile load eval)
  (optimize-level 2)
  (case-sensitive #t)
  )

(load "../match.ss")
(load "../helpers.ss")
(load "../fmts.pretty")     ;inform pretty-print about new forms
(load "../driver.ss")

(load "a8.ss")
(load "../a8-wrapper.ss")   ;defines syntactic forms and procedures
                            ;needed to output of each pass

(set! parameter-registers '(rbp))
(set! frame-pointer-register 'rax)
(set! allocation-pointer-register 'r15)
(set! return-value-register 'rsi)
(set! return-address-register 'rsi)
(set! registers '(rbp rax r15 rsi rdx))

(load "../tests8.ss")
