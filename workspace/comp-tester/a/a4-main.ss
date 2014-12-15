(eval-when (compile load eval)
  (optimize-level 2)
  (case-sensitive #t)
  )

(load "../match.ss")
(load "../helpers.ss")
(load "../fmts.pretty")     ;inform pretty-print about new forms
(load "../driver.ss")

(load "a4-verify.ss")
(load "a4-rest.ss")
(load "a4.ss")
(load "../a4-wrapper.ss")   ;defines syntactic forms and procedures
                            ;needed to output of each pass
(compiler-passes
  '(
    verify-scheme
    uncover-register-conflict
    assign-registers
    discard-call-live
    finalize-locations
    expose-frame-var
    expose-basic-blocks
    flatten-program
    generate-x86-64
    ))

(load "../tests4.ss")