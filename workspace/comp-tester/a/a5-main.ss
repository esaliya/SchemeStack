(eval-when (compile load eval)
  (optimize-level 2)
  (case-sensitive #t)
  )

(load "../match.ss")
(load "../helpers.ss")
(load "../fmts.pretty")     ;inform pretty-print about new forms
(load "../driver.ss")

(load "a5-verify.ss")
(load "a5-rest.ss")
(load "a5.ss")
(load "../a5-wrapper.ss")   ;defines syntactic forms and procedures
                            ;needed to output of each pass
(compiler-passes '(
  verify-scheme
  uncover-frame-conflict
  introduce-allocation-forms
  (iterate
    select-instructions
    uncover-register-conflict
    assign-registers
    (break when everybody-home?)
    assign-frame
    finalize-frame-locations)
  discard-call-live
  finalize-locations
  expose-frame-var
  expose-basic-blocks
  flatten-program
  generate-x86-64
))

(load "../tests5.ss")