(eval-when (compile load eval)
  (optimize-level 2)
  (case-sensitive #t)
  )

(load "../match.ss")
(load "../helpers.ss")
(load "../fmts.pretty")     ;inform pretty-print about new forms
(load "../driver.ss")

(load "a6-verify.ss")
(load "a6.ss")
(load "a6-rest.ss")
(load "../a6-wrapper.ss")   ;defines syntactic forms and procedures
                            ;needed to output of each pass

;;(define parameter-registers '())

(compiler-passes '(
  verify-scheme
  remove-complex-opera*
  flatten-set!
  impose-calling-conventions
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

(load "../tests6.ss")
