(eval-when (compile load eval)
  (optimize-level 2)
  (case-sensitive #t)
  )

(load "../match.ss")
(load "../helpers.ss")
(load "../fmts.pretty")     ;inform pretty-print about new forms
(load "../driver.ss")

(load "a7-verify.ss")
(load "a7.ss")
(load "a7-rest.ss")
(load "../a7-wrapper.ss")   ;defines syntactic forms and procedures
                            ;needed to output of each pass

;;(define parameter-registers '())

(compiler-passes '(
  verify-scheme
  remove-complex-opera*
  flatten-set!
  impose-calling-conventions
  uncover-frame-conflict
  pre-assign-frame
  assign-new-frame
  (iterate
    finalize-frame-locations ;;Note. This comes first now since we need to finalize frame locs from
                             ;; previous assign-new-frame pass. 
    select-instructions
    uncover-register-conflict
    assign-registers
    (break when everybody-home?)
    assign-frame)
  discard-call-live
  finalize-locations
  expose-frame-var
  expose-basic-blocks
  flatten-program
  generate-x86-64
))

(load "../tests7.ss")
