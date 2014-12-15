(eval-when (compile load eval)
  (optimize-level 2)
  (case-sensitive #t)
  )

(load "../match.ss")
(load "../helpers.ss")
(load "../fmts.pretty")     ;inform pretty-print about new forms
(load "../driver.ss")

(load "a9.ss")
(load "a9-verify.ss")
(load "uil.ss")
(load "../a9-wrapper.ss")   ;defines syntactic forms and procedures
                            ;needed to output of each pass

;---------------------------------------------------------------
; Compiler passes
;---------------------------------------------------------------
(compiler-passes '(
  verify-scheme 
  uncover-locals
  remove-let
  verify-uil
  remove-complex-opera*
  flatten-set!
  impose-calling-conventions
  expose-allocation-pointer
  uncover-frame-conflict
  pre-assign-frame
  assign-new-frame
  (iterate
    finalize-frame-locations 
    select-instructions
    uncover-register-conflict
    assign-registers
    (break when everybody-home?)
    assign-frame)
  discard-call-live
  finalize-locations
  expose-frame-var
  expose-memory-operands
  expose-basic-blocks
  flatten-program
  generate-x86-64
))
;---------------------------------------------------------------

(load "../tests9.ss")
