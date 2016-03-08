(eval-when (compile load eval)
  (optimize-level 2)
  (case-sensitive #t)
  )

(load "../match.ss")
(load "../helpers.ss")
(load "../fmts.pretty")     ;inform pretty-print about new forms
(load "../driver.ss")

(load "uil.ss")
(load "a9.ss") ; for uncover-locals and remove-let
(load "a10.ss") ; for specify-representation
(load "a11.ss") ; for lift-letrec, normalize-context, and optimize-jumps
(load "a11-verify.ss")
(load "a11-rest.ss") ; for verify-a11-output and verify-a10-output

(load "../a11-wrapper.ss")   ;defines syntactic forms and procedures
                            ;needed to output of each pass

;---------------------------------------------------------------
; Compiler passes
;---------------------------------------------------------------
(compiler-passes '(
  verify-scheme 
  lift-letrec
  normalize-context
  verify-a11-output
  specify-representation
  verify-a10-output
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
optimize-jumps
  flatten-program
  generate-x86-64
))
;---------------------------------------------------------------

(load "../tests11.ss")
