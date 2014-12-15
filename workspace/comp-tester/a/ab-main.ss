(eval-when (compile load eval)
  (optimize-level 2)
  (case-sensitive #t)
  )

(load "../match.ss")
(load "../helpers.ss")
(load "../fmts.pretty")     ;inform pretty-print about new forms
(load "../driver.ss")

; Note. This depends mostly on a12 work
(load "ab-rest.ss") ; for verify-scheme, uncover-free convert-closures introduce-procedure-primitives,
                    ; lift-letrec, normalize-context, verify-a11-output, specify-representation,
                    ; verify-a10-output, uncover-lSocals, remove-let, and optimize-jumps,
(load "ab.ss") ; for optimize-source
(load "uil.ss")
(load "../ab-wrapper.ss")   ;defines syntactic forms and procedures
                            ;needed to output of each pass

;---------------------------------------------------------------
; Compiler passes
;---------------------------------------------------------------
(compiler-passes '(
  verify-scheme 
  uncover-free
  convert-closures
  introduce-procedure-primitives
  optimize-source
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

(load "../testsab.ss")
