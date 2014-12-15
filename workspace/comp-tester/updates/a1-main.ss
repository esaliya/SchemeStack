(eval-when (compile load eval)
  (optimize-level 2)
  (case-sensitive #t)
  )

(load "../match.ss")
(load "../helpers.ss")
(load "../fmts.pretty")     ;inform pretty-print about new forms
(load "../driver.ss")

(load "a1.ss")
(load "../a1-wrapper.ss")   ;defines syntactic forms and procedures
                         ;needed to output of each pass
(compiler-passes
  '(
    verify-scheme
    generate-x86-64
    ))

(load "../tests1.ss")