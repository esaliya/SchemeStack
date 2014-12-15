(eval-when (compile load eval)
  (optimize-level 2)
  (case-sensitive #t)
  )

(load "../match.ss")
(load "../helpers.ss")
(load "../fmts.pretty")     ;inform pretty-print about new forms
(load "../driver.ss")

(load "a3.ss")
(load "../a3-wrapper.ss")   ;defines syntactic forms and procedures
                            ;needed to output of each pass
(compiler-passes
  '(
    verify-scheme
    finalize-locations
    expose-frame-var
    expose-basic-blocks
    flatten-program
    generate-x86-64
    ))

(load "../tests3.ss")