(eval-when (compile load eval)
  (optimize-level 2)
  (case-sensitive #t)
  )

(load "../match.ss")
(load "../helpers.ss")
(load "../fmts.pretty")     ;inform pretty-print about new forms
(load "../driver.ss")

(load "a2.ss")
(load "../a2-wrapper.ss")   ;defines syntactic forms and procedures
                            ;needed to output of each pass
(compiler-passes
  '(
    verify-scheme
    expose-frame-var
    flatten-program
    generate-x86-64
    ))

(load "../tests2.ss")