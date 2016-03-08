; Main for ac with a13 work
; Added analyze-closure-size
(eval-when (compile load eval)
  (optimize-level 2)
  (case-sensitive #t)
  )

(load "../match.ss")
(load "../helpers.ss")
(load "../fmts.pretty")     ;inform pretty-print about new forms
(load "../driver.ss")

(load "a15.ss")      ; for parse-scheme and all the rest

(load "../a15-wrapper.ss")   ; defines syntactic forms and procedures
                             ; needed to output of each pass

(load "../tests15.ss")