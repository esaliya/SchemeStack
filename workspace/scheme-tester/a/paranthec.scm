(load "pmatch.scm")
       

;;*************************************************************************************
;;*************************************************************************************
;; Syntax: define-label,
;;         mount-trampoline,
;;         dismount-trampoline,
;;         define-union,
;;         union-case,
;;         union-case/free

;;; A very handy macro for making consistent error messages.

(define-syntax pc-err
  (syntax-rules ()
    [(_ who code (str arg ...))
     (begin
       (printf "\nParentheC Error - In Expression:\n\n")
       (pretty-print code)
       (errorf who str arg ...))]))

;;; Table needed for define-label

(define **pc-func-name-table** '())

(define pc-add-func-name!
  (lambda (func-name)
    (set! **pc-func-name-table**
      (cons func-name **pc-func-name-table**))))

(define pc-func-name-exists?
  (lambda (fn)
    (memv fn **pc-func-name-table**)))

;;; define-label

(define-syntax define-label
  (lambda (x)
    (pc-error-check:define-label (syntax-object->datum x))
    (syntax-case x ()
      [(_ fn body ...)
       (pc-add-func-name! (syntax-object->datum #'fn))
       #'(define fn (lambda () body ...))])))

(define pc-error-check:define-label
  (lambda (code)
    (pmatch code
      [(define-label ,fn)
       (pc-err 'define-label code ("must have at least one body"))]
      [(define-label (,fn . ,p*) ,body)
       (pc-err 'define-label code ("cannot have any parameters"))]
      [(define-label ,fn ,body . ,body*)
       (if (pc-func-name-exists? fn)
           (pc-err 'define-label code
             ("function name ~s already exists" fn)))]
      [else (pc-err 'define-label code ("invalid syntax"))])))

;;; Trivial helper functions

(define pc-check-set-of-vars
  (letrec
      ([set-of-vars?
         (lambda (ls)
           (or (null? ls)
               (and (not (memv (car ls) (cdr ls))) (set-of-vars? (cdr ls)))))])
    (lambda (who code vars)
      (if (not (set-of-vars? vars))
          (pc-err who code ("duplicate variable used: ~s" vars))))))

;;; Table needed for define-union

(define **pc-union-type-table** `())

(define pc-add-union-type!
  (lambda (union-type sub-tn* arg-count*)
    (set! **pc-union-type-table**
      (cons `(,union-type ,(map cons sub-tn* arg-count*)) **pc-union-type-table**))))

(define pc-union-type-exists?
  (lambda (union-type)
    (assv union-type **pc-union-type-table**)))

;;; define-union

(define-syntax define-union
  (lambda (x)
    (pc-error-check:define-union (syntax-object->datum x))
    (syntax-case x ()
      [(__ union-type [sub-tn arg* ...] ...)
       (let ([ut-val (syntax-object->datum #'union-type)]
             [st*-val (syntax-object->datum #'(sub-tn ...))]
             [arg-count*-val (map length (syntax-object->datum #'((arg* ...) ...)))])
         (with-syntax
             ([(constructor-fn* ...)
               (datum->syntax-object #'__
                 (map (lambda (st-val)
                        (string->symbol (format "~s_~s" ut-val st-val)))
                   st*-val))]
              [(arg-count* ...)
               (datum->syntax-object #'__ arg-count*-val)])
           (pc-add-union-type! ut-val st*-val arg-count*-val)
           #'(begin
               (define constructor-fn*
                 (lambda n-arg
                   (if (eq? (length n-arg) arg-count*)
                       `(union-type sub-tn ,@n-arg)
                       (pc-err 'constructor-fn* `(constructor-fn* ,@n-arg)
                         ("wrong number of arguments to constructor: expected ~s"
                          arg-count*)))))
               ...)))])))

(define pc-error-check:define-union
  (lambda (code)
    (pmatch code
      [(define-union ,union-type)
       (pc-err 'define-union code
         ("must have at least one sub-type in union-type: ~s" union-type))]
      [(define-union ,union-type . ,c*)
       (let ((sub-tn* (map car c*))
             (arg** (map cdr c*)))
         (pc-check-set-of-vars 'define-union code sub-tn*)
         (for-each
           (lambda (arg*)
             (pc-check-set-of-vars 'define-union code arg*))
           arg**)
         (if (pc-union-type-exists? union-type)
             (pc-err 'define-union code
                     ("union-type ~s already exists" union-type))))]
      [else (pc-err 'define-union code ("invalid syntax"))])))

;;; union-case and union-case/free

(define-syntax union-case
  (lambda (x)
    (syntax-case x ()
      [(_ exp union-type [(sub-tn arg* ...) body* ...] ...)
       #'(general-union-case union-case exp union-type
           [(sub-tn arg* ...) body* ...] ...)])))

(define-syntax union-case/free
  (lambda (x)
    (syntax-case x ()
      [(_ exp union-type [(sub-tn arg* ...) body* ...] ...)
       #'(general-union-case union-case/free exp union-type
           [(sub-tn arg* ...) body* ...] ...)])))
 
(define-syntax general-union-case
  (lambda (x)
    (let ([code (syntax-object->datum x)])
      (pc-error-check:general-union-case code (cadr code)))
    (syntax-case x ()
      [(_ label var union-type [(sub-tn arg* ...) body] ...)
       #'(let ([code '(label exp union-type [(sub-tn arg* ...) body] ...)])
           (if (not (pc-valid-variant? 'union-type var))
               (pc-err 'label code
                 ("invalid datum for union-type \"~s\": ~s" 'union-type var)))
           (case (cadr var)
             [sub-tn (apply (lambda (arg* ...) body) (cddr var))]
             ...
             [else (pc-err
                     'label code
                     ("It should never come here: ~s, ~s" var 'union-type))]))])))


(define pc-valid-variant?
  (lambda (union-type variant)
    (and
      (list? variant)
      (>= (length variant) 2)
      (let ([ut (car variant)]
            [st (cadr variant)]
            [arg-count (length (cddr variant))])
        (and
          (eqv? union-type ut)
          (let ([type (assoc union-type **pc-union-type-table**)])
            (and type
              (member `(,st . ,arg-count) (cadr type)))))))))

(define pc-error-check:general-union-case
  (lambda (code who)
    (pmatch code
      [(general-union-case ,label ,var ,union-type)
       (pc-err who code ("all union-type must have at least one sub-type"))]
      [(general-union-case ,label ,var ,union-type . ,c*)
       (let* ((test* (map car c*))
              (sub-tn* (map car test*))
              (arg** (map cdr test*))
              (body** (map cdr c*)))
         (pc-check-set-of-vars who code `(,var ,union-type))
         (pc-check-set-of-vars who code sub-tn*)
         (for-each
           (lambda (arg*)
             (pc-check-set-of-vars who code arg*))
           arg**)
         (if (ormap null? body**)
             (pc-err who code
                     ("all union-case clause must contain at least one body")))
         (pc-union-type-does-not-exist? who var union-type
                                        sub-tn* arg** body**))]
      [else (pc-err who code ("invalid syntax"))])))

(define lookup-union
  (lambda (name)
    (let loop ([reg **pc-union-type-table**])
      (cond
       [(null? reg) (errorf 'lookup-union 
                           "union type `~a' not defined ~n" name)]
       [(eq? name (caar reg)) (car reg)]
       [else (loop (cdr reg))]))))

(define check-union-case
  (lambda (expr name type case)
    (cond
     [(and (null? type) (not (null? case)))
      (let ([s (open-output-string)])
        (pretty-print expr s)
        (errorf 'union-case  "~a\nsuperfluous cases for union type `~a': ~a"
               (get-output-string s) name case))]
     [(and (null? case) (not (null? type)))
      (let ([s (open-output-string)])
        (pretty-print expr s)
        (errorf 'union-case  "~a\nunmatched cases for union type `~a': ~a"
               (get-output-string s) name type))]
     [(and (null? type) (null? case)) #t]
     [(not (memq (car case) type))
      (let ([s (open-output-string)])
        (pretty-print expr s)
        (errorf 'union-case "~a\nvariant `~a' is not in union type `~a'"
               (get-output-string s) (car case) name))]
     [(memq (car case) (cdr case))
      (let ([s (open-output-string)])
        (pretty-print expr s)
        (errorf 'union-case  "~a\nduplicated cases `~a' in union-case of type `~a'"
               (get-output-string s) (car case) name))]
     [else (check-union-case expr name (remq (car case) type) (cdr case))])))

(define pc-union-type-does-not-exist?
  (lambda (who var ut st* arg** body**)
    (let* ([arg-count* (map length arg**)]
           [sub-type* (map cons st* arg-count*)]
           [type `(,ut ,sub-type*)])
      (check-union-case 
       `(,who ,var ,ut
              ,(map (lambda (st arg* body*)
                      (cons (cons st arg*) body*))
                    st* arg** body**)) 
       ut (map car (cadr (lookup-union ut))) (map car sub-type*)))))



;; this version has "macro expansion time" error checking and "runtime" error checking.
;; Helper functions should not interfere with correct parentheC code because all
;; helper functions have a "-"(minus) in them. Which  you cannot use.

;; Test codes.




(define-syntax define-registers
  (syntax-rules ()
    ((_ reg1 reg2 ...)
     (begin
       (define reg1 0)
       (define reg2 0)
       ...))))

(define-syntax define-program-counter
  (syntax-rules ()
    ((_ pc)
     (define-registers pc))))

(define-syntax mount-trampoline
  (lambda (x)
    (syntax-case x ()
      [(_ construct reg pc)
       #'(if (not (procedure? construct))
           (errorf 'mount-trampoline
             "~s must evaluate to 1 arity #<procedure>" 'trampfn-var)
           (call/cc
             (lambda (dismount-var)
               (set! reg (construct dismount-var))
               (let trampoline ()
                 (pc)
                 (trampoline)))))])))


(define-syntax dismount-trampoline
  (lambda (x)
    (syntax-case x ()
      [(_ var)
       #'(if (not (procedure? var))
           (errorf 'dismount-trampoline
             "~s must evaluate to 1 arity #<procedure>" 'var)
           (var 0))])))
