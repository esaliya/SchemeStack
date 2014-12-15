(define o (lambda (f g) (lambda (x) (f (g x))))}

(star_M unit_M) = Identity_M
(o (star_M f) unit_M) = f
(star_M (o (star_M f) g)) = (o (star_M f) (star_M g))

(define unit_store
  (lambda (a)
    (lambda (s)     ;; <-------------------- this lambda is a Ma
      `(,a . ,s))))

(define star_store
  (lambda (f)
    (lambda (Ma)
      (lambda (s)   ;; <-------------------- this lambda is a Ma
        (let ([p (Ma s)])
          (let ([new-a (car p)] [new-s (cdr p)])
            (let ([new-Ma (f new-a)])
              (new-Ma new-s))))))))

(define unit_M (lambda (a) Ma))
(define star_M (lambda (f) (lambda (Ma) Ma)))
(define f (lambda (a) Ma))

unit_M : a -> Ma
star_M : (a -> Ma) -> (Ma -> Ma)

(define remberevenXhowmanyeven
  (lambda (l)
    (cond
      ((null? l) (unit_store '()))
      ((odd? (car l))
       ((star_store (lambda (d) (unit_store (cons (car l) d))))
        (remberevenXhowmanyeven (cdr l))))
      (else
       ((star_store (lambda (__)
                      ((star_store (lambda (d) (unit_store d)))
                       (remberevenXhowmanyeven (cdr l)))))
        (lambda (s) `(__ . ,(add1 s))))))))

> ((remberevenXhowmanyeven '(2 3 7 4 5 6 8 9 2)) 0)
((3 7 5 9) . 5)

       ((star_store (lambda (d) (unit_store (cons (car l) d))))
        (remberevenXhowmanyeven (cdr l)))

       ((star_store (lambda (__)
                      ((star_store (lambda (d) (unit_store d)))
                       (remberevenXhowmanyeven (cdr l)))))
        (lambda (s) `(__ . ,(add1 s))))

                      ((star_store unit_store)
                       (remberevenXhowmanyeven (cdr l)))

                      (remberevenXhowmanyeven (cdr l))

(define remberevenXhowmanyeven
  (lambda (l)
    (cond
      ((null? l) (unit_store '()))
      ((odd? (car l))
       ((star_store (lambda (d) (unit_store (cons (car l) d))))
        (remberevenXhowmanyeven (cdr l))))
      (else
       ((star_store (lambda (__) (remberevenXhowmanyeven (cdr l))))
        (lambda (s) `(__ . ,(add1 s))))))))

(define remberevenXhawmanyeven
  (lambda (l)
    (cons (rembereven l) (count-even l))))

(define remberevenXhowmanyeven
  (lambda (ls k)
    (cond
      ((null? ls) (k `(() . 0)))
      ((odd? (car ls)) (remberevenXhowmanyeven (cdr ls)
                         (lambda (p)
                           (k `(,(cons (car ls) (car p)) . ,(cdr p))))))
      (else (remberevenXhowmanyeven (cdr ls)
              (lambda (p) (k `(,(car p) . ,(add1 (cdr p))))))))))

> (remberevenXhowmanyeven '(2 3 7 4 5 6 8 9 2) (lambda (p) p))
((3 7 5 9) . 5)

(define rember*evenXhowmanyeven
  (lambda (l k)
    (cond
      ((null? l) (k `(() . 0)))
      ((pair? (car l))
       (rember*evenXhowmanyeven (car l)
         (lambda (pa)
           (rember*evenXhowmanyeven (cdr l)
             (lambda (pd)
               (k `(,(cons (car pa) (car pd)) . ,(+ (cdr pa) (cdr pd)))))))))
      ((odd? (car l)) (rember*evenXhowmanyeven (cdr l)
                         (lambda (p)
                           (k `(,(cons (car l) (car p)) . ,(cdr p))))))
      (else (rember*evenXhowmanyeven (cdr l)
              (lambda (p) (k `(,(car p) . ,(add1 (cdr p))))))))))

> (rember*evenXhowmanyeven '(2 3 (7 4 5 6) 8 (9) 2) (lambda (p) p))
((3 (7 5) (9)) . 5)

(define rember*evenXhowmanyeven
  (lambda (l)
    (cond
      ((null? l) (unit_store '()))
      ((pair? (car l))
       ((star_store
         (lambda (a)
           ((star_store (lambda (d) (unit_store (cons a d))))
            (rember*evenXhowmanyeven (cdr l)))))
        (rember*evenXhowmanyeven (car l))))
      ((odd? (car l))
       ((star_store (lambda (d) (unit_store (cons (car l) d))))
        (rember*evenXhowmanyeven (cdr l))))
      (else
       ((star_store (lambda (__) (rember*evenXhowmanyeven (cdr l))))
        (lambda (s) `(__ . ,(add1 s))))))))

> ((rember*evenXhowmanyeven '(2 3 (7 4 5 6) 8 (9) 2)) 0)
((3 (7 5) (9)) . 5)

(define incr-store
  (lambda (s)
    `(__ . ,(add1 s))))

(lambda (__) ...) and (lambda (s) `(__ . ,(add1 s))) would not be as clear.

1)  \scheme{((lambda (x) body) arg)} is equivalent to 
\scheme{(let ((x arg)) body)},
2)  In \scheme{(let ((x arg)) body)} it is legitimate to substitute
\scheme{arg} for \scheme{x} in \scheme{body} provided that no unwanted 
variable capture occurs, and of course, this works in both directions.
So, for example, \scheme{((f x) ((g x) (g x)))} can be rewritten as
\scheme{(let ((gx (g x))) ((f x) (gx gx)))} and vice versa.

1/2. [../unit_store] and [../star_store].

(define rember*evenXhowmanyeven
  (lambda (l)
    (cond
      ((null? l) ((lambda (a) (lambda (s) `(,a . ,s))) '()))
      ((pair? (car l))
       (((lambda (f)
           (lambda (Ma)
             (lambda (s)
               (let ((p (Ma s)))
                 (let ((new-a (car p)) (new-s (cdr p)))
                   (let ((new-Ma (f new-a)))
                     (new-Ma new-s)))))))
         (lambda (a)
           (((lambda (f)
               (lambda (Ma)
                 (lambda (s)
                   (let ((p (Ma s)))
                     (let ((new-a (car p)) (new-s (cdr p)))
                       (let ((new-Ma (f new-a)))
                         (new-Ma new-s)))))))
            (lambda (d) ((lambda (a) (lambda (s) `(,a . ,s))) (cons a d))))
         (rember*evenXhowmanyeven (cdr l)))))
        (rember*evenXhowmanyeven (car l))))
      ((odd? (car l))
       (((lambda (f)
           (lambda (Ma)
             (lambda (s)
               (let ((p (Ma s)))
                 (let ((new-a (car p)) (new-s (cdr p)))
                   (let ((new-Ma (f new-a)))
                     (new-Ma new-s)))))))
         (lambda (d) ((lambda (a) (lambda (s) `(,a . ,s))) (cons (car l) d))))
        (rember*evenXhowmanyeven (cdr l))))
      (else
       (((lambda (f)
           (lambda (Ma)
             (lambda (s)
               (let ((p (Ma s)))
                 (let ((new-a (car p)) (new-s (cdr p)))
                   (let ((new-Ma (f new-a)))
                     (new-Ma new-s)))))))
         (lambda (a) (lambda (s) `(,a . ,(add1 s)))))
        (rember*evenXhowmanyeven (cdr l)))))))

3. [(lambda (a) (lambda (s) `(,a . ,(add1 s))))/f].

      (else
       ((lambda (Ma)
          (lambda (s)
            (let ((p (Ma s)))
              (let ((new-a (car p)) (new-s (cdr p)))
                (let ((new-Ma ((lambda (a) (lambda (s) `(,a . ,(add1 s))))
                               new-a)))
                  (new-Ma new-s))))))
        (rember*evenXhowmanyeven (cdr l))))

4. [(rember*evenXhowmanyeven (cdr l))/Ma].

      (else
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
           (let ((new-a (car p)) (new-s (cdr p)))
             (let ((new-Ma ((lambda (a) (lambda (s) `(,a . ,(add1 s))))
                            new-a)))
               (new-Ma new-s))))))

5. [../a].

      (else
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
           (let ((new-a (car p)) (new-s (cdr p)))
             (let ((new-Ma (lambda (s) `(,new-a . ,(add1 s)))))
               (new-Ma new-s))))))
6/7.. [(car p)/new-a] and [(cdr p)/new-s].

      (else
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
           (let ((new-Ma (lambda (s) `(,(car p) . ,(add1 s)))))
             (new-Ma (cdr p))))))

8. [(lambda (s) `(,(car p) . ,(add1 s)))/new-Ma].

      (else
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
           ((lambda (s) `(,(car p) . ,(add1 s))) (cdr p)))))

Now, we finish the clause.
9. [(cdr p)/s].

      (else
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
           `(,(car p) . ,(add1 (cdr p))))))

10. [(lambda (d) ((lambda (a) (lambda (s) `(,a . ,s))) (cons a d)))/f].

      ((odd? (car l))
       ((lambda (Ma)
          (lambda (s)
            (let ((p (Ma s)))
              (let ((new-a (car p)) (new-s (cdr p)))
                (let ((new-Ma ((lambda (d)
                                 ((lambda (a)
                                    (lambda (s)
                                      `(,a . ,s)))
                                  (cons (car l) d)))
                               new-a)))
                  (new-Ma new-s))))))
        (rember*evenXhowmanyeven (cdr l))))

11. [(rember*evenXhowmanyeven (cdr l))/Ma].

      ((odd? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
           (let ((new-a (car p)) (new-s (cdr p)))
             (let ((new-Ma ((lambda (d)
                              ((lambda (a)
                                 (lambda (s)
                                   `(,a . ,s))) (cons (car l) d))) new-a)))
               (new-Ma new-s))))))

12/13. [(car p)/new-a] and [(cdr p)/new-d].

      ((odd? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
           (let ((new-Ma ((lambda (d)
                            ((lambda (a)
                               (lambda (s) `(,a . ,s)))
                             (cons (car l) d)))
                          (car p))))
             (new-Ma (cdr p))))))

14. [(car p)/d].

      ((odd? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
           (let ((new-Ma ((lambda (a)
                            (lambda (s) `(,a . ,s)))
                          (cons (car l) (car p)))))
             (new-Ma (cdr p))))))

15. [((cons (car l) (car p))/a)].

      ((odd? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
           (let ((new-Ma (lambda (s) `(,(cons (car l) (car p)) . ,s))))
             (new-Ma (cdr p))))))

16. [(lambda (s) `(,(cons (car l) (car p)) . ,s))/new-Ma].

      ((odd? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
           ((lambda (s) `(,(cons (car l) (car p)) . ,s)) (cdr p)))))

With this final step, we are done with the third clause.

17. [(cdr p)/s].

      ((odd? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
           `(,(cons (car l) (car p)) . ,(cdr p)))))

18. Rename variables.

      ((pair? (car l))
       (((lambda (f)
           (lambda (Ma)
             (lambda (s)
               (let ((p (Ma s)))
                 (let ((new-a (car p)) (new-s (cdr p)))
                   (let ((new-Ma (f new-a)))
                     (new-Ma new-s)))))))
         (lambda (a^)
           (((lambda (f^)
               (lambda (Ma^)
                 (lambda (s^)
                   (let ((p^ (Ma^ s^)))
                     (let ((new-a^ (car p^)) (new-s^ (cdr p^)))
                       (let ((new-Ma^ (f^ new-a^)))
                         (new-Ma^ new-s^)))))))
            (lambda (d)
              ((lambda (a) (lambda (s) `(,a . ,s)))
               (cons a^ d))))
         (rember*evenXhowmanyeven (cdr l)))))
        (rember*evenXhowmanyeven (car l))))

19. [.../f].

      ((pair? (car l))
       ((lambda (Ma)
          (lambda (s)
            (let ((p (Ma s)))
              (let ((new-a (car p)) (new-s (cdr p)))
                (let ((new-Ma ((lambda (a^)
                                 (((lambda (f^)
                                     (lambda (Ma^)
                                       (lambda (s^)
                                         (let ((p^ (Ma^ s^)))
                                           (let ((new-a^ (car p^))
                                                 (new-s^ (cdr p^)))
                                             (let ((new-Ma^ (f^ new-a^)))
                                               (new-Ma^ new-s^)))))))
                                    (lambda (d)
                                      ((lambda (a)
                                         (lambda (s) `(,a . ,s)))
                                       (cons a^ d))))
                                  (rember*evenXhowmanyeven (cdr l))))
                               new-a)))
                  (new-Ma new-s))))))
        (rember*evenXhowmanyeven (car l))))

20. [../Ma].

      ((pair? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (car l)) s)))
           (let ((new-a (car p)) (new-s (cdr p)))
             (let ((new-Ma ((lambda (a^)
                              (((lambda (f^)
                                  (lambda (Ma^)
                                    (lambda (s^)
                                      (let ((p^ (Ma^ s^)))
                                        (let ((new-a^ (car p^))
                                              (new-s^ (cdr p^)))
                                          (let ((new-Ma^ (f^ new-a^)))
                                            (new-Ma^ new-s^)))))))
                                (lambda (d)
                                  ((lambda (a)
                                     (lambda (s) `(,a . ,s)))
                                   (cons a^ d))))
                               (rember*evenXhowmanyeven (cdr l))))
                            new-a)))
               (new-Ma new-s))))))

21/22. [../new-a] and [../new-s].

      ((pair? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (car l)) s)))
           (let ((new-Ma ((lambda (a^)
                            (((lambda (f^)
                                (lambda (Ma^)
                                  (lambda (s^)
                                    (let ((p^ (Ma^ s^)))
                                      (let ((new-a^ (car p^))
                                            (new-s^ (cdr p^)))
                                        (let ((new-Ma^ (f^ new-a^)))
                                          (new-Ma^ new-s^)))))))
                              (lambda (d)
                                ((lambda (a)
                                   (lambda (s) `(,a . ,s)))
                                 (cons a^ d))))
                             (rember*evenXhowmanyeven (cdr l))))
                          (car p))))
             (new-Ma (cdr p))))))

23. [../new-Ma].

      ((pair? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (car l)) s)))
           (((lambda (a^)
               (((lambda (f^)
                   (lambda (Ma^)
                     (lambda (s^)
                       (let ((p^ (Ma^ s^)))
                         (let ((new-a^ (car p^))
                               (new-s^ (cdr p^)))
                           (let ((new-Ma^ (f^ new-a^)))
                             (new-Ma^ new-s^)))))))
                 (lambda (d)
                   ((lambda (a) (lambda (s) `(,a . ,s)))
                    (cons a^ d))))
                (rember*evenXhowmanyeven (cdr l))))
             (car p))
            (cdr p)))))

24. [(car p)/a^].

      ((pair? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (car l)) s)))
           ((((lambda (f^)
                (lambda (Ma^)
                  (lambda (s^)
                    (let ((p^ (Ma^ s^)))
                      (let ((new-a^ (car p^))
                            (new-s^ (cdr p^)))
                        (let ((new-Ma^ (f^ new-a^)))
                          (new-Ma^ new-s^)))))))
              (lambda (d)
                ((lambda (a) (lambda (s) `(,a . ,s)))
                 (cons (car p) d))))
             (rember*evenXhowmanyeven (cdr l)))
            (cdr p)))))

25. [../f^].

      ((pair? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (car l)) s)))
           (((lambda (Ma^)
               (lambda (s^)
                 (let ((p^ (Ma^ s^)))
                   (let ((new-a^ (car p^))
                         (new-s^ (cdr p^)))
                     (let ((new-Ma^ ((lambda (d)
                                       ((lambda (a) (lambda (s) `(,a . ,s)))
                                        (cons (car p) d)))
                                     new-a^)))
                       (new-Ma^ new-s^))))))
             (rember*evenXhowmanyeven (cdr l)))
            (cdr p)))))

26. [(rember*evenXhowmanyeven (cdr l))/Ma^].

      ((pair? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (car l)) s)))
           ((lambda (s^)
              (let ((p^ ((rember*evenXhowmanyeven (cdr l)) s^)))
                (let ((new-a^ (car p^))
                      (new-s^ (cdr p^)))
                  (let ((new-Ma^ ((lambda (d)
                                    ((lambda (a) (lambda (s) `(,a . ,s)))
                                     (cons (car p) d)))
                                  new-a^)))
                    (new-Ma^ new-s^)))))
            (cdr p)))))

27. [(cdr p)/s^].

      ((pair? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (car l)) s)))
           (let ((p^ ((rember*evenXhowmanyeven (cdr l)) (cdr p))))
             (let ((new-a^ (car p^))
                   (new-s^ (cdr p^)))
               (let ((new-Ma^ ((lambda (d)
                                 ((lambda (a) (lambda (s) `(,a . ,s)))
                                  (cons (car p) d)))
                               new-a^)))
                 (new-Ma^ new-s^)))))))

28/29. [(car p^)/new-a^], and [(cdr p^)/new-s^].

      ((pair? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (car l)) s)))
           (let ((p^ ((rember*evenXhowmanyeven (cdr l)) (cdr p))))
             (let ((new-Ma^ ((lambda (d)
                               ((lambda (a) (lambda (s) `(,a . ,s)))
                                (cons (car p) d)))
                             (car p^))))
               (new-Ma^ (cdr p^)))))))

30. [../new-Ma^].

      ((pair? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (car l)) s)))
           (let ((p^ ((rember*evenXhowmanyeven (cdr l)) (cdr p))))
             (((lambda (d)
                 ((lambda (a)
                    (lambda (s) `(,a . ,s)))
                  (cons (car p) d)))
               (car p^))
              (cdr p^))))))

31. [(car p^)/d].

(define rember*evenXhowmanyeven
  (lambda (l)
    (cond
      ((null? l) ((lambda (a) (lambda (s) `(,a . ,s))) '()))
      ((pair? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (car l)) s)))
           (let ((p^ ((rember*evenXhowmanyeven (cdr l)) (cdr p))))
             (((lambda (a) (lambda (s) `(,a . ,s)))
               (cons (car p) (car p^)))
              (cdr p^))))))
      ((odd? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
           `(,(cons (car l) (car p)) . ,(cdr p)))))
      (else
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
           `(,(car p) . ,(add1 (cdr p)))))))))

32. [(cons (car p) (car p^))/a].

      ((pair? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (car l)) s)))
           (let ((p^ ((rember*evenXhowmanyeven (cdr l)) (cdr p))))
             ((lambda (s) `(,(cons (car p) (car p^)) . ,s))
              (cdr p^))))))

The next step finishes the second clause.

33. [(cdr p^)/s].

      ((pair? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (car l)) s)))
           (let ((p^ ((rember*evenXhowmanyeven (cdr l)) (cdr p))))
             `(,(cons (car p) (car p^)) . ,(cdr p^))))))
\end{scheme}

\begin{scheme}
34. ['()/a].

(define rember*evenXhowmanyeven
  (lambda (l)
    (cond
      ((null? l) (lambda (s) `(,'() . ,s)))
      ((pair? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (car l)) s)))
           (let ((p^ ((rember*evenXhowmanyeven (cdr l)) (cdr p))))
             `(,(cons (car p) (car p^)) . ,(cdr p^))))))
      ((odd? (car l))
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
           `(,(cons (car l) (car p)) . ,(cdr p)))))
      (else
       (lambda (s)
         (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
           `(,(car p) . ,(add1 (cdr p)))))))))

35. Inverted staging.

(define rember*evenXhowmanyeven
  (lambda (l)
    (lambda (s)
      (cond
        ((null? l) `(,'() . ,s))
        ((pair? (car l))
         (let ((p ((rember*evenXhowmanyeven (car l)) s)))
           (let ((p^ ((rember*evenXhowmanyeven (cdr l)) (cdr p))))
             `(,(cons (car p) (car p^)) . ,(cdr p^)))))
        ((odd? (car l))
         (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
           `(,(cons (car l) (car p)) . ,(cdr p))))
        (else
          (let ((p ((rember*evenXhowmanyeven (cdr l)) s)))
            `(,(car p) . ,(add1 (cdr p)))))))))