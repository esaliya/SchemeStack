Project Milestone 1
  Saliya Ekanayake
  Eric Holk
  Hyungro Lee

We are including two implementations of the Categorical Abstract
Machine. The first is written in Scheme, and the second is in
Coq. Both versions have working versions of factorial. Scheme's
factorial function is:

((lambda ((lambda (1 (lambda ((1 1) 0))))
          (lambda (1 (lambda ((1 1) 0))))))
  (lambda (lambda
           ((0 (lambda (((lambda (lambda
                                  (lambda (lambda ((3 (2 1)) 0)))))
                          1)
                        (2 ((lambda (lambda
                                     (lambda (((2 (lambda (lambda
                                                           (0 (1 3)))))
                                                (lambda 1))
                                              (lambda 0)))))
                             1)))))
             ((lambda (lambda (lambda (1 ((2 1) 0)))))
               (lambda (lambda 0)))))))

The equivalent version in Coq is:

app
         (lambda
            (app
               (lambda
                  (app (var 1) (lambda (app (app (var 1) (var 1)) (var 0)))))
               (lambda
                  (app (var 1) (lambda (app (app (var 1) (var 1)) (var 0)))))))
         (lambda
            (lambda
               (app
                  (app (var 0)
                     (lambda
                        (app
                           (app
                              (lambda
                                 (lambda
                                    (lambda
                                       (lambda
                                          (app
                                             (app (var 3)
                                                (app (var 2) (var 1)))
                                             (var 0)))))) 
                              (var 1))
                           (app (var 2)
                              (app
                                 (lambda
                                    (lambda
                                       (lambda
                                          (app
                                             (app
                                                (app 
                                                  (var 2)
                                                  (lambda
                                                  (lambda
                                                  (app 
                                                  (var 0)
                                                  (app (var 1) (var 3))))))
                                                (lambda (var 1)))
                                             (lambda (var 0)))))) 
                                 (var 1))))))
                  (app
                     (lambda
                        (lambda
                           (lambda
                              (app (var 1)
                                 (app (app (var 2) (var 1)) (var 0))))))
                     (lambda (lambda (var 0)))))))

The derivation of both versions of the functions are given in the
respect source files.

