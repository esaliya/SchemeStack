; This is to test profiling with scheme, but it seems it's not working with petite
;;To compile the code with profiling enabled, set the parameter compile-profile to #t while compiling your application or loading it from source. Let's assume that the file /tmp/fatfib/fatfib.ss contains the following source code.

;;(define fat+
;;  (lambda (x y)
;;    (if (zero? y)
;;        x
;;        (fat+ (1+ x) (1- y)))))

;;(define fatfib
;;  (lambda (x)
;;    (if (< x 2)
;;        1
;;        (fat+ (fatfib (1- x)) (fatfib (1- (1- x)))))))

;;We can load fatfib.ss with profiling enabled as follows.

;;(parameterize ([compile-profile #t])
;;  (load "/tmp/fatfib/fatfib.ss"))

;;We then run the application as usual.

;;(fatfib 20) => 10946

;;After the run (or multiple runs), we dump the profile information as a set of html files using profile-dump-html.

;;(profile-dump-html) 
(define fat+
  (lambda (x y)
    (if (zero? y)
        x
        (fat+ (1+ x) (1- y)))))

(define fatfib
  (lambda (x)
    (if (< x 2)
        1
        (fat+ (fatfib (1- x)) (fatfib (1- (1- x)))))))