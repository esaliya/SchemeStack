(* This file contains several test cases for the CAM evaluation
function. At the end there is a definition of factorial. We use Church
encodings for numbers, which unfortunately are not accepted by our
type system. *)
Require Import CAM.

(* Test cases *)
Eval compute in eval (lambda (var 0)) 10.
Eval compute in eval nil 10.
Eval compute in eval (cons nil nil) 10.
Eval compute in eval (app (lambda (var 0)) nil) 10.
Eval compute in eval (app (lambda (var 0)) (lambda (var 0))) 10.
Eval compute in eval (car (cons nil (cons nil nil))) 100.
Eval compute in eval (cdr (cons nil (cons nil nil))) 100.

(* Definitions *)
Definition suc := 
  (lambda (lambda (lambda (app (var 1) (app (app (var 2) (var 1)) (var 0)))))).

Definition zero := 
  (lambda (lambda (var 0))).

Fixpoint encode_number n :=
  match n with
    | O => zero
    | S n' => (app suc (encode_number n'))
  end.

Definition add :=
  (lambda (lambda (lambda (lambda
    (app (app (var 3) (var 1)) (app (app (var 2) (var 1)) (var 0))))))).

Definition to_list :=
  (lambda 
    (app 
      (app (var 0)
        (lambda (cons nil (var 0))))
      nil)).

Eval compute in eval (app to_list zero) 100.
Eval compute in eval (app to_list (encode_number 1)) 100.
Eval compute in eval (app to_list (app suc zero)) 100.
Eval compute in eval (app to_list (encode_number 5)) 1000.
Eval compute in eval 
  (app to_list 
    (app (app add (encode_number 2))
      (encode_number 3))) 
  1000.

Definition mul :=
  (lambda (lambda (lambda (lambda
    (app (app (var 3) (app (var 2) (var 1))) (var 0)))))).

Eval compute in eval (app to_list 
  (app (app mul (encode_number 2))
    (encode_number 3))) 1000.

Fixpoint cam_length n :=
  match n with
    | pair c d => 1 + (cam_length d)
    | null => 0
    | _ => 0
  end.

Eval compute in 
  match eval 
    (app to_list 
      (app (app mul (encode_number 2))
        (encode_number 3)))
    1000
    with
    | Some ls => Some (cam_length ls)
    | None => None
  end.

Definition pred :=
  (lambda (lambda (lambda
    (app 
      (app 
        (app
          (var 2)
          (lambda (lambda (app (var 0) (app (var 1) (var 3))))))
        (lambda (var 1)))
      (lambda (var 0)))))).

Eval compute in 
  match eval 
    (app to_list 
      (app pred (encode_number 5)))
    1000
    with
    | Some ls => Some (cam_length ls)
    | None => None
  end.

Definition Y :=
  (lambda 
    (app
      (lambda (app (var 1) (lambda (app (app (var 1) (var 1)) (var 0)))))
      (lambda (app (var 1) (lambda (app (app (var 1) (var 1)) (var 0))))))).

Definition fact :=
  (app Y
    (lambda (lambda
      (app 
        (app (var 0)
          (lambda (app (app mul (var 1)) (app (var 2) (app pred (var 1))))))
        (encode_number 1))))).

Eval compute in 
  match eval 
    (app to_list 
      (app fact (encode_number 3)))
    5000
    with
    | Some ls => Some (cam_length ls)
    | None => None
  end.

Eval compute in fact.
