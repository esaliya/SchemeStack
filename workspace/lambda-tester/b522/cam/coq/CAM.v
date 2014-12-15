(* This defines an evaluator for the Categorical Abstract Machine. *)

(* Syntax of terms *)
Inductive term :=
| var (n : nat) 
| lambda (body : term)
| app (t1 t2 : term)
| nil
| cons (t1 t2 : term)
| car (t : term)
| cdr (t : term).

(* Syntax of values *)
Inductive value :=
| null
| pair (v1 v2 : value)
| closure (env : value) (body : term).

(* Syntax of continuations *)
Inductive cont :=
| cont0
| cont1 (t : term) (k : cont)
| cont2 (k : cont)
| cont3 (t : term) (k : cont)
| cont4 (k : cont)
| cont5 (k : cont)
| cont6 (k : cont).

(* Machine configurations *)
Inductive state :=
| eval_st (t : term) (v : value) (s : list value) (k : cont)
| cont_st (k : cont) (v : value) (s : list value).

(* Runtime environment lookup *)
Fixpoint gamma (n : nat) (env : value) :=
  match n, env with
    | O, pair v1 v2 => Some v2
    | S n', pair v1 v2 => gamma n' v1
    | _, _ => None
  end.

(* Runtime environment lookup, defined relationally. Relational
definitions are much easier to use in proofs, because Coq's inversion
tactic makes much more information available to you. *)
Inductive gamma_r : nat -> value -> value -> Prop :=
| Env_Zero : forall v1 v2, gamma_r 0 (pair v1 v2) v2
| Env_Suc  : forall n v1 v2 v', 
  gamma_r n v1 v' -> gamma_r (S n) (pair v1 v2) v'.

(* A proof that the two definitions of environment lookup are
interchangeable *)
Lemma gamma_equiv :
  forall n v v',
    gamma n v = Some v' <-> gamma_r n v v'.
intro n.
induction n.
intros.
simpl. destruct v. 
split.
intro H. contradict H. discriminate.
intros. inversion H.
split.
intro H. inversion H. subst.
apply Env_Zero.
intro H.
inversion H; subst. reflexivity.
split.
intro H. inversion H.
intro H; inversion H.
intros. split. intros.
simpl in H.
destruct v. inversion H.
apply Env_Suc.
apply IHn. exact H.
inversion H.
intros. inversion H; subst.
simpl. apply IHn. exact H1.
Qed.

(* The intial evaluation step *)
Definition init t :=
  eval_st t null Datatypes.nil cont0.

(* A function that computes one step of the evaluation. For the most
part, it follows the definition in the paper, except that we have to
use option types everywhere because evaluation is a partial
function. *)
Definition step st :=
  match st with
    | eval_st (var n) v s k =>
      match (gamma n v) with
        | Some v' => Some (cont_st k v' s)
        | None => None
      end
    | eval_st (lambda t) v s k =>
      Some (cont_st k (closure v t) s)
    | eval_st nil v s k =>
      Some (cont_st k null s)
    | eval_st (app t0 t1) v s k =>
      Some (eval_st t0 v (v :: s) (cont1 t1 k))
    | eval_st (cons t1 t2) v s k =>
      Some (eval_st t1 v (v :: s) (cont3 t2 k))
    | eval_st (car t) v s k =>
      Some (eval_st t v s (cont5 k))
    | eval_st (cdr t) v s k =>
      Some (eval_st t v s (cont6 k))
    | cont_st (cont1 t k) v (v' :: s) =>
      Some (eval_st t v' (v :: s) (cont2 k))
    | cont_st (cont2 k) v' ((closure v t) :: s) =>
      Some (eval_st t (pair v v') s k)
    | cont_st (cont3 t1 k) v (v' :: s) =>
      Some (eval_st t1 v' (v :: s) (cont4 k))
    | cont_st (cont4 k) v (v' :: s) =>
      Some (cont_st k (pair v' v) s)
    | cont_st (cont5 k) (pair v1 v2) s =>
      Some (cont_st k v1 s)
    | cont_st (cont6 k) (pair v1 v2) s =>
      Some (cont_st k v2 s)
    | _ => None
  end.

(* A relational definition of evaluation. Again, this one is more
useful in proofs. *)
Inductive step_r : state -> state -> Prop :=
| ST_var : forall n v v' s k,
  gamma_r n v v' -> step_r (eval_st (var n) v s k) (cont_st k v' s)
| ST_lam : forall tm v s k,
  step_r (eval_st (lambda tm) v s k) (cont_st k (closure v tm) s)
| ST_nil : forall v s k,
  step_r (eval_st nil v s k) (cont_st k null s)
| ST_app : forall t0 t1 v s k,
  step_r (eval_st (app t0 t1) v s k) (eval_st t0 v (v :: s) (cont1 t1 k))
| ST_cons : forall t1 t2 v s k,
  step_r (eval_st (cons t1 t2) v s k) (eval_st t1 v (v :: s) (cont3 t2 k))
| ST_car : forall t v s k,
  step_r (eval_st (car t) v s k) (eval_st t v s (cont5 k))
| ST_cdr : forall t v s k,
  step_r (eval_st (cdr t) v s k) (eval_st t v s (cont6 k))
| ST_cont1 : forall t k v v' s,
  step_r (cont_st (cont1 t k) v (v' :: s)) (eval_st t v' (v :: s) (cont2 k))
| ST_cont2 : forall k v' v t s,
  step_r (cont_st (cont2 k) v' ((closure v t) :: s))
  (eval_st t (pair v v') s k)
| ST_cont3 : forall t1 k v v' s,
  step_r (cont_st (cont3 t1 k) v (v' :: s)) (eval_st t1 v' (v :: s ) (cont4 k))
| ST_cont4 : forall k v v' s,
  step_r (cont_st (cont4 k) v (v' :: s)) (cont_st k (pair v' v) s)
| ST_cont5 : forall k v1 v2 s,
  step_r (cont_st (cont5 k) (pair v1 v2) s) (cont_st k v1 s)
| ST_cont6 : forall k v1 v2 s,
  step_r (cont_st (cont6 k) (pair v1 v2) s) (cont_st k v2 s).

(* Proving the two are equivalent again. This is mostly just a sanity
check, although using this might it easier to automate some steps of
the type safety proofs. *)
Lemma step_equiv :
  forall s1 s2,
    step s1 = Some s2 <-> step_r s1 s2.
split.
intros.
destruct s1. destruct t.
assert (exists v', (gamma n v = Some v')).
simpl in H. destruct (gamma n v).
exists v0. reflexivity.
inversion H.
destruct H0.
simpl in H.
rewrite H0 in H.
inversion H; subst.
apply ST_var.
apply gamma_equiv. exact H0.
simpl in H. inversion H; subst.
apply ST_lam.
inversion H; subst.
apply ST_app.
inversion H; subst.
apply ST_nil.
inversion H; subst.
apply ST_cons.
inversion H; subst.
apply ST_car.
inversion H; subst.
apply ST_cdr.
destruct k.
inversion H; subst.
inversion H; subst.
destruct s.
inversion H1.
inversion H1; subst.
apply ST_cont1.
inversion H.
destruct s. 
inversion H1.
destruct v0. inversion H1. inversion H1.
inversion H1. 
apply ST_cont2.
inversion H. destruct s. inversion H1.
inversion H1. apply ST_cont3.
inversion H. destruct s; inversion H1.
apply ST_cont4.
inversion H. destruct v.
inversion H1. inversion H1. apply ST_cont5.
inversion H1. inversion H. destruct v. inversion H1.
inversion H1. apply ST_cont6.
inversion H1.
intros.
inversion H. subst.
simpl.
assert (gamma n v = Some v').
apply gamma_equiv. exact H0.
rewrite H1. reflexivity.
subst.
simpl; reflexivity.
auto. auto. auto. auto. auto. eauto. auto. auto. auto. auto. auto.
Qed.

(* A function that evaluates for up to n steps. Ideally we'd just
evaluate to completion, but Coq requires all functions to terminate so
we must bound the number of execution steps. *)
Fixpoint step_n s n :=
  match n with
    | O => Some s
    | S n' =>
      match (step s) with
        | Some (cont_st cont0 v Datatypes.nil) => 
          Some (cont_st cont0 v Datatypes.nil)
        | Some st' =>
          step_n st' n'
        | None => None
      end
  end.

(* Evaluates a term to a value, if possible in n or fewer steps. The
number of steps can be made arbitarily large. *)
Definition eval t n :=
  match (step_n (init t) n) with
    | Some (cont_st cont0 v Datatypes.nil) => Some v
    | _ => None
  end.
