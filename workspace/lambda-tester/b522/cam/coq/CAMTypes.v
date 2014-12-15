(* Here, we define an extremely simple type system for the Categorical
Abstract Machine, and prove type safety by means of progress and
preservation. *)

Require Import CAM.

(* Syntax of types *)
Inductive type :=
| func (t1 t2 : type)
| pair (t1 t2 : type)
| null_type.

(* Typing environments *)
Inductive type_env :=
| empty
| extend (g : type_env) (t : type).

(* Type environment lookup *)
Fixpoint lookup (n : nat) (g : type_env) :=
  match g with 
    | extend g' t =>
      match n with 
        | 0 => Some t
        | S n' => lookup n' g'
      end
    | _ => None
  end.

(* Typing judgments for terms. In this case, we chose only to use a
relational definition. *)
Inductive type_term (g : type_env) :
  term -> type -> Prop :=
| T_Var : forall n t, lookup n g = Some t -> type_term g (var n) t
| T_Lam : forall t1 t2 e',
  type_term (extend g t1) e' t2
  -> type_term g (lambda e') (func t1 t2)
| T_App : forall e1 e2 t' t, type_term g e1 (func t' t) 
  -> type_term g e2 t' -> type_term g (app e1 e2) t
| T_Nil : type_term g nil null_type
| T_Cons : forall e1 e2 t1 t2,
  type_term g e1 t1 -> type_term g e2 t2 
  -> type_term g (cons e1 e2) (pair t1 t2)
| T_Car : forall e' t t', type_term g e' (pair t t')
  -> type_term g (car e') t
| T_Cdr : forall e' t t', type_term g e' (pair t' t)
  -> type_term g (cdr e') t.

(* Mutually inductive relational definitions of environment
consistency and the value typing judgment. *)
Inductive val_type_consistent_r : type_env -> value -> Prop :=
| Consistent_Base : val_type_consistent_r empty null
| Consistent_Step : 
  forall g' t v1 v2, val_type_consistent_r g' v1 -> value_type_r v2 t
    -> val_type_consistent_r (extend g' t) (CAM.pair v1 v2)
with value_type_r : value -> type -> Prop :=
| VT_null : value_type_r null null_type
| VT_pair : forall v1 v2 t1 t2,
  value_type_r v1 t1 -> value_type_r v2 t2 
  -> value_type_r (CAM.pair v1 v2) (pair t1 t2)
| VT_closure : forall gamma env body t1 t2,
  val_type_consistent_r gamma env ->
  type_term (extend gamma t1) body t2 ->
  value_type_r (closure env body) (func t1 t2).

(* This is Lemma 2 from our project submission. It says if a typing
environment and a runtime environment are consistent, then variable
lookups in both will have the correct types. *)
Lemma lookup_consistency :
  forall n Gamma v v' t,
    val_type_consistent_r Gamma v -> type_term Gamma (var n) t ->
    (gamma n v) = Some v' ->
    value_type_r v' t.
induction n.
intros.
inversion H.
subst.
contradict H1.
simpl. discriminate.
subst.
simpl in H1.
inversion H1.
inversion H0. subst.
simpl in H6. inversion H6. subst. exact H3.
intros.
inversion H. subst.
contradict H1. simpl. discriminate.
subst.
simpl in H1. 
inversion H. subst.
apply (IHn g' v1).
exact H7.
apply T_Var.
inversion H0. subst. simpl in H5. exact H5.
exact H1.
Qed.

(* A relational definition of continuation type rules. *)
Inductive type_cont_r : list value -> cont -> type -> Prop :=
| TC_CONT0 : forall t, type_cont_r Datatypes.nil cont0 (func t t)
| TC_CONT1 : forall Gamma v tm t1 t2 s k t, 
  val_type_consistent_r Gamma v -> 
  type_term Gamma tm t1 -> 
  type_cont_r s k (func t2 t) 
  -> type_cont_r (v::s) (cont1 tm k) (func (func t1 t2) t)
| TC_CONT2 : forall v s k t1 t2 t, 
  value_type_r v (func t1 t2) 
  -> type_cont_r s k (func t2 t) 
  -> type_cont_r (v::s) (cont2 k) (func t1 t)
| TC_CONT3 : forall Gamma v s tm k t1 t2 t, 
  val_type_consistent_r Gamma v -> 
  type_term Gamma tm t2 -> 
  type_cont_r s k (func (pair t1 t2) t)
  -> type_cont_r (v::s) (cont3 tm k) (func t1 t)
| TC_CONT4 : forall v s k t1 t2 t, 
  value_type_r v t1 -> 
  type_cont_r s k (func (pair t1 t2) t) 
  -> type_cont_r (v::s) (cont4 k) (func t2 t)
| TC_CONT5 : forall s k t1 t2 t, 
  type_cont_r s k (func t1 t)
  -> type_cont_r s (cont5 k) (func (pair t1 t2) t)
| TC_CONT6 : forall s k t1 t2 t, 
  type_cont_r s k (func t2 t)
  -> type_cont_r s (cont6 k) (func (pair t1 t2) t).

(* A relational definition of the typing rules for machine states. *)
Inductive type_state_r : state -> type -> Prop :=
| TS_Eval : forall Gamma v tm s k t1 t, 
  val_type_consistent_r Gamma v -> 
  type_term Gamma tm t1 -> 
  type_cont_r s k (func t1 t)
  -> type_state_r (eval_st tm v s k) t
| TS_Cont : forall k v s t1 t, type_cont_r s k (func t1 t)
  -> value_type_r v t1
  -> type_state_r (cont_st k v s) t.

(* This lemma states that the initial machine translation preserves
types. *)
Lemma type_init :
  forall tm ty, 
    type_term empty tm ty 
    -> type_state_r (init tm) ty.
intros.
unfold init.
apply (TS_Eval empty _ _ _ _ ty _).
apply Consistent_Base.
auto.
apply TC_CONT0.
Qed.

(* The Preservation Theorem *)
Theorem preservation:
  forall s t, type_state_r s t -> forall s', step_r s s' -> type_state_r s' t.
intros s t H.
inversion H.
intros.
inversion H1. inversion H5.
subst. inversion H9; subst. clear H9.
apply (TS_Cont _ _ _ t1 _).
exact H2. 
apply (lookup_consistency n Gamma v). auto. auto.
apply gamma_equiv. auto.
subst.
apply (TS_Cont _ _ _ t1 _).
exact H2.
inversion H10. subst.
apply (TS_Cont _ _ _ t1 _); auto.
inversion H10.
subst. apply (TS_Eval Gamma _ _ _ _ t1 _). auto.
inversion H10. inversion H10.
subst. inversion H10. subst. inversion H10. subst. inversion H10.
subst. 
inversion H5. subst.
subst; apply (TS_Cont _ _ _ (func t2 t3) _). exact H2.
subst. inversion H5. subst.
apply (VT_closure Gamma). auto. auto. subst.
inversion H5. subst.
apply (TS_Eval Gamma _ _ _ _ (func t' t1)).
auto. auto.
apply (TC_CONT1 Gamma). auto. auto. auto.
subst.
inversion H5. subst.
apply (TS_Cont _ _ _ null_type). auto.
subst. inversion H5. subst.
apply VT_null.
subst.
inversion H5.
apply (TS_Eval Gamma _ _ _ _ t2). auto. auto.
apply (TC_CONT3 Gamma _ _ _ _ _ t3). auto. auto. auto.
subst. inversion H5. subst.
apply (TS_Eval Gamma _ _ _ _ (pair t1 t')). auto. auto.
apply (TC_CONT5). auto.
subst. inversion H5. subst. 
apply (TS_Eval Gamma _ _ _ _ (pair t' t1)). auto. auto.
apply (TC_CONT6). auto.
intros.
inversion H3. subst. inversion H; subst.
clear H5. inversion H4. subst.
inversion H0. subst.
apply (TS_Eval Gamma _ _ _ _ t3). auto. auto.
apply (TC_CONT2 _ _ _ _ t4). auto.
inversion H0. subst. auto. subst.
inversion H. subst.
inversion H8. subst. inversion H11; subst.
apply (TS_Eval (extend gamma t0) _ _ _ _ t5).
apply Consistent_Step. auto. auto. auto. auto.
subst. inversion H; subst. inversion H7; subst.
apply (TS_Eval Gamma _ _ _ _ (t5)). auto. auto.
apply (TC_CONT4 _ _ _ t3). auto. auto.
subst.
inversion H8. subst.
apply (TS_Cont _ _ _ (pair t2 t0)). auto.
apply VT_pair. auto. auto.
subst.
inversion H8. subst.
apply (TS_Cont _ _ _ t2). auto.
inversion H9; subst. auto.
subst.
inversion H8. subst.
apply (TS_Cont _ _ _ t3). auto.
inversion H9; subst. auto.
Qed.

(* This lemma is used in the progress proof. It says that if we look
up a variable in a well-typed environment, we'll indeed find a
value. *)
Lemma lookup_exists :
  forall n Gamma v t,
    val_type_consistent_r Gamma v -> 
    type_term Gamma (var n) t 
    -> exists v', gamma n v = Some v'.
induction n.
intros.
inversion H. subst.
inversion H0. subst.
simpl in H2. inversion H2.
subst.
exists v2.
simpl. reflexivity.
intros.
destruct v.
inversion H. subst. inversion H0. subst. simpl in H2. inversion H2.
destruct Gamma.
inversion H.
apply (IHn Gamma _ t).
inversion H. subst. exact H4.
inversion H0. subst.
apply T_Var.
simpl in H2. exact H2.
inversion H.
Qed.

(* The Progress Theorem *)
Theorem progress :
  forall s t, type_state_r s t -> 
  (exists v, s = (cont_st cont0 v Datatypes.nil)) \/
  exists s', step_r s s'.
intros.
destruct s.
right.
destruct t0.
inversion H. subst.
inversion H6. subst.
case (lookup_exists n Gamma v t1).
exact H5. exact H6.
intros.
exists (cont_st k x s).
apply ST_var.
apply gamma_equiv. exact H0.
exists (cont_st k (closure v t0) s).
apply ST_lam.
exists (eval_st t0_1 v (v::s) (cont1 t0_2 k)).
apply ST_app.
exists (cont_st k null s).
apply ST_nil.
exists (eval_st t0_1 v (v::s) (cont3 t0_2 k)).
apply ST_cons.
exists (eval_st t0 v s (cont5 k)).
apply ST_car.
exists (eval_st t0 v s (cont6 k)).
apply ST_cdr.
destruct k.
left.
exists v.
destruct s.
reflexivity.
inversion H; subst.
inversion H4.
right.
destruct s.
inversion H; subst.
inversion H4.
exists (eval_st t0 v0 (v::s) (cont2 k)).
apply ST_cont1.
right.
destruct s.
inversion H; subst.
inversion H4.
inversion H; subst. 
inversion H4; subst.
inversion H6; subst.
exists (eval_st body (CAM.pair env v) s k).
apply ST_cont2.
right.
destruct s.
inversion H; subst.
inversion H4.
exists (eval_st t0 v0 (v::s) (cont4 k)).
apply ST_cont3.
right.
destruct s.
inversion H; subst.
inversion H4.
exists (cont_st k (CAM.pair v0 v) s).
apply ST_cont4.
right.
destruct v.
inversion H; subst.
inversion H5; subst.
inversion H4.
exists (cont_st k v1 s).
apply ST_cont5.
inversion H; subst.
inversion H4; subst.
inversion H5; subst.
right.
destruct v.
inversion H; subst.
inversion H5; subst; inversion H4.
exists (cont_st k v2 s).
apply ST_cont6.
inversion H; subst.
inversion H4; subst.
inversion H5; subst.
Qed. 
