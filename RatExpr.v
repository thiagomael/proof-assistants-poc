Require Import Reals.
Require Import Raxioms.
Require Import RIneq.
Require Import List.
Require Import ListSet.
Require Import Logic.

Open Scope R_scope.

Require Import Probabilities.

(** * Rational Expressions *)

Parameter Var : Type.
Hypothesis Var_eq_dec : forall x y:Var, {x = y} + {x <> y}.

Inductive RatExpr : Type :=
  | Const:  R -> RatExpr
  | OneVar: Var -> RatExpr
  | Sum:    RatExpr -> RatExpr -> RatExpr
  | Sub:    RatExpr -> RatExpr -> RatExpr
  | Mul:    RatExpr -> RatExpr -> RatExpr
  | Div:    RatExpr -> RatExpr -> RatExpr
  | Minus:  RatExpr -> RatExpr.

Hypothesis eq_dec : forall x y: RatExpr, {x = y} + {x <> y}.

Definition const (e: RatExpr): Prop :=
match e with
  | Const p => True
  | _ => False
end.

Definition expr_sum (e1 e2: RatExpr): RatExpr :=
match e1, e2 with
  | Const r1, Const r2 => Const (r1 + r2)
  | _, _ => Sum e1 e2
end.


Fixpoint vars (e: RatExpr) : set Var :=
match e with
  | Const _  => empty_set Var
  | OneVar v => set_add Var_eq_dec v (empty_set Var)
  | Minus a  => vars a
  | Sum a b  => set_union Var_eq_dec (vars a) (vars b)
  | Sub a b  => set_union Var_eq_dec (vars a) (vars b)
  | Mul a b  => set_union Var_eq_dec (vars a) (vars b)
  | Div a b  => set_union Var_eq_dec (vars a) (vars b)
end.


(** Evaluation of variables **)
Definition Evaluation: Type := Var -> R.

Fixpoint eval_expr (e: RatExpr) (u: Evaluation) : R :=
match e with
  | Const r  => r
  | OneVar v => u v
  | Minus a  => - (eval_expr a u)
  | Sum a b  => (eval_expr a u) + (eval_expr b u)
  | Sub a b  => (eval_expr a u) - (eval_expr b u)
  | Mul a b  => (eval_expr a u) * (eval_expr b u)
  | Div a b  => (eval_expr a u) / (eval_expr b u)
end.

(** Extensional equality of expressions. **)
Inductive eq: RatExpr -> RatExpr -> Prop :=
  | eq_refl: forall a: RatExpr, eq a a
  | eq_var: forall a b: RatExpr,
              ( (forall u: Evaluation, (eval_expr a u = eval_expr b u))
                -> eq a b ).

Axiom custom_eq: forall a b: RatExpr, eq a b <-> a = b.

(** ** Expression arithmetics *)
Theorem expr_0_identity: forall a: RatExpr, Sum a (Const 0) =  a.
Proof.
    intros. rewrite <- custom_eq with (a:=Sum a (Const 0)).
    apply eq_var. intros. simpl. apply Rplus_0_r.
Qed.

Theorem expr_0_nonnegative: Const 0 = Minus (Const 0).
Proof.
    intros. rewrite <- custom_eq.
    apply eq_var. intros. simpl.
    rewrite Ropp_0. reflexivity.
Qed.

Theorem expr_sum_commutative: forall a b: RatExpr, Sum a b = Sum b a.
Proof.
    intros. rewrite <- custom_eq.
    apply eq_var. intros. simpl.
    apply Rplus_comm.
Qed.

Theorem expr_sum_commutative':
    forall a b: RatExpr, expr_sum a b = expr_sum b a.
Proof.
    intros.
    destruct a; destruct b;
        simpl;
        try rewrite Rplus_comm;
        try apply expr_sum_commutative;
        try trivial.
Qed.

Theorem expr_sum_associative: forall a b c: RatExpr, Sum a (Sum b c) = Sum (Sum a b) c.
Proof.
    intros. rewrite <- custom_eq.
    apply eq_var. intros. simpl.
    rewrite Rplus_assoc. reflexivity.
Qed.

Theorem expr_sum_associative': forall a b c: RatExpr, expr_sum a (expr_sum b c) = expr_sum (expr_sum a b) c.
Proof.
    intros.
    destruct a; destruct b; destruct c;
        simpl;
        try apply expr_sum_associative;
        try rewrite Rplus_assoc;
        try reflexivity;
        try rewrite <- custom_eq;
        try apply eq_var;
        try intros;
        try simpl;
        try rewrite ?Rplus_assoc; (* rewrite as many times as possible *)
        try reflexivity.
Qed.

Theorem expr_sum_cancelation: forall a: RatExpr, Sum a (Minus a) = Const 0.
Proof.
    intros. rewrite <- custom_eq.
    apply eq_var. intros. simpl.
    apply Rplus_opp_r.
Qed.

Theorem expr_sub_minus: forall a b: RatExpr, Sub a b = Sum a (Minus b).
Proof.
    intros. rewrite <- custom_eq.
    apply eq_var. intros. simpl.
    reflexivity.
Qed.


Lemma distributive_eval_sum:
    forall (a b: RatExpr) (u: Evaluation),
        eval_expr (expr_sum a b) u = eval_expr a u + eval_expr b u.
Proof.
    intros.
    destruct a; destruct b; simpl; reflexivity.
Qed.


(** ** Expressions and probabilities **)

Definition expr_is_valid_prob (r: RatExpr): Prop :=
match r with
  | Const p => is_valid_prob p
  | _ => False
end.


Lemma valid_prob_preservation:
    forall (e: RatExpr) (u: Evaluation),
        expr_is_valid_prob e -> is_valid_prob (eval_expr e u).
Proof.
    intros. induction e.
    - apply H.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H.
Qed.

Definition stochastic_evaluation (u: Evaluation) (X: set Var): Prop :=
    forall x: Var, In x X -> is_valid_prob (u x).
