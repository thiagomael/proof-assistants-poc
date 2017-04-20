(** ** PMC *)
Require Import List.
Require Import ListSet.

Require Import State.
Require Import RatExpr.
Require Import TransitionMatrix.Definitions.
Require Import TransitionMatrix.Parametric.
Require Import Markov.DTMC.

(** Definition 1 (PMC) *)
Record PMC : Type := { S:  set State;
                       s0: State;
                       X:  set Var;
                       P:  TransitionMatrix RatExpr;
                       T:  set State }.

(** Well-formed PMC: *)

Definition wf_PMC (p: PMC) : Prop :=
  (In p.(s0) p.(S))
  /\ (incl p.(T) p.(S))
  /\ (forall s: State, In s p.(S) <-> StateMaps.In s p.(P))
  /\ (p.(X) = var_set p.(P)).

(** Definition 1.5 (PMC Evaluation) *)
Definition eval_pmc (p: PMC) (e: Evaluation) : DTMC :=
    Build_DTMC p.(S) p.(s0) (eval_matrix p.(P) e) p.(T).

(** Definition 2 (Well-defined evaluation) *)
(** Definition: an evaluation is well-defined iff the evaluated PMC is a well-formed DTMC. *)
Definition well_defined_evaluation (p: PMC) (u: Evaluation) : Prop := wf_DTMC (eval_pmc p u).


(** Hahn's algorithm. *)
Variable alpha_v : PMC -> RatExpr.

(** Lemma 1 (Hahn's lemma) *)
Hypothesis parametric_reachability_soundness:
 forall (p: PMC) (u: Evaluation),
    (well_defined_evaluation p u /\ wf_PMC p)
    -> (DTMC.pr_set (eval_pmc p u) p.(s0) p.(T)) = eval_expr (alpha_v p) u.
