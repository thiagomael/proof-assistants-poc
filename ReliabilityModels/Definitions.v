(** Basic Reliability Models Definitions **)
Require Import SPL.
Require Import RatExpr.
Require Import Markov.DTMC.
Require Import Markov.PMC.


Definition PresenceFunction : Type := Var -> SPL.Configuration -> bool.

Definition EvaluationFactory : Type := SPL.Configuration -> Evaluation.

(** ** Evaluation **)

(** Definition 7 (DTMC derivation) *)
Definition lambda (p: PMC) (w: EvaluationFactory) (c: SPL.Configuration) : DTMC :=
    eval_pmc p (w c).
