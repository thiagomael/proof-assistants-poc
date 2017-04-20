(** ** DTMC *)
Require Import Reals.
Require Import List.
Require Import ListSet.

Open Scope R_scope.

Require Import State.
Require Import TransitionMatrix.Definitions.
Require Import TransitionMatrix.Real.
Require Import Probabilities.


Record DTMC : Type := { S:  set State;
                        s0: State;
                        P:  TransitionMatrix R;
                        T:  set State }.


(** Well-formed DTMC *)

Definition wf_DTMC (d: DTMC) : Prop :=
  (In d.(s0) d.(S))
  /\ (incl d.(T) d.(S))
  /\ (forall s: State, In s d.(S) <-> StateMaps.In s d.(P))
  /\ (is_stochastic_matrix d.(P)).


(** Probability of going from a given state to any other within a set of target states. *)

Variable pr_set: DTMC -> State -> set State -> R.

Hypothesis wf_dtmc_yields_valid_probability:
  forall (d: DTMC) (s: State) (Tgt: set State),
    (wf_DTMC d /\ In s d.(S) /\ incl Tgt d.(T)) -> is_valid_prob (pr_set d s Tgt).


(** Probability of going from a given state to another within a DTMC. *)

Definition pr (d: DTMC) (s t: State): R := pr_set d s (set_add State.eq_dec t (empty_set State)).
