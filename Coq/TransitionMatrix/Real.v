(** * Real-valued transition matrices **)
Require Import Reals.
Require Import List.
Require Import ListSet.

Open Scope R_scope.

Require Import State.
Require Import TransitionMatrix.Definitions.
Require Import Probabilities.


Definition is_stochastic_row (r: StateMaps.t R) : Prop :=
    (forall (s: State) (v: R), StateMaps.MapsTo s v r -> is_valid_prob v)
    /\ sum_in_map r = 1.


Definition is_stochastic_matrix (m: TransitionMatrix R) : Prop :=
    forall s: State, forall r: StateMaps.t R,
        StateMaps.MapsTo s r m -> is_stochastic_row r.
