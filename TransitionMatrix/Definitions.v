(** Transition Matrices with arbitrary values **)
Require Import Reals.
Require Import Coq.FSets.FMapWeakList.
Require Import Coq.FSets.FMapFacts.

Open Scope R_scope.

Require Import State.

Module StateMaps := FMapWeakList.Make DecidableState.
Module StateMapsFacts := WFacts_fun DecidableState StateMaps.

Definition TransitionMatrix (t: Type) := StateMaps.t (StateMaps.t t).

Definition sum_f {S T: Type} (l: list (prod S T)) (f: T -> T -> T) (t0: T) : T :=
    fold_right (fun ( e: prod S T ) (t: T) => f t (snd e) ) t0 l.

Definition sum_f_in_map {T: Type} (m: StateMaps.t T) (f: T -> T -> T) (t0: T) : T :=
    sum_f (StateMaps.elements m) f t0.

Definition sum_in_map (m: StateMaps.t R) : R := sum_f_in_map m Rplus 0.


(** ** Correspondence between In and MapsTo **)

Lemma in_mapsto {T: Type}:
    forall (r: StateMaps.t T) (s: State),
        StateMaps.In s r <-> exists v: T, StateMaps.MapsTo s v r.
Proof.
    intros. split.
    - auto.
    - auto.
Qed.

Lemma mapsto_in {T: Type}:
    forall (r: StateMaps.t T) (s: State),
        forall v: T, StateMaps.MapsTo s v r -> StateMaps.In s r.
Proof.
    intros. rewrite in_mapsto. exists v. apply H.
Qed.
