Require Import Reals.
Require Import ListSet.
Require Import List.

Module Rome.

Open Scope R_scope.
Open Scope bool_scope.

Definition is_valid_prob (p: R): Prop := 0 <= p <= 1.
Definition opt_is_valid_prob (o: option R): Prop :=
match o with
  | Some p => 0 <= p <= 1
  | None   => False
end.

Require Import Coq.FSets.FMapWeakList.


Parameter State : Type.
(**
   The following hypothesis is needed if we use bool predicates (instead of Prop).
   This happens because Coq lacks the excluded middle axiom (P V ~P).
*)
Hypothesis State_eq_dec : forall x y:State, {x = y} + {x <> y}.

Module DecidableState.
  (* Eq module type *)
  Definition t := State.
  Definition eq : t -> t -> Prop := @eq t.
  (* IsEqOrig module type: defines eq as an equivalence class *)
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  (* HasEqDec module type: equality is decidable *)
  Definition eq_dec := State_eq_dec.
End DecidableState.


Module StateMaps := FMapWeakList.Make DecidableState.
Definition TransitionMatrix (t: Type) := StateMaps.t (StateMaps.t t).


Definition summation {S: Type} (l: list (prod S R)) : R :=
    fold_left (fun (a: R) ( e: prod S R ) => a + (snd e) ) l 0.
Definition sum_in_map (m: StateMaps.t R) : R := summation (StateMaps.elements m).

Parameter Var : Type.
Hypothesis Var_eq_dec : forall x y:Var, {x = y} + {x <> y}.


Inductive RatExpr : Type :=
  | Const:  R -> RatExpr
  | OneVar: Var -> RatExpr
  | Sum:    RatExpr -> RatExpr -> RatExpr
  | Sub:    RatExpr -> RatExpr -> RatExpr
  | Mul:    RatExpr -> RatExpr -> RatExpr
  | Div:    RatExpr -> RatExpr -> RatExpr.


Definition Evaluation (X: Type) := X -> R.
Variable eval_expr : RatExpr -> Evaluation Var -> R.

Fixpoint vars (e: RatExpr) : set Var :=
  match e with
  | Const _  => empty_set Var
  | OneVar v => set_add Var_eq_dec v (empty_set Var)
  | Sum a b  => set_union Var_eq_dec (vars a) (vars b)
  | Sub a b  => set_union Var_eq_dec (vars a) (vars b)
  | Mul a b  => set_union Var_eq_dec (vars a) (vars b)
  | Div a b  => set_union Var_eq_dec (vars a) (vars b)
  end.



Section NonParametric.
Record DTMC : Type := { S:  set State;
                        s0: State;
                        P:  TransitionMatrix R;
                        T:  set State }.




Definition bimap {T: Type} (s s': State) (m: TransitionMatrix T): option T :=
  match StateMaps.find s m with
  | Some val => StateMaps.find s' val
  | None     => None
  end.

Notation "m [ s , s' ]" := (bimap s s' m) (at level 0).

(** Well-formed DTMC *)
Definition wf_DTMC (d: DTMC) : Prop :=
  (In d.(s0) d.(S))
  /\ (incl d.(T) d.(S))
  /\ forall s s': State, opt_is_valid_prob (d.(P)[s, s'])
  /\ forall s: State,
       In s d.(S) -> option_map sum_in_map (StateMaps.find s d.(P)) = Some 1.

End NonParametric.


(** Probability of going from a given state to any other within a set of target states. *)
Variable pr_set: DTMC -> State -> set State -> R.

Lemma wf_dtmc_yields_valid_probability:
  forall (d: DTMC) (s: State) (Tgt: set State),
    (wf_DTMC d /\ In s d.(S) /\ incl Tgt d.(T)) -> is_valid_prob (pr_set d s Tgt).
Admitted.


(** Probability of going from a given state to another within a DTMC. *)
Definition pr (d: DTMC) (s t: State): R := pr_set d s (set_add State_eq_dec t (empty_set State)).




Module Parametric.

Record PMC : Type := { S:  set State;
                       s0: State;
                       X:  set Var;
                       P:  TransitionMatrix (RatExpr + R);
                       T:  set State }.
(** Well-formed PMC *)
Definition wf_PMC (p: PMC) : Prop :=
  (In p.(s0) p.(S))
  /\ (incl p.(T) p.(S)).
  (*/\ forall e: RatExpr, In e P -> incl (vars e) X. *)

Variable eval_pmc : PMC -> Evaluation Var -> DTMC.

(** Hahn's algorithm. *)
Variable alpha_v : PMC -> RatExpr.

Definition well_defined_evaluation (p: PMC) (u: Evaluation Var) : Prop := wf_DTMC (eval_pmc p u).

(** Hahn's lemma *)
Lemma parametric_reachability_soundness:
 forall (p: PMC) (u: Evaluation Var),
    (well_defined_evaluation p u /\ wf_PMC p)
    -> (pr_set (eval_pmc p u) p.(s0) p.(T)) = eval_expr (alpha_v p) u.
Proof.
Admitted.

End Parametric.



End Rome.