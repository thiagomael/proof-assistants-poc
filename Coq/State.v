(** * Transition Matrix *)

Parameter State : Type.

(**
   The following hypothesis is needed if we use bool predicates (instead of Prop).
   This happens because Coq lacks the excluded middle axiom (P V ~P).
*)

Hypothesis eq_dec : forall x y:State, {x = y} + {x <> y}.

Module DecidableState.
  (* Eq module type *)
  Definition t := State.
  Definition eq : t -> t -> Prop := @eq t.
  (* IsEqOrig module type: defines eq as an equivalence class *)
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  (* HasEqDec module type: equality is decidable *)
  Definition eq_dec := eq_dec.
End DecidableState.
