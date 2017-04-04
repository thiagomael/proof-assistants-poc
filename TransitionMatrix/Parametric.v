(** Parametric Transition Matrices **)
Require Import ListSet.
Require Import Reals.
Require Import List.

Require Import State.
Require Import TransitionMatrix.Definitions.
Require Import TransitionMatrix.Real.
Require Import RatExpr.
Require Import Probabilities.


Open Scope R_scope.

Definition Var : Type := RatExpr.Var.
Definition Var_eq_dec := RatExpr.Var_eq_dec.

(** ** Variables in the Matrix **)

Fixpoint var_set_list' (l: list (State * RatExpr)): set Var :=
match l with
  | nil       => empty_set Var
  | e :: rest => set_union Var_eq_dec (vars (snd e)) (var_set_list' rest)
end.

Definition var_set' (r: StateMaps.t RatExpr): set Var :=
    var_set_list' (StateMaps.elements r).

Fixpoint var_set_list (l: list (State * StateMaps.t RatExpr)): set Var :=
match l with
  | nil       => empty_set Var
  | e :: rest => set_union Var_eq_dec (var_set' (snd e)) (var_set_list rest)
end.

Definition var_set (m: TransitionMatrix RatExpr): set Var :=
    var_set_list (StateMaps.elements m).

Lemma vars_injection: forall (m: TransitionMatrix RatExpr) (r: StateMaps.t RatExpr) (s: State) (x: Var),
    StateMaps.MapsTo s r m -> In x (var_set' r) -> In x (var_set m).
Proof.
    intros m r s x H_mapsto H_x_in_r.
    unfold var_set.
    apply StateMaps.elements_1 in H_mapsto.
    elim H_mapsto.
    - (* r is the first element *)
      intros.
      red in H. red in H. destruct H as [H_fst H_snd].
      unfold var_set_list.
      rewrite <- H_snd. simpl.
      apply set_union_intro1. assumption.
    - (* r is in the tail of elements list *)
      intros.
      unfold var_set_list.
      apply set_union_intro2. assumption.
Qed.


(** ** Evaluation **)

Definition eval_row (r: StateMaps.t RatExpr) (u: Evaluation) : StateMaps.t R :=
    StateMaps.map (fun val => eval_expr val u) r.

Definition eval_matrix (m: TransitionMatrix RatExpr) (u: Evaluation): TransitionMatrix R :=
    StateMaps.map (fun r => eval_row r u) m.

Definition expr_sum_in_map (m: StateMaps.t RatExpr) : RatExpr :=
    sum_f_in_map m expr_sum (Const 0).

Lemma commutative_eval_elements:
  forall (m: StateMaps.t RatExpr) (u: Evaluation),
      let eval_snd := (fun p => (fst p, eval_expr (snd p) u)) in
      StateMaps.elements (eval_row m u) = map eval_snd (StateMaps.elements m).
Proof.
    intros.
    unfold eval_row. unfold StateMaps.elements. unfold StateMaps.Raw.elements.
    unfold StateMaps.map. simpl.
    induction StateMaps.this.
    - reflexivity.
    - simpl. rewrite IHt.
      destruct a as [k v]. reflexivity.
Qed.

Lemma eval_sum_in_map:
    forall (m: StateMaps.t RatExpr) (u: Evaluation),
        eval_expr (expr_sum_in_map m) u = sum_in_map (eval_row m u).
Proof.
    intros.
    unfold expr_sum_in_map.
    unfold sum_in_map. unfold sum_f_in_map.
    unfold sum_f.
    rewrite commutative_eval_elements.
    induction (StateMaps.elements (elt:=RatExpr) m).
    - (* nil *)
      reflexivity.
    - (* a:: l *)
      rewrite map_cons.
      unfold fold_right. simpl.
      rewrite distributive_eval_sum.
      unfold fold_right in IHl.
      rewrite IHl. reflexivity.
Qed.

Lemma commutative_eval_find:
    forall (m: TransitionMatrix RatExpr) (s: State) (u: Evaluation),
        StateMaps.In s m ->
        StateMaps.find s (eval_matrix m u) = option_map (fun row => eval_row row u) (StateMaps.find s m).
Proof.
    intros m s u H_s_in_m.
    unfold eval_matrix.
    inversion H_s_in_m as [e H_mapsto].
    apply StateMaps.find_1 in H_mapsto. rewrite -> H_mapsto.
    apply StateMaps.find_2 in H_mapsto.
    apply StateMaps.map_1 with (elt':=StateMaps.t R) (f:=fun r : StateMaps.t RatExpr => eval_row r u) in H_mapsto.
    apply StateMaps.find_1 in H_mapsto. rewrite -> H_mapsto.
    unfold option_map. reflexivity.
Qed.

Lemma commutative_eval_mapsto:
    forall (r: StateMaps.t RatExpr) (s: State) (u: Evaluation) (v: R),
        StateMaps.MapsTo s v (eval_row r u) ->
            ( exists e: RatExpr, StateMaps.MapsTo s e r
              /\ v = eval_expr e u ).
Admitted.

Lemma eval_matrix_in:
    forall (m: TransitionMatrix RatExpr) (s: State) (u: Evaluation),
        StateMaps.In s m <-> StateMaps.In s (eval_matrix m u).
Proof.
    intros. unfold eval_matrix.
    split.
    - (* -> *)
      intros.
      rewrite in_mapsto in H. elim H. intros.
      rewrite in_mapsto. exists (eval_row x u).
      apply StateMaps.map_1 with (f:=(fun r : StateMaps.t RatExpr => eval_row r u)).
      apply H0.
    - (* <- *)
      intros. apply StateMaps.map_2 in H. apply H.
Qed.

Lemma eval_matrix_mapsto:
    forall (m: TransitionMatrix RatExpr) (s: State) (r: StateMaps.t RatExpr) (u: Evaluation),
        StateMaps.MapsTo s r m -> StateMaps.MapsTo s (eval_row r u) (eval_matrix m u).
Proof.
    intros m s r u. unfold eval_matrix. apply StateMaps.map_1.
Qed.

Lemma eval_matrix_evaluated_expr:
    forall (m: TransitionMatrix RatExpr) (s: State) (r: StateMaps.t R) (u: Evaluation),
        StateMaps.MapsTo s r (eval_matrix m u) ->
            ( exists e: StateMaps.t RatExpr, StateMaps.MapsTo s e m
              /\ r = eval_row e u ).
Proof.
Admitted.

Lemma sum_in_list: forall (l: list RatExpr) (e: RatExpr) (a0: RatExpr),
    In e l -> fold_left expr_sum l a0 = expr_sum e (fold_left expr_sum (remove RatExpr.eq_dec e l) a0).
Admitted.

Lemma sum_in_map: forall (r: StateMaps.t RatExpr) (s: State) (e: RatExpr),
    StateMaps.MapsTo s e r ->
    expr_sum_in_map r = expr_sum e (expr_sum_in_map (StateMaps.remove s r)).
Admitted.

Lemma sum_zero_in_map:
    forall (r: StateMaps.t RatExpr),
        (forall s: State, StateMaps.In s r -> StateMaps.MapsTo s (Const 0) r) ->
            expr_sum_in_map r = Const 0.
Proof.
    intros.
    unfold expr_sum_in_map. unfold sum_f_in_map.
    assert (H':
        (forall s: State, StateMaps.In s r -> StateMaps.MapsTo s (Const 0) r ) ->
          (forall p: State * RatExpr, (In p (StateMaps.elements r)) -> snd p = Const 0)).
    {
        intros.
        specialize (H0 (fst p)).
        apply SetoidList.In_InA with (eqA:=StateMaps.eq_key_elt (elt:=RatExpr)) in H1.
        - destruct p as [s e].
          apply StateMaps.elements_2 in H1. assert (H':= H1).
          simpl in H0.
          apply mapsto_in in H1. apply H0 in H1.
          apply StateMapsFacts.MapsTo_fun with (e':=Const 0) (e:=e) in H1.
          + auto.
          + assumption.
        - exact (StateMapsProperties.eqke_equiv RatExpr).
    }
    induction (StateMaps.elements (elt:=RatExpr) r).
    - (* empty list *)
      reflexivity.
    - (* a::l *)
      eapply H' in H.
      + (* main goal *)
        unfold sum_f. unfold fold_right.
        unfold sum_f in IHl. unfold fold_right in IHl.
        rewrite IHl.
        * rewrite H. simpl. rewrite Rplus_0_r. reflexivity.
        * intros.
          { apply H' with (p:=p) in H0.
            - assumption.
            - apply in_cons. assumption.
          }
      + (* proof obligation *)
        apply in_eq.
Qed.

(** ** Evaluation and stochasticity **)
Definition expr_is_stochastic_row (r: StateMaps.t RatExpr) : Prop :=
    (forall (s: State) (e: RatExpr), StateMaps.MapsTo s e r -> expr_is_valid_prob e)
    /\ expr_sum_in_map r = Const 1.

Lemma eval_stochastic_row:
    forall (r: StateMaps.t RatExpr) (u: Evaluation),
        expr_is_stochastic_row r -> is_stochastic_row (eval_row r u).
Proof.
    intros.
    unfold expr_is_stochastic_row in H.
    destruct H as [H_valid_prob H_sum_1].
    unfold is_stochastic_row. split.
    - (* all values are valid probabilities *)
      intros.
      apply commutative_eval_mapsto in H.
      inversion H as [e [H_s_mapsto_e H_v_eval_e]].
      apply H_valid_prob in H_s_mapsto_e.
      rewrite H_v_eval_e.
      apply valid_prob_preservation. assumption.
    - (* sum is 1 *)
      rewrite <- eval_sum_in_map.
      rewrite H_sum_1. reflexivity.
Qed.