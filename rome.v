Require Import Reals.
Require Import ListSet.
Require Import List.
Require Import Coq.FSets.FMapWeakList.
Require Import Coq.FSets.FMapFacts.

Require Import Coq.Classes.RelationClasses.

Load fm.

Module Rome.

Open Scope R_scope.
Open Scope bool_scope.

Definition is_valid_prob (p: R): Prop := 0 <= p <= 1.
Definition opt_is_valid_prob (o: option R): Prop :=
match o with
  | Some p => 0 <= p <= 1
  | None   => False
end.


(** * Transition Matrix *)

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
Module StateMapsFacts := WFacts_fun DecidableState StateMaps.

Definition TransitionMatrix (t: Type) := StateMaps.t (StateMaps.t t).

Definition sum_f {S T: Type} (l: list (prod S T)) (f: T -> T -> T) (t0: T) : T :=
    fold_left (fun (t: T) ( e: prod S T ) => f t (snd e) ) l t0.

Definition sum_f_in_map {T: Type} (m: StateMaps.t T) (f: T -> T -> T) (t0: T) : T :=
    sum_f (StateMaps.elements m) f t0.

Definition summation {S: Type} (l: list (prod S R)) : R :=
    sum_f l Rplus 0.
Definition sum_in_map (m: StateMaps.t R) : R := sum_f_in_map m Rplus 0.


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

Hypothesis Expr_eq_dec : forall x y: RatExpr, {x = y} + {x <> y}.

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


Definition expr_sub (e1 e2: RatExpr): RatExpr :=
match e1, e2 with
  | Const r1, Const r2 => Const (r1 - r2)
  (*| OneVar v1, OneVar v2 => if @eq Var v1 v2 then Const 0 else Sub e1 e2 *) (*How do I define equality of variables?? *)
  | _, _ => Sub e1 e2
end.

(** ** Expression arithmetics *)
Axiom expr_0_identity: forall a: RatExpr, Sum a (Const 0) = a.
Axiom expr_0_nonnegative: Const 0 = Minus (Const 0).

Axiom expr_sum_commutative: forall a b: RatExpr, Sum a b = Sum b a.
Axiom expr_sum_associative: forall a b c: RatExpr, Sum a (Sum b c) = Sum (Sum a b) c.
Axiom expr_sum_cancelation: forall a: RatExpr, Sum a (Minus a) = Const 0.

Axiom expr_sub_minus: forall a b: RatExpr, Sub a b = Sum a (Minus b).

Axiom expr_mul_cancelation: forall a b: RatExpr, Mul a (Div b a) = b.


Definition Evaluation := Var -> R.

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

(** * Markov Chains *)
(** ** DTMC *)

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

Definition is_stochastic_row (r: StateMaps.t R) : Prop :=
    (forall (s: State) (v: R), StateMaps.MapsTo s v r -> is_valid_prob v)
    /\ sum_in_map r = 1.

Definition opt_is_stochastic_row (o: option (StateMaps.t R)) : Prop :=
match o with
    | Some r => is_stochastic_row r
    | None => False
end.

Definition is_stochastic_matrix (m: TransitionMatrix R) : Prop :=
    forall s: State, forall r: StateMaps.t R,
        StateMaps.MapsTo s r m -> is_stochastic_row r.

(** Well-formed DTMC *)

Definition wf_DTMC (d: DTMC) : Prop :=
  (In d.(s0) d.(S))
  /\ (incl d.(T) d.(S))
  /\ (forall s: State, In s d.(S) <-> StateMaps.In s d.(P))
  /\ (is_stochastic_matrix d.(P)).

End NonParametric.


(** Probability of going from a given state to any other within a set of target states. *)

Variable pr_set: DTMC -> State -> set State -> R.

Hypothesis wf_dtmc_yields_valid_probability:
  forall (d: DTMC) (s: State) (Tgt: set State),
    (wf_DTMC d /\ In s d.(S) /\ incl Tgt d.(T)) -> is_valid_prob (pr_set d s Tgt).


(** Probability of going from a given state to another within a DTMC. *)

Definition pr (d: DTMC) (s t: State): R := pr_set d s (set_add State_eq_dec t (empty_set State)).

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

(** ** PMC *)

Module Parametric.

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


Definition eval_row (r: StateMaps.t RatExpr) (u: Evaluation) : StateMaps.t R :=
    StateMaps.map (fun val => eval_expr val u) r.

Definition eval_matrix (m: TransitionMatrix RatExpr) (u: Evaluation): TransitionMatrix R :=
    StateMaps.map (fun r => eval_row r u) m.

(** Definition 1.5 (PMC Evaluation) *)
Definition eval_pmc (p: PMC) (e: Evaluation) : DTMC :=
    Build_DTMC p.(S) p.(s0) (eval_matrix p.(P) e) p.(T).

(** Hahn's algorithm. *)

Variable alpha_v : PMC -> RatExpr.


(** Definition 2 (Well-defined evaluation) *)
(** Definition: an evaluation is well-defined iff the evaluated PMC is a well-formed DTMC. *)
Definition well_defined_evaluation (p: PMC) (u: Evaluation) : Prop := wf_DTMC (eval_pmc p u).


(** Lemma 1 (Hahn's lemma) *)
Hypothesis parametric_reachability_soundness:
 forall (p: PMC) (u: Evaluation),
    (well_defined_evaluation p u /\ wf_PMC p)
    -> (pr_set (eval_pmc p u) p.(s0) p.(T)) = eval_expr (alpha_v p) u.


Definition expr_is_valid_prob (r: RatExpr): Prop :=
match r with
  | Const p => is_valid_prob p
  | _ => False
end.

Definition opt_expr_is_valid_prob (o: option RatExpr): Prop :=
match o with
  | Some r => expr_is_valid_prob r
  | None   => False
end.

Lemma valid_prob_preservation: forall (e: RatExpr) (u: Evaluation), expr_is_valid_prob e -> is_valid_prob (eval_expr e u).
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

Lemma valid_prob_1_minus_p: forall p: R, is_valid_prob p -> is_valid_prob (1 - p).
Proof.
    intros p H.
    unfold is_valid_prob in H. elim H.
    intros H_ux_gte0 H_ux_lte1.
    unfold is_valid_prob. split.
    - apply Rge_le. apply Rle_minus in H_ux_lte1.
      apply Ropp_le_ge_contravar in H_ux_lte1.
      rewrite Ropp_0 in H_ux_lte1.
      rewrite <- Ropp_minus_distr in H_ux_lte1.
      rewrite Ropp_involutive in H_ux_lte1.
      assumption.
    - apply Ropp_le_contravar in H_ux_gte0.
      apply Rplus_le_compat_l with (r:=1) in H_ux_gte0.
      rewrite Ropp_0 in H_ux_gte0. rewrite Rplus_0_r in H_ux_gte0.
      apply H_ux_gte0.
Qed.

Definition expr_sum_in_map (m: StateMaps.t RatExpr) : RatExpr := sum_f_in_map m expr_sum (Const 0).

Lemma eval_sum_in_map:
    forall (m: StateMaps.t RatExpr) (u: Evaluation),
        eval_expr (expr_sum_in_map m) u = sum_in_map (eval_row m u).
Admitted.


Definition expr_is_stochastic_row (r: StateMaps.t RatExpr) : Prop :=
    (forall (s: State) (e: RatExpr), StateMaps.MapsTo s e r -> const e)
    /\ expr_sum_in_map r = Const 1.

Lemma eval_stochastic_row: forall (r: StateMaps.t RatExpr) (u: Evaluation),
    expr_is_stochastic_row r -> is_stochastic_row (eval_row r u).
Admitted.


Definition opt_In {T: Type} (s: State) (m: option (StateMaps.t T)): Prop :=
match m with
    | Some row => StateMaps.In s row
    | None     => False
end.


Lemma in_mapsto {T: Type} : forall (r: StateMaps.t T) (s: State),
    StateMaps.In s r <-> exists v: T, StateMaps.MapsTo s v r.
Proof.
    intros. split.
    - auto.
    - auto.
Qed.

Lemma mapsto_in {T: Type} : forall (r: StateMaps.t T) (s: State),
    forall v: T, StateMaps.MapsTo s v r -> StateMaps.In s r.
Proof.
    intros. rewrite in_mapsto. exists v. apply H.
Qed.


Definition annotative_state (m: TransitionMatrix RatExpr) (s: State): Prop :=
    forall r: StateMaps.t RatExpr, StateMaps.MapsTo s r m ->
        (expr_is_stochastic_row r
        \/
        (exists s1 s2: State, exists x: Var,
            s1 <> s2
            /\ StateMaps.MapsTo s1 (OneVar x) r
            /\ StateMaps.MapsTo s2 (Sub (Const 1) (OneVar x)) r
            /\ forall s': State,
                StateMaps.MapsTo s' (Const 0) (StateMaps.remove s2 (StateMaps.remove s1 r)) )).


Definition annotative_pmc (p: PMC) : Prop :=
    forall s: State, In s p.(S) -> annotative_state p.(P) s.

Lemma commutative_eval_find: forall (m: TransitionMatrix RatExpr) (s: State) (u: Evaluation),
    StateMaps.In s m -> StateMaps.find s (eval_matrix m u) = option_map (fun row => eval_row row u) (StateMaps.find s m).
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

Lemma commutative_eval_mapsto: forall (r: StateMaps.t RatExpr) (s: State) (u: Evaluation) (v: R),
    StateMaps.MapsTo s v (eval_row r u) ->
        exists e: RatExpr, StateMaps.MapsTo s e r /\ v = eval_expr e u.
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
        StateMaps.MapsTo s r (eval_matrix m u)
        -> (exists e: StateMaps.t RatExpr, StateMaps.MapsTo s e m /\ r = eval_row e u).
Proof.
Admitted.

Lemma sum_in_list: forall (l: list RatExpr) (e: RatExpr) (a0: RatExpr),
    In e l -> fold_left expr_sum l a0 = expr_sum e (fold_left expr_sum (remove Expr_eq_dec e l) a0).
Admitted.

Lemma sum_in_map: forall (r: StateMaps.t RatExpr) (s: State) (e: RatExpr),
    StateMaps.MapsTo s e r ->
    expr_sum_in_map r = expr_sum e (expr_sum_in_map (StateMaps.remove s r)).
Admitted.

Lemma sum_zero_in_map: forall (r: StateMaps.t RatExpr),
    (forall s: State, StateMaps.MapsTo s (Const 0) r) -> expr_sum_in_map r = Const 0.
Admitted.


Definition stochastic_evaluation (u: Evaluation) (X: set Var): Prop :=
    forall x: Var, In x X -> is_valid_prob (u x).

Lemma eval_annotative_state_is_stochastic:
    forall (m: TransitionMatrix RatExpr) (s: State) (r: StateMaps.t RatExpr) (u: Evaluation),
        StateMaps.MapsTo s r m ->
        annotative_state m s ->
        stochastic_evaluation u (var_set m)
        -> is_stochastic_row (eval_row r u).
Proof.
    intros m s r u H_s_mapsto_m H_s_annot H_u_stochastic.
    unfold annotative_state in H_s_annot.
    assert (H_s_mapsto_m':= H_s_mapsto_m).
    apply H_s_annot in H_s_mapsto_m.
    destruct H_s_mapsto_m.
    - (* all transitions are constant values *)
      apply eval_stochastic_row. apply H.
    - (* transitions are x and 1-x *)
      destruct H as [s1 [s2 [x [Hs1_s2 [Hx [Hx_compl H]]]]]].
      clear H_s_annot.
      unfold is_stochastic_row. split.
      + (* expressions evaluate to valid probabilities *)
        intros s' v H_s'_value.
        unfold stochastic_evaluation in H_u_stochastic.
        assert (H_x_in_r: In x (var_set' r)).
        { unfold var_set'.
          apply StateMaps.elements_1 in Hx. elim Hx.
          - (* x is in the first element. *)
            intros.
            unfold var_set_list'.
            repeat red in H0. destruct H0 as [H_fst H_snd].
            rewrite <- H_snd. simpl.
            apply set_union_intro1. simpl. left. reflexivity.
          - (* x is somewhere in the remaining elements. *)
            intros.
            unfold var_set_list'.
            apply set_union_intro2. assumption.
        }
        apply vars_injection with (m:=m) (s:=s) in H_x_in_r.
          Focus 2. assumption.
        apply H_u_stochastic in H_x_in_r.
        apply commutative_eval_mapsto in H_s'_value.
        elim H_s'_value. intros e [H_s'_mapsto_e H_v_eval_e].
        { (* Let us perform case analysis of s': *)
          destruct (State_eq_dec s1 s').
          - (* s' == s1 *)
            apply StateMaps.MapsTo_1 with (x:=s1) (y:=s') in Hx.
              Focus 2. auto.
            apply StateMapsFacts.MapsTo_fun with (e:=OneVar x) in H_s'_mapsto_e.
              Focus 2. assumption.
            rewrite H_v_eval_e.
            rewrite <- H_s'_mapsto_e.
            simpl. assumption.
          - (* s' <> s1 *)
            destruct (State_eq_dec s2 s').
            + (* s' == s2 *)
              apply StateMaps.MapsTo_1 with (x:=s2) (y:=s') in Hx_compl.
                Focus 2. auto.
              apply StateMapsFacts.MapsTo_fun with (e:=(Sub (Const 1) (OneVar x))) in H_s'_mapsto_e.
                Focus 2. assumption.
              rewrite H_v_eval_e.
              rewrite <- H_s'_mapsto_e.
              simpl.
              apply valid_prob_1_minus_p. assumption.
            + (* s' <> s2 *)
              apply StateMaps.remove_2 with (x:=s1) in H_s'_mapsto_e.
                Focus 2. assumption.
              apply StateMaps.remove_2 with (x:=s2) in H_s'_mapsto_e.
                Focus 2. assumption.
              apply StateMapsFacts.MapsTo_fun with (e:=Const 0) in H_s'_mapsto_e.
                Focus 2. apply H.
              rewrite H_v_eval_e.
              rewrite <- H_s'_mapsto_e. simpl.
              unfold is_valid_prob. split.
              * apply Rle_refl.
              * apply Rle_0_1.
        }
      + (* sum of row is 1 *)
        rewrite <- eval_sum_in_map.
        rewrite sum_in_map with (s:=s1) (e:=OneVar x).
        Focus 2. apply Hx.
        rewrite sum_in_map with (s:=s2) (e:=Sub (Const 1) (OneVar x)).
        Focus 2. apply StateMaps.remove_2 with (x:=s1) in Hx_compl.
        Focus 2. apply Hs1_s2.
        apply Hx_compl.
        remember (StateMaps.remove s2 (StateMaps.remove s1 r)) as rest.
        apply sum_zero_in_map in H. rewrite H. simpl. remember (u x) as a.
        rewrite Rplus_0_r. rewrite Rplus_minus. reflexivity.
Qed.

End Parametric.


Definition PresenceFunction : Type := Var -> SPL.Configuration -> bool.

Definition EvaluationFactory : Type := SPL.Configuration -> Evaluation.

Definition AnnotativeEvaluationFactory (pf: PresenceFunction): EvaluationFactory :=
    fun (c: SPL.Configuration) (x: Var) => if pf x c then 1 else 0.

(** Definition 6 (Annotative probabilistic model) *)
Record AnnotativeProbModel : Type := { pmc: Parametric.PMC;
                                       pf: PresenceFunction;
                                       w: EvaluationFactory;
                                       FM: SPL.FM }.

Notation "[| fm |]" := (SPL.fm_semantics fm).
Definition wf_annot_prob_model (apm: AnnotativeProbModel) : Prop :=
    Parametric.wf_PMC apm.(pmc)
    /\ Parametric.annotative_pmc apm.(pmc)
    /\ ( forall (c: SPL.Configuration) (x: Var),
           (In c [| apm.(FM) |]) -> (In x apm.(pmc).(Parametric.X))
           ->  apm.(w) = AnnotativeEvaluationFactory apm.(pf) ).

(** Definition 7 (DTMC derivation) *)
Definition lambda (p: Parametric.PMC) (w: EvaluationFactory) (c: SPL.Configuration) : DTMC :=
    Parametric.eval_pmc p (w c).


(** Lemma 2 (Evaluation well-definedness for annotative models) *)
Lemma lemma_2:
    forall apm: AnnotativeProbModel, wf_annot_prob_model apm ->
        forall c: SPL.Configuration,
            In c [|apm.(FM)|] -> Parametric.well_defined_evaluation apm.(pmc) (apm.(w) c).
Proof.
    intros.
    destruct H as [[Hs0 [HTinS [HSinP HXinP]]] [HannotPMC HannotEvalFactory]].
    unfold Parametric.well_defined_evaluation.
    remember (Parametric.eval_pmc (pmc apm) (w apm c)) as d.
    unfold wf_DTMC.
    intuition. (* Break each proposition in the conjunction into a separate goal. *)
    - (* s0 in S *)
      rewrite -> Heqd. simpl. apply Hs0.
    - (* T in S *)
      rewrite -> Heqd. simpl. apply HTinS.
    - (* StateMaps.In s (P d) *)
      rewrite Heqd in H. unfold Parametric.eval_pmc in H. unfold S in H.
      rewrite Heqd. unfold Parametric.eval_pmc. unfold P.
      apply HSinP in H. apply Parametric.eval_matrix_in. apply H.
    - (* In s (S d) *)
      rewrite Heqd in H. unfold Parametric.eval_pmc in H. unfold P in H.
      rewrite Heqd. unfold Parametric.eval_pmc. unfold S.
      apply HSinP. apply Parametric.eval_matrix_in in H. apply H.
    - (* all transitions are valid probabilities *)
      unfold is_stochastic_matrix. intros s r H_mapsto.
      rewrite Heqd in H_mapsto. unfold Parametric.eval_pmc in H_mapsto. unfold P in H_mapsto.
      apply Parametric.eval_matrix_evaluated_expr in H_mapsto. elim H_mapsto.
      intros e [H_mapsto_e H_r]. rewrite H_r.
      apply Parametric.eval_annotative_state_is_stochastic with (m:=Parametric.P (pmc apm)) (s:=s).
      + (* MapsTo s e (P apm) ? *)
        assumption.
      + (* annotative_state ? *)
        unfold Parametric.annotative_pmc in HannotPMC.
        apply Parametric.mapsto_in in H_mapsto_e.
        rewrite <- HSinP in H_mapsto_e. apply HannotPMC in H_mapsto_e.
        assumption.
      + (* w is a stochastic evaluation? *)
        unfold Parametric.stochastic_evaluation. intros.
        apply HannotEvalFactory with (x:=x) in H0.
        { (* is valid probability? *)
          rewrite H0.
          unfold AnnotativeEvaluationFactory.
          induction (pf apm x c).
          - unfold is_valid_prob. split.
              + apply Rle_0_1.
              + apply Rle_refl.
          - unfold is_valid_prob. split.
              + apply Rle_refl.
              + apply Rle_0_1.
        }
        { (* is x in X? *)
          rewrite HXinP. assumption.
        }
Qed.

End Rome.
