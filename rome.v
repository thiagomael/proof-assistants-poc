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
  | Div:    RatExpr -> RatExpr -> RatExpr.

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




Definition Evaluation := Var -> R.

Fixpoint eval_expr (e: RatExpr) (u: Evaluation) : R :=
match e with
  | Const r  => r
  | OneVar v => u v
  | Sum a b  => (eval_expr a u) + (eval_expr b u)
  | Sub a b  => (eval_expr a u) - (eval_expr b u)
  | Mul a b  => (eval_expr a u) * (eval_expr b u)
  | Div a b  => (eval_expr a u) / (eval_expr b u)
end.

Fixpoint vars (e: RatExpr) : set Var :=
  match e with
  | Const _  => empty_set Var
  | OneVar v => set_add Var_eq_dec v (empty_set Var)
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
    (forall s: State, StateMaps.In s r -> opt_is_valid_prob (StateMaps.find s r) )
    /\ sum_in_map r = 1.

Definition opt_is_stochastic_row (o: option (StateMaps.t R)) : Prop :=
match o with
    | Some r => is_stochastic_row r
    | None => False
end.

Definition is_stochastic_matrix (m: TransitionMatrix R) : Prop :=
    forall s: State,
       StateMaps.In s m -> option_map is_stochastic_row (StateMaps.find s m) = Some True.

(** Well-formed DTMC *)

Definition wf_DTMC (d: DTMC) : Prop :=
  (In d.(s0) d.(S))
  /\ (incl d.(T) d.(S))
  /\ (is_stochastic_matrix d.(P)).

End NonParametric.


(** Probability of going from a given state to any other within a set of target states. *)

Variable pr_set: DTMC -> State -> set State -> R.

Lemma wf_dtmc_yields_valid_probability:
  forall (d: DTMC) (s: State) (Tgt: set State),
    (wf_DTMC d /\ In s d.(S) /\ incl Tgt d.(T)) -> is_valid_prob (pr_set d s Tgt).
Admitted.


(** Probability of going from a given state to another within a DTMC. *)

Definition pr (d: DTMC) (s t: State): R := pr_set d s (set_add State_eq_dec t (empty_set State)).


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
  /\ (forall s: State, In s p.(S) -> StateMaps.In s p.(P)).
  (*/\ forall e: RatExpr, In e P -> incl (vars e) X. *)


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

(** Hahn's lemma: *)

Lemma parametric_reachability_soundness:
 forall (p: PMC) (u: Evaluation),
    (well_defined_evaluation p u /\ wf_PMC p)
    -> (pr_set (eval_pmc p u) p.(s0) p.(T)) = eval_expr (alpha_v p) u.
Proof.
Admitted.

Definition expr_is_valid_prob (r: RatExpr): Prop :=
match r with
  | Const p => is_valid_prob p
  (*| Mul a b => expr_is_valid_prob a /\ expr_is_valid_prob b*)
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
Qed.

Definition expr_sum_in_map (m: StateMaps.t RatExpr) : RatExpr := sum_f_in_map m expr_sum (Const 0).


Definition expr_is_stochastic_row (r: StateMaps.t RatExpr) : Prop :=
    (forall s: State, StateMaps.In s r -> opt_expr_is_valid_prob (StateMaps.find s r) )
    /\ expr_sum_in_map r = Const 1.

Definition opt_expr_is_stochastic_row (o: option (StateMaps.t RatExpr)) : Prop :=
match o with
    | Some row => expr_is_stochastic_row row
    | None => False
end.

Definition expr_is_stochastic_matrix (m: TransitionMatrix RatExpr) : Prop :=
    forall s: State, StateMaps.In s m -> option_map expr_is_stochastic_row (StateMaps.find s m) = Some True.

Lemma eval_stochastic: forall (m: TransitionMatrix RatExpr) (u: Evaluation),
    expr_is_stochastic_matrix m -> is_stochastic_matrix (eval_matrix m u).
Admitted.

Lemma eval_stochastic_row: forall (r: StateMaps.t RatExpr) (u: Evaluation),
    expr_is_stochastic_row r -> is_stochastic_row (eval_row r u).
Admitted.


Inductive annotative_state (m: TransitionMatrix RatExpr) (s: State): Prop :=
  | stochastic_const: opt_expr_is_stochastic_row (StateMaps.find s m)(* = Some True*) -> annotative_state m s
  | var_complement: (exists s1 s2: State, exists x: Var,
                StateMaps.In s1 m
                /\ StateMaps.In s2 m
                /\ ( (bimap s s1 m) = Some (OneVar x) )
                /\ bimap s s2 m = Some (Sub (Const 1) (OneVar x))
                /\ forall s': State,
                    (StateMaps.In s' m /\ s' <> s1 /\ s' <> s2) -> bimap s s' m = Some (Const 0) )
                -> annotative_state m s.

(*Definition annotative_pmc (p: PMC) : Prop :=
    forall s: State,
        In s p.(S) ->
            (option_map expr_is_stochastic_row (StateMaps.find s p.(P)) = Some True)
            \/
            (exists s1 s2: State, exists x: Var,
                In s1 p.(S)
                /\ In s2 p.(S)
                /\ In x p.(X)
                /\ ( (bimap s s1 p.(P)) = Some (OneVar x) )
                /\ bimap s s2 p.(P) = Some (Sub (Const 1) (OneVar x))
                /\ forall s': State,
                    (In s' p.(S) /\ s' <> s1 /\ s' <> s2) -> bimap s s' p.(P) = Some (Const 0)).
*)
Definition annotative_pmc (p: PMC) : Prop :=
    forall s: State, In s p.(S) -> annotative_state p.(P) s.

Lemma eval_annotative_state_is_stochastic: forall (m: TransitionMatrix RatExpr) (s: State) (u: Evaluation),
    StateMaps.In s m -> annotative_state m s -> opt_is_stochastic_row (StateMaps.find s (eval_matrix m u)).
Proof.
    intros m s u H_s_in_m H_s_annot.
    assert (StateMaps.find s (eval_matrix m u) = option_map (fun row => eval_row row u) (StateMaps.find s m)) as eval_sbrubles.
      {
          unfold eval_matrix.
          (*inversion H_s_in_m.*)
          (*destruct (StateMaps.find s m) as [opt_value|].
          - simpl. inversion H_s_in_m as [e H_mapsto].
            apply StateMaps.map_1 with (elt':=StateMaps.t R) (f:=fun r : StateMaps.t RatExpr => eval_row r u) in H_mapsto.
            apply StateMaps.find_1. generalize dependent opt_value. exists e.*)
          inversion H_s_in_m as [e H_mapsto].
          apply StateMaps.find_1 in H_mapsto. rewrite -> H_mapsto.
          apply StateMaps.find_2 in H_mapsto.
          apply StateMaps.map_1 with (elt':=StateMaps.t R) (f:=fun r : StateMaps.t RatExpr => eval_row r u) in H_mapsto.
          apply StateMaps.find_1 in H_mapsto. rewrite -> H_mapsto.
          unfold option_map. reflexivity.
      }
      rewrite eval_sbrubles. inversion H_s_in_m as [e H_mapsto]. apply StateMaps.find_1 in H_mapsto. rewrite -> H_mapsto.
      unfold option_map. unfold opt_is_stochastic_row. apply eval_stochastic_row.
      destruct H_s_annot.
      - (*stochastic_const*) rewrite H_mapsto in H. unfold option_map in H. apply H.
      - (*var_complement*)
    - 
Qed.

End Parametric.

Load fm.

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
           (In c [| apm.(FM) |]) /\ (In x apm.(pmc).(Parametric.X))
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
    destruct H as [[Hs0 [HTinS HSinP]] [HannotPMC HannotEvalFactory]].
    unfold Parametric.well_defined_evaluation.
    remember (Parametric.eval_pmc (pmc apm) (w apm c)) as d.
    unfold wf_DTMC.
    intuition. (* Break each proposition in the conjunction into a separate goal. *)
    - (*s0 in S*)
      rewrite -> Heqd. simpl. apply Hs0.
    - (*T in S*)
      rewrite -> Heqd. simpl. apply HTinS.
    - (*all transitions are valid probabilities*)
      unfold Parametric.annotative_pmc in HannotPMC.
      assert (forall s : State,
                 In s (Parametric.S (pmc apm))
                 <-> In s (S d)) as S_unchanged.
      { rewrite -> Heqd. simpl. tauto.}
      unfold is_stochastic_matrix.
        intros. apply Parametric.eval_stochastic_row.
        unfold opt_is_valid_prob. destruct (bimap s s' (P d)).

      apply H1 in HannotPMC.
      destruct HannotPMC with (s:=s).
      induction (bimap s s' (P d)). unfold opt_is_valid_prob.
Qed.

End Rome.
