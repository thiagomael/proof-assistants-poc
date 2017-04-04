(** * Annotative Probabilistic Models *)
Require Import Reals.
Require Import List.
Require Import ListSet.

Open Scope R_scope.

Require Import Probabilities.
Require Import State.
Require Import RatExpr.
Require Import TransitionMatrix.Definitions.
Require Import TransitionMatrix.Real.
Require Import TransitionMatrix.Parametric.
Require Import Markov.DTMC.
Require Import Markov.PMC.
Require Import ReliabilityModels.Definitions.

(** ** Annotative PMC **)

Definition annotative_state (m: TransitionMatrix RatExpr) (s: State): Prop :=
    forall r: StateMaps.t RatExpr, StateMaps.MapsTo s r m ->
        (expr_is_stochastic_row r
        \/
        (exists s1 s2: State, exists x: Var,
            s1 <> s2
            /\ StateMaps.MapsTo s1 (OneVar x) r
            /\ StateMaps.MapsTo s2 (Sub (Const 1) (OneVar x)) r
            /\ forall s': State,
                StateMaps.In s' (StateMaps.remove s2 (StateMaps.remove s1 r)) ->
                  StateMaps.MapsTo s' (Const 0) (StateMaps.remove s2 (StateMaps.remove s1 r)) )).

Definition annotative_pmc (p: PMC) : Prop :=
    forall s: State, In s p.(S) -> annotative_state p.(P) s.


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
          destruct (State.eq_dec s1 s').
          - (* s' == s1 *)
            apply StateMaps.MapsTo_1 with (x:=s1) (y:=s') in Hx.
              Focus 2. auto.
            apply StateMapsFacts.MapsTo_fun with (e:=OneVar x) in H_s'_mapsto_e.
              Focus 2. assumption.
            rewrite H_v_eval_e.
            rewrite <- H_s'_mapsto_e.
            simpl. assumption.
          - (* s' <> s1 *)
            destruct (State.eq_dec s2 s').
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
                Focus 2. apply H. apply mapsto_in in H_s'_mapsto_e. assumption.
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
        apply sum_zero_in_map in H.
        rewrite H. simpl. remember (u x) as a.
        rewrite Rplus_0_r. rewrite Rplus_minus. reflexivity.
Qed.


Definition AnnotativeEvaluationFactory (pf: PresenceFunction): EvaluationFactory :=
    fun (c: SPL.Configuration) (x: Var) => if pf x c then 1 else 0.

(** Definition 6 (Annotative probabilistic model) *)
Record AnnotativeProbModel : Type := { pmc: PMC;
                                       pf: PresenceFunction;
                                       w: EvaluationFactory;
                                       FM: SPL.FM }.

Notation "[| fm |]" := (SPL.fm_semantics fm).
Definition wf_annot_prob_model (apm: AnnotativeProbModel) : Prop :=
    wf_PMC apm.(pmc)
    /\ annotative_pmc apm.(pmc)
    /\ ( forall (c: SPL.Configuration) (x: Var),
           (In c [| apm.(FM) |]) -> (In x apm.(pmc).(X))
           ->  apm.(w) = AnnotativeEvaluationFactory apm.(pf) ).


(** Lemma 2 (Evaluation well-definedness for annotative models) *)
Lemma evaluation_well_definedness:
    forall apm: AnnotativeProbModel, wf_annot_prob_model apm ->
        forall c: SPL.Configuration,
            In c [|apm.(FM)|] -> well_defined_evaluation apm.(pmc) (apm.(w) c).
Proof.
    intros.
    destruct H as [[Hs0 [HTinS [HSinP HXinP]]] [HannotPMC HannotEvalFactory]].
    unfold well_defined_evaluation.
    remember (eval_pmc (pmc apm) (w apm c)) as d.
    unfold wf_DTMC.
    intuition. (* Break each proposition in the conjunction into a separate goal. *)
    - (* s0 in S *)
      rewrite -> Heqd. simpl. apply Hs0.
    - (* T in S *)
      rewrite -> Heqd. simpl. apply HTinS.
    - (* StateMaps.In s (P d) *)
      rewrite Heqd in H. unfold eval_pmc in H. unfold S in H.
      rewrite Heqd. unfold eval_pmc. unfold P.
      apply HSinP in H. apply eval_matrix_in. apply H.
    - (* In s (S d) *)
      rewrite Heqd in H. unfold eval_pmc in H. unfold P in H.
      rewrite Heqd. unfold eval_pmc. unfold S.
      apply HSinP. apply eval_matrix_in in H. apply H.
    - (* all transitions are valid probabilities *)
      unfold is_stochastic_matrix. intros s r H_mapsto.
      rewrite Heqd in H_mapsto. unfold eval_pmc in H_mapsto. unfold P in H_mapsto.
      apply eval_matrix_evaluated_expr in H_mapsto. elim H_mapsto.
      intros e [H_mapsto_e H_r]. rewrite H_r.
      apply eval_annotative_state_is_stochastic with (m:=P (pmc apm)) (s:=s).
      + (* MapsTo s e (P apm) ? *)
        assumption.
      + (* annotative_state ? *)
        unfold annotative_pmc in HannotPMC.
        apply mapsto_in in H_mapsto_e.
        rewrite <- HSinP in H_mapsto_e. apply HannotPMC in H_mapsto_e.
        assumption.
      + (* w is a stochastic evaluation? *)
        unfold stochastic_evaluation. intros.
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