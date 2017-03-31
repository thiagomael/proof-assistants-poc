Require Import Reals.
Open Scope R_scope.

Definition is_valid_prob (p: R): Prop := 0 <= p <= 1.


Lemma valid_prob_1_minus_p:
    forall p: R,
        is_valid_prob p -> is_valid_prob (1 - p).
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