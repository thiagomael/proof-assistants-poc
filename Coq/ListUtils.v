(** Useful lemmas about lists **)
Require Import Coq.Lists.SetoidList.
Require Import Coq.Logic.Classical_Prop.

Lemma not_InA (T: Type) (eqT: T -> T -> Prop):
    forall (l1 l2: list T)
           (x: T),
         ~InA eqT x (l1 ++ l2) -> (~InA eqT x l1 /\ ~InA eqT x l2).
Proof.
    intros.
    rewrite InA_app_iff in H.
    tauto.
Qed.

Lemma NoDupA_swap' (A : Type) (eqA : A -> A -> Prop):
    Equivalence eqA ->
      forall (l l' : list A) (x : A),
      NoDupA eqA (x :: l ++ l') -> NoDupA eqA (l ++ x :: l').
Proof.
    intros.
    induction l.
    - simpl in *. assumption.
    - simpl in *.
      inversion H0 as [ | x' l'' H_not_in H_nodup].
      inversion H_nodup as [ | x'' l''' H_not_in_a H_nodup_ll].
      rewrite InA_cons in H_not_in.
      apply Classical_Prop.not_or_and in H_not_in.
      destruct H_not_in as [H_x_neq_a H_x_not_in_ll].
      assert (H_nodup_xll := NoDupA_cons H_x_not_in_ll H_nodup_ll).
      apply IHl in H_nodup_xll.
      apply NoDupA_cons.
      + rewrite InA_app_iff.
        apply Classical_Prop.and_not_or.
        apply not_InA in H_not_in_a.
        destruct H_not_in_a as [H_a_not_in_l H_a_not_in_l'].
        split; auto.
        rewrite InA_cons. intuition.
      + assumption.
Qed.