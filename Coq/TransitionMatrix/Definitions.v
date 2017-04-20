(** Transition Matrices with arbitrary values **)
Require Import Reals.
Require Import Coq.FSets.FMapWeakList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Lists.SetoidList.

Open Scope R_scope.

Require Import ListUtils.
Require Import State.

Module StateMaps := FMapWeakList.Make DecidableState.
Module StateMapsFacts := WFacts_fun DecidableState StateMaps.
Module StateMapsProperties := WProperties_fun DecidableState StateMaps.

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


(** Useful lemmas about lists of elements **)

Lemma remove_nodup (T: Type):
    forall (l: list (State * T))
           (s: State)
           (t: T),
         ~InA (StateMaps.Raw.PX.eqk (elt:=T)) (s, t) l ->
         StateMaps.Raw.remove s l = l.
Proof.
    intros.
    induction l.
    - auto.
    - (* make IH applicable *)
      intuition.
      destruct a as [s' t'].
      unfold StateMaps.Raw.remove.
      destruct (StateMapsProperties.F.eq_dec s s') as [H' | H'].
      + (* s = s' *)
        rewrite <- H' in H.
        assert (H_eq: (StateMaps.Raw.PX.eqk (elt:=T)) (s, t) (s, t')).
        {
          - auto.
        }
        apply InA_cons_hd with (l:=l) in H_eq.
        apply H in H_eq. contradiction.
      + (* s <> s' *)
        unfold StateMaps.Raw.remove in H0.
        rewrite H0. trivial.
Qed.

Lemma remove_distributive (T: Type):
    forall (l1 l2: list (State * T))
           (s: State),
         SetoidList.NoDupA (StateMaps.Raw.PX.eqk (elt:=T)) (l1 ++ l2) ->
         StateMaps.Raw.remove s (l1 ++ l2) = (StateMaps.Raw.remove s l1) ++ (StateMaps.Raw.remove s l2).
Proof.
    intros.
    induction l1.
    - rewrite ?app_nil_l. trivial.
    - rewrite <- app_comm_cons.
      destruct a as [s' t].
      destruct (StateMapsProperties.F.eq_dec s s') as [H' | H'].
      + rewrite <- H'.
        rewrite <- H' in H.
        rewrite <- app_comm_cons in H.
        inversion H as [H_nil | x l H_x_not_in_l H_nodup_l].
        apply IHl1 in H_nodup_l.
        simpl.
        destruct (StateMapsProperties.F.eq_dec s s) as [H'' | H''].
        * apply not_InA in H_x_not_in_l.
          destruct H_x_not_in_l as [H_x_not_in_l1 H_x_not_in_l2].
          rewrite remove_nodup with (t:=t).
          trivial. assumption.
        * contradiction.
      + unfold StateMaps.Raw.remove at 1.
        destruct (StateMapsProperties.F.eq_dec s s') as [H'' | _].
        * rewrite H'' in H'. contradiction.
        * inversion H as [H_nil | x l H_x_not_in_l H_nodup_l].
          apply IHl1 in H_nodup_l.
          unfold StateMaps.Raw.remove at 1 in H_nodup_l.
          rewrite H_nodup_l.
          {
            unfold StateMaps.Raw.remove at 3.
            destruct (StateMapsProperties.F.eq_dec s s') as [H'' | _].
            - rewrite H'' in H'. contradiction.
            - replace
                ((fix
                 remove (k : StateMaps.Raw.key) (s0 : StateMaps.Raw.t T) {struct s0} :
                   StateMaps.Raw.t T :=
                   match s0 with
                   | Datatypes.nil => Datatypes.nil
                   | (k', x0) :: l0 =>
                       if StateMapsProperties.F.eq_dec k k'
                       then l0
                       else (k', x0) :: remove k l0
                   end) s l1)
              with (StateMaps.Raw.remove (elt:=T) s l1).
              trivial.
              unfold StateMaps.Raw.remove. trivial.
          }
Qed.


Lemma remove_middle (T: Type):
    forall (l1 l2: list (State * T))
           (s: State)
           (t: T),
        (~ SetoidList.InA (StateMaps.Raw.PX.eqk (elt:=T)) (s, t) (l1 ++ l2)) ->
        (NoDupA (StateMaps.Raw.PX.eqk (elt:=T)) (l1 ++ l2)) ->
            StateMaps.Raw.remove s (l1 ++ (s, t)::l2) = l1++l2.
Proof.
    intros l1 l2 s t H H_nodup.
    induction l1; induction l2; try rewrite ?app_nil_l.
    - (* l1 = nil /\ l2 = nil *)
      unfold StateMaps.Raw.remove.
      destruct (StateMapsProperties.F.eq_dec s s).
      trivial. contradiction.
    - (* l1 = nil /\ l2 = a :: l *)
      unfold StateMaps.Raw.remove.
      destruct (StateMapsProperties.F.eq_dec s s).
      trivial. contradiction.
    - (* l1 = a::l /\ l2 = nil *)
      rewrite ?app_nil_r in H. rewrite ?app_nil_r in IHl1.
      intuition.
      rewrite <- app_comm_cons.
      unfold StateMaps.Raw.remove.
      unfold StateMaps.Raw.remove in H0.
      rewrite H0.
        Focus 2.
          rewrite app_nil_r in H_nodup.
          inversion H_nodup. assumption.
      destruct a. simpl.
      destruct (StateMapsProperties.F.eq_dec s s0).
      + (* s = s0 *)
        contradict e.
        rewrite SetoidList.InA_cons in H.
        contradict H. rewrite H.
        left. auto.
      + (* s <> s0 *)
        symmetry. apply app_nil_r with (l:=(s0, t0)::l1).
    - (* l1 = a::l /\ l2 = a0::l' *)
      rewrite remove_distributive.
      + apply not_InA in H.
        destruct H as [H_s_not_in_al1 H_s_not_in_a0l2].
        apply remove_nodup in H_s_not_in_al1. rewrite H_s_not_in_al1.
        replace (StateMaps.Raw.remove (elt:=T) s ((s, t) :: a0 :: l2))
          with (a0 :: l2).
        trivial.
        symmetry. simpl.
        destruct (StateMapsProperties.F.eq_dec s s) as [H|H].
        * trivial.
        * contradiction.
      + specialize (NoDupA_cons H H_nodup). intros H_nodup_s.
        apply NoDupA_swap'.
        * exact (StateMapsProperties.eqk_equiv T).
        * assumption.
Qed.

Lemma remove_elements' (T: Type):
    forall (r: StateMaps.t T)
           (s: State)
           (e: T)
           (l1 l2: list (State * T))
           (a: State * T),
        StateMaps.eq_key_elt (s, e) a ->
        StateMaps.elements r = l1 ++ a::l2 ->
            StateMaps.elements (StateMaps.remove s r) = l1++l2.
Proof.
    intros r s e l1 l2 a H_eq_pair H_elem.
    unfold StateMaps.elements, StateMaps.Raw.elements in H_elem.
    simpl. rewrite H_elem.
  (* s, e = fst a, snd a *)
    destruct H_eq_pair as [H_s H_e].
    simpl in H_s. simpl in H_e.
  (* *)
    destruct l1(* ; destruct l2 *).
    - destruct a. rewrite H_s.
      rewrite app_nil_l. rewrite app_nil_l.
      simpl. compute.
      destruct (State.eq_dec s0 s0).
      + reflexivity.
      + contradiction.
    - destruct a. rewrite H_s.
    (* we need to generate a hypothesis stating that p <> a *)
      destruct r. simpl in H_elem.
      rewrite H_elem in NoDup.
      destruct p. simpl.
      destruct (StateMapsProperties.F.eq_dec s0 s1).
      + (* s0 = s1 *)
        contradict e0.
        inversion NoDup as [H | x l H_x_not_in_l H_nodup_l].
        contradict H_x_not_in_l.
        rewrite H_x_not_in_l.
        rewrite SetoidList.InA_app_iff.
        right. auto.
      + (* s0 <> s1 *)
        replace (StateMaps.Raw.remove (elt:=T) s0 (l1 ++ (s0, t) :: l2))
          with (l1 ++ l2).
        auto.
        symmetry. apply remove_middle.
        inversion NoDup as [H | x l H_x_not_in_l H_nodup_l].
        apply SetoidList.NoDupA_swap in H_nodup_l.
        inversion H_nodup_l.
        * assumption.
        * exact (StateMapsProperties.eqk_equiv T).
        * rewrite app_comm_cons in NoDup.
          apply NoDupA_swap' in NoDup.
          apply NoDupA_split in NoDup.
          apply NoDupA_split in NoDup.
          assumption.
          exact (StateMapsProperties.eqk_equiv T).
Qed.
