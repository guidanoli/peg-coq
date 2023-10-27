From Coq Require Import Arith.PeanoNat.

Definition pre (P : nat -> Prop) n := forall m, m < n -> P m.

Lemma P_n_iff_pre_P_n :
  forall (P : nat -> Prop),
  (forall n, P n) <-> (forall n, pre P n).
Proof.
  intro.
  unfold pre.
  split; intro; eauto.
Qed.

Lemma pre_0 :
  forall P,
  pre P 0.
Proof.
  unfold pre.
  intros P n contra.
  exfalso.
  eapply Nat.nlt_0_r.
  eauto.
Qed.

Lemma pre_S :
  forall P n,
  pre P n /\ P n ->
  pre P (S n).
Proof.
  unfold pre.
  intros P n Hand m Hlt.
  remember (S n) as Sn eqn:HeqSn.
  destruct Hlt;
  injection HeqSn as Heqn;
  subst;
  apply Hand;
  auto.
Qed.

Theorem strong_ind_nat :
  forall (P : nat -> Prop),
  (forall n, (forall m, m < n -> P m) -> P n) ->
  (forall n, P n).
Proof.
  intros P H n.
  apply P_n_iff_pre_P_n.
  clear n.
  intros n.
  induction n.
  - apply pre_0.
  - apply pre_S.
    split.
    + auto.
    + apply H.
      auto.
Qed.
