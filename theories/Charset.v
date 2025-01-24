From Coq Require Import Bool.
From Coq Require Import Strings.Ascii.
From Peg Require Import Tactics.

Inductive charset : Type :=
  | fullcharset
  | basecharset (f : ascii -> bool)
  | complementcharset (cs : charset)
  | unioncharset (cs1 cs2 : charset)
  .

Notation "cs1 'U' cs2" := (unioncharset cs1 cs2) (at level 120, right associativity).

Fixpoint in_charset a cs :=
  match cs with
  | fullcharset => true
  | basecharset f => f a
  | complementcharset cs => negb (in_charset a cs)
  | unioncharset cs1 cs2 => orb (in_charset a cs1) (in_charset a cs2)
  end.

Definition charseteq cs1 cs2 :=
  forall a, in_charset a cs1 = in_charset a cs2.

Lemma charseteq_refl :
  forall cs,
  charseteq cs cs.
Proof.
  unfold charseteq.
  auto.
Qed.

Lemma charseteq_comm :
  forall cs1 cs2,
  charseteq cs1 cs2 ->
  charseteq cs2 cs1.
Proof.
  unfold charseteq.
  auto.
Qed.

Lemma charseteq_trans :
  forall cs1 cs2 cs3,
  charseteq cs1 cs2 ->
  charseteq cs2 cs3 ->
  charseteq cs1 cs3.
Proof.
  unfold charseteq.
  eauto.
Qed.

Ltac pose_charseteq_trans :=
  match goal with
    [ _: charseteq ?cs1 ?cs2,
      _: charseteq ?cs2 ?cs3 |- _ ] =>
          assert (charseteq cs1 cs3)
          by eauto using charseteq_trans
  end.

Lemma unioncharset_diag :
  forall cs,
  charseteq (cs U cs) cs.
Proof.
  unfold charseteq.
  simpl.
  auto using orb_diag.
Qed.

Lemma unioncharset_assoc :
  forall cs1 cs2 cs3,
  charseteq (cs1 U (cs2 U cs3))
            ((cs1 U cs2) U cs3).
Proof.
  unfold charseteq.
  simpl.
  auto using orb_assoc.
Qed.

Lemma unioncharset_comm :
  forall cs1 cs2,
  charseteq (cs1 U cs2)
            (cs2 U cs1).
Proof.
  unfold charseteq.
  simpl.
  auto using orb_comm.
Qed.

Lemma unioncharset_distrib :
  forall cs1 cs1' cs2 cs2',
  charseteq cs1 cs1' ->
  charseteq cs2 cs2' ->
  charseteq (cs1 U cs2) (cs1' U cs2').
Proof.
  unfold charseteq.
  intros * H1 H2 a.
  simpl.
  rewrite (H1 a).
  rewrite (H2 a).
  auto.
Qed.

Ltac pose_charseteq_union_distrib :=
  match goal with
    [ _: charseteq ?cs1 ?cs1',
      _: charseteq ?cs2 ?cs2' |- _ ] =>
          assert (charseteq (cs1 U cs2) (cs1' U cs2'))
          by eauto using unioncharset_distrib
  end.

Lemma unioncharset_rep_l :
  forall cs1 cs2 cs3,
  charseteq ((cs1 U cs3) U (cs2 U cs3))
            ((cs1 U cs2) U cs3).
Proof.
  unfold charseteq.
  intros.
  simpl.
  destruct (in_charset a cs1);
  destruct (in_charset a cs2);
  destruct (in_charset a cs3);
  auto.
Qed.
