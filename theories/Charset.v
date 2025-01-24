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

Inductive in_charset : ascii -> charset -> bool -> Prop :=
  | ICSFull :
      forall a,
      in_charset a fullcharset true
  | ICSBase :
      forall a f,
      in_charset a (basecharset f) (f a)
  | ICSComplementTrue :
      forall a cs,
      in_charset a cs false ->
      in_charset a (complementcharset cs) true
  | ICSComplementFalse :
      forall a cs,
      in_charset a cs true ->
      in_charset a (complementcharset cs) false
  | ICSUnion1True :
      forall a cs1 cs2,
      in_charset a cs1 true ->
      in_charset a (unioncharset cs1 cs2) true
  | ICSUnion2True :
      forall a cs1 cs2,
      in_charset a cs2 true ->
      in_charset a (unioncharset cs1 cs2) true
  | ICSUnionFalse :
      forall a cs1 cs2,
      in_charset a cs1 false ->
      in_charset a cs2 false ->
      in_charset a (unioncharset cs1 cs2) false
  .

Lemma in_charset_determinism :
  forall a cs b1 b2,
  in_charset a cs b1 ->
  in_charset a cs b2 ->
  b1 = b2.
Proof.
  intros * H1 H2.
  generalize dependent b2.
  induction H1; intros;
  inversion H2; subst;
  try assert (true = false) by auto;
  try assert (false = true) by auto;
  try discriminate;
  eauto.
Qed.

Ltac pose_in_charset_determinism :=
  match goal with
    [ Hx: in_charset ?a ?cs ?b1,
      Hy: in_charset ?a ?cs ?b2 |- _ ] =>
          assert (b1 = b2)
          by eauto using in_charset_determinism;
          clear Hx
  end.

Lemma in_charset_dec :
  forall a cs, {in_charset a cs true} + {in_charset a cs false}.
Proof.
  intros.
  induction cs; intros.
  - (* fullcharset *)
    eauto using in_charset.
  - (* basecharset f *)
    destruct (f a) eqn:Heqfa;
    rewrite <- Heqfa;
    eauto using in_charset.
  - (* complementcharset cs *)
    destruct IHcs;
    eauto using in_charset.
  - (* unioncharset cs1 cs2 *)
    destruct IHcs1;
    destruct IHcs2;
    eauto using in_charset.
Qed.

Lemma in_charset_complete :
  forall a cs, exists b, in_charset a cs b.
Proof.
  intros.
  destruct (in_charset_dec a cs);
  eauto.
Qed.

Definition charseteq (cs1 cs2 : charset) : Prop :=
  forall a, exists b,
  in_charset a cs1 b /\ in_charset a cs2 b.

Lemma charseteq_refl :
  forall cs,
  charseteq cs cs.
Proof.
  unfold charseteq.
  intros.
  destruct (in_charset_complete a cs).
  eauto.
Qed.

Lemma charseteq_comm :
  forall cs1 cs2,
  charseteq cs1 cs2 ->
  charseteq cs2 cs1.
Proof.
  unfold charseteq.
  intros * H a.
  destruct (H a) as [b [? ?]].
  eauto.
Qed.

Lemma charseteq_trans :
  forall cs1 cs2 cs3,
  charseteq cs1 cs2 ->
  charseteq cs2 cs3 ->
  charseteq cs1 cs3.
Proof.
  unfold charseteq.
  intros * H12 H23 a.
  destruct (H12 a) as [? [? ?]];
  destruct (H23 a) as [? [? ?]];
  pose_in_charset_determinism;
  subst.
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
  intros.
  destruct (in_charset_complete a cs) as [[|] ?];
  eauto using in_charset.
Qed.

Lemma unioncharset_assoc :
  forall cs1 cs2 cs3,
  charseteq (cs1 U (cs2 U cs3))
            ((cs1 U cs2) U cs3).
Proof.
  unfold charseteq.
  intros.
  destruct (in_charset_complete a cs1) as [[|] ?];
  destruct (in_charset_complete a cs2) as [[|] ?];
  destruct (in_charset_complete a cs3) as [[|] ?];
  eauto 7 using in_charset.
Qed.

Lemma unioncharset_comm :
  forall cs1 cs2,
  charseteq (cs1 U cs2)
            (cs2 U cs1).
Proof.
  unfold charseteq.
  intros.
  destruct (in_charset_complete a cs1) as [[|] ?];
  destruct (in_charset_complete a cs2) as [[|] ?];
  eauto using in_charset.
Qed.

Lemma unioncharset_distrib :
  forall cs1 cs1' cs2 cs2',
  charseteq cs1 cs1' ->
  charseteq cs2 cs2' ->
  charseteq (cs1 U cs2) (cs1' U cs2').
Proof.
  unfold charseteq.
  intros * H1 H2 a.
  specialize (H1 a) as [[|] [? ?]];
  specialize (H2 a) as [[|] [? ?]];
  eauto using in_charset.
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
  destruct (in_charset_complete a cs1) as [[|] ?];
  destruct (in_charset_complete a cs2) as [[|] ?];
  destruct (in_charset_complete a cs3) as [[|] ?];
  eauto 8 using in_charset.
Qed.
