From Coq Require Import Bool.
From Coq Require Import Strings.Ascii.
From Peg Require Import Tactics.

Definition charset : Type := (ascii -> bool).

(* Full charset *)
Definition fullcharset : charset :=
  (fun _ => true).

(* Union of charsets *)
Definition unioncharset cs1 cs2 : charset :=
  (fun a => orb (cs1 a) (cs2 a)).

Notation "cs1 'U' cs2" := (unioncharset cs1 cs2) (at level 120, right associativity).

(* Set complement of a charset *)
Definition complementcharset cs : charset :=
  (fun a => negb (cs a)).

Inductive in_charset : ascii -> charset -> Prop :=
  | ICSIntro :
      forall a cs,
      cs a = true ->
      in_charset a cs.

Lemma in_charset_dec :
  forall a cs, {in_charset a cs} + {~in_charset a cs}.
Proof.
  intros.
  destruct (cs a) eqn:Heqcsa.
  - (* true *)
    auto using in_charset.
  - (* false *)
    right.
    intro Hcontra.
    inversion Hcontra; subst.
    destruct1sep.
Qed.

Inductive charseteq : charset -> charset -> Prop :=
  | CSEq :
      forall cs1 cs2,
      (forall a, cs1 a = cs2 a) ->
      charseteq cs1 cs2.

Lemma charseteq_refl :
  forall cs,
  charseteq cs cs.
Proof.
  eauto using charseteq.
Qed.

Lemma charseteq_comm :
  forall cs1 cs2,
  charseteq cs1 cs2 ->
  charseteq cs2 cs1.
Proof.
  intros * H.
  inversion H; subst.
  econstructor.
  auto.
Qed.

Lemma charseteq_trans :
  forall cs1 cs2 cs3,
  charseteq cs1 cs2 ->
  charseteq cs2 cs3 ->
  charseteq cs1 cs3.
Proof.
  intros * H12 H23.
  inversion H12; subst;
  inversion H23; subst;
  eauto using charseteq.
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
  eauto using orb_diag, charseteq.
Qed.

Lemma unioncharset_assoc :
  forall cs1 cs2 cs3,
  charseteq (cs1 U (cs2 U cs3))
            ((cs1 U cs2) U cs3).
Proof.
  eauto using orb_assoc, charseteq.
Qed.

Lemma unioncharset_comm :
  forall cs1 cs2,
  charseteq (cs1 U cs2)
            (cs2 U cs1).
Proof.
  eauto using orb_comm, charseteq.
Qed.

Lemma unioncharset_distrib :
  forall cs1 cs1' cs2 cs2',
  charseteq cs1 cs1' ->
  charseteq cs2 cs2' ->
  charseteq (cs1 U cs2) (cs1' U cs2').
Proof.
  intros * H1 H2.
  unfold unioncharset.
  inversion H1; subst.
  inversion H2; subst.
  econstructor.
  intros.
  repeat match goal with
    [ Hx: forall a, _ a = _ a |- _ ] =>
        rewrite Hx;
        clear Hx
  end.
  auto.
Qed.

Ltac pose_charseteq_union_distrib :=
  match goal with
    [ _: charseteq ?cs1 ?cs1',
      _: charseteq ?cs2 ?cs2' |- _ ] =>
          assert (charseteq (cs1 U cs2)
                            (cs1' U cs2'))
          by eauto using unioncharset_distrib
  end.

Lemma unioncharset_rep_l :
  forall cs1 cs2 cs3,
  charseteq ((cs1 U cs3) U (cs2 U cs3))
            ((cs1 U cs2) U cs3).
Proof with (eauto 3 using
  unioncharset_assoc,
  unioncharset_comm,
  unioncharset_distrib,
  unioncharset_diag,
  charseteq_comm,
  charseteq_refl,
  charseteq_trans
).
  intros.
  assert (charseteq ((cs1 U cs3) U (cs2 U cs3)) (cs1 U (cs3 U (cs2 U cs3))))...
  assert (charseteq (cs1 U (cs3 U (cs2 U cs3))) (cs1 U ((cs3 U cs2) U cs3)))...
  assert (charseteq (cs1 U ((cs3 U cs2) U cs3)) (cs1 U ((cs2 U cs3) U cs3)))...
  assert (charseteq (cs1 U ((cs2 U cs3) U cs3)) (cs1 U (cs2 U (cs3 U cs3))))...
  assert (charseteq (cs1 U (cs2 U (cs3 U cs3))) (cs1 U (cs2 U cs3)))...
  assert (charseteq (cs1 U (cs2 U cs3)) ((cs1 U cs2) U cs3))...
  eauto 6 using charseteq_trans, charseteq_comm.
Qed.
