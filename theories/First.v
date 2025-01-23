From Coq Require Import Bool.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Peg Require Import Checkloops.
From Peg Require Import Coherent.
From Peg Require Import Match.
From Peg Require Import Nullable.
From Peg Require Import Suffix.
From Peg Require Import Syntax.
From Peg Require Import Tactics.
From Peg Require Import Verifygrammar.
From Peg Require Import Verifyrule.

Import ListNotations.

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

Definition tocharset p : option charset :=
  match p with
  | PSet f => Some f
  | _ => None
  end.

Inductive first : grammar -> pat -> charset -> bool -> charset -> Prop :=
  | FEmpty :
      forall g cs,
      first g PEmpty cs true cs
  | FSet :
      forall g cs cs',
      first g (PSet cs') cs false cs'
  | FSequenceNullableSomeFalse :
      forall g p1 p2 cs b cs',
      nullable g p1 false ->
      first g p1 fullcharset b cs' ->
      first g (PSequence p1 p2) cs b cs'
  | FSequenceNullableSomeTrue :
      forall g p1 p2 cs b1 b2 cs1 cs2,
      nullable g p1 true ->
      first g p2 cs b2 cs2 ->
      first g p1 cs2 b1 cs1 ->
      first g (PSequence p1 p2) cs (andb b1 b2) cs1
  | FChoice :
      forall g p1 p2 cs cs1 cs2 b1 b2,
      first g p1 cs b1 cs1 ->
      first g p2 cs b2 cs2 ->
      first g (PChoice p1 p2) cs (orb b1 b2) (cs1 U cs2)
  | FRepetition :
      forall g p cs b cs',
      first g p cs b cs' ->
      first g (PRepetition p) cs true (cs U cs')
  | FNotNone :
      forall g p cs,
      tocharset p = None ->
      first g (PNot p) cs true cs
  | FNotSome :
      forall g p cs cs',
      tocharset p = Some cs' ->
      first g (PNot p) cs true (complementcharset cs')
  | FNT :
      forall g i p cs b cs',
      nth_error g i = Some p ->
      first g p cs b cs' ->
      first g (PNT i) cs b cs'
  .

Theorem first_determinism :
  forall g p cs b1 b2 cs1 cs2,
  first g p cs b1 cs1 ->
  first g p cs b2 cs2 ->
  b1 = b2 /\ cs1 = cs2.
Proof.
  intros * H1 H2.
  generalize dependent cs2.
  generalize dependent b2.
  induction H1; intros;
  inversion H2; subst;
  try pose_nullable_determinism;
  try destruct2sep;
  try destruct1sep;
  repeat match goal with
    [ IHx: forall bx csx, first ?g ?p ?cs bx csx -> _ = bx /\ _ = csx,
      Hx: first ?g ?p ?cs _ _ |- _ ] =>
          apply IHx in Hx;
          destruct Hx;
          subst
  end;
  try discriminate;
  eauto using first.
Qed.

Ltac pose_first_determinism :=
  match goal with
    [ _: first ?g ?p ?cs ?b1 ?cs1,
      _: first ?g ?p ?cs ?b2 ?cs2 |- _ ] =>
            assert (b1 = b2 /\ cs1 = cs2)
            as [? ?] by eauto using first_determinism
  end.

Theorem first_complete :
  forall g p cs,
  verifygrammarpat g p true ->
  exists b cs', first g p cs b cs'.
Proof.
  intros * Hvgp.
  assert (exists nb d b k, verifyrule g p d nb (Some b) k)
  as [nb [d [b [k Hvr]]]] by eauto using verifygrammarpat_verifyrule.
  remember (Some b) as res.
  generalize dependent cs.
  generalize dependent b.
  clear Hvgp.
  induction Hvr; intros;
  try discriminate;
  try destruct1;
  try (eauto using first; fail).
  - (* PSequence p1 p2; where p1 is nullable *)
    assert (nullable g p1 true)
    by eauto using verifyrule_similar_to_nullable.
    assert (exists b cs', first g p2 cs b cs')
    as [? [cs2 ?]] by eauto.
    assert (exists b cs', first g p1 cs2 b cs')
    as [? [? ?]] by eauto.
    eauto using first.
  - (* PSequence p1 p2; where p1 is non-nullable *)
    assert (nullable g p1 false)
    by eauto using verifyrule_similar_to_nullable.
    assert (exists b cs', first g p1 fullcharset b cs')
    as [? [? ?]] by eauto.
    eauto using first.
  - (* PChoice p1 p2 *)
    assert (exists b cs', first g p1 cs b cs')
    as [? [? ?]] by eauto.
    assert (exists b cs', first g p2 cs b cs')
    as [? [? ?]] by eauto.
    eauto using first.
  - (* PRepetition p *)
    assert (exists b cs', first g p cs b cs')
    as [? [? ?]] by eauto.
    eauto using first.
  - (* PNot p *)
    destruct (tocharset p) eqn:?;
    eauto using first.
  - (* PNT i *)
    assert (exists b cs', first g p cs b cs')
    as [? [? ?]] by eauto.
    eauto using first.
Qed.

Lemma first_false :
  forall g p cs cs',
  verifygrammarpat g p true ->
  first g p cs false cs' ->
  matches g p EmptyString Failure.
Proof.
  intros * Hvgp Hf.
  remember false as b in Hf.
  induction Hf;
  try match goal with
    [ Hx: ?b1 && ?b2 = false |- _ ] =>
        destruct b1;
        destruct b2;
        simpl in Hx
  end;
  try match goal with
    [ Hx: ?b1 || ?b2 = false |- _ ] =>
        destruct b1;
        destruct b2;
        simpl in Hx
  end;
  try match goal with
    [ _: verifygrammarpat ?g (_ ?p1 ?p2) true |- _ ] =>
      assert (verifygrammarpat g p1 true)
      by eauto using pat_le, verifygrammarpat_true_le;
      assert (verifygrammarpat g p2 true)
      by eauto using pat_le, verifygrammarpat_true_le;
      assert (exists res, matches g p1 EmptyString res)
      as [[|?] ?] by eauto using verifygrammarpat_safe_match
  end;
  try match goal with
    [ _: matches _ _ EmptyString (Success ?s) |- _ ] =>
        let H := fresh "H" in (
          assert (suffix s EmptyString)
          as H by eauto using matches_suffix;
          inversion H; subst
        )
  end;
  try match goal with
    [ Hvgp: verifygrammarpat ?g (PNT ?i) true,
      _: nth_error ?g ?i = Some ?p |- _ ] =>
          inversion Hvgp; subst;
          assert (verifygrammarpat g p true)
          by eauto using nth_error_In, verifygrammarpat_true_In
  end;
  try discriminate;
  eauto using matches.
Qed.

Lemma first_true :
  forall g p cs,
  verifygrammarpat g p true ->
  matches g p EmptyString (Success EmptyString) ->
  exists cs', first g p cs true cs'.
Proof.
  intros * Hvgp Hm.
  assert (exists b cs', first g p cs b cs')
  as [b [cs' ?]] by eauto using first_complete.
  destruct b.
  - (* true *)
    eauto.
  - (* false *)
    assert (matches g p EmptyString Failure)
    by eauto using first_false.
    pose_matches_determinism.
    discriminate.
Qed.
