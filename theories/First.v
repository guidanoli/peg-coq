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
      forall g p1 p2 cs d b cs',
      nullable g p1 d (Some false) ->
      first g p1 fullcharset b cs' ->
      first g (PSequence p1 p2) cs b cs'
  | FSequenceNullableSomeTrue :
      forall g p1 p2 cs d b1 b2 cs1 cs2,
      nullable g p1 d (Some true) ->
      first g p2 cs b2 cs2 ->
      first g p1 cs2 b1 cs1 ->
      first g (PSequence p1 p2) cs (andb b1 b2) cs1
  | FChoice :
      forall g p1 p2 cs cs1 cs2 b1 b2,
      first g p1 cs b1 cs1 ->
      first g p2 cs b2 cs2 ->
      first g (PChoice p1 p2) cs (orb b1 b2) (unioncharset cs1 cs2)
  | FRepetition :
      forall g p cs b cs',
      first g p cs b cs' ->
      first g (PRepetition p) cs true (unioncharset cs cs')
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

Theorem first_deterministic :
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
  try pose_nullable_Some_determinism;
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

Theorem first_nullable :
  forall g p cs cs' b,
  matches g p EmptyString (Success EmptyString) ->
  first g p cs b cs' ->
  b = true.
Proof.
  intros * Hm Hf.
  induction Hf;
  intros;
  inversion Hm; subst;
  try destruct2;
  try discriminate;
  try match goal with
    [ Hx: matches ?g ?p ?s (Success EmptyString) |- _ ] =>
        let H := fresh "H" in (
          assert (suffix EmptyString s) as H
          by eauto using matches_suffix;
          inversion H; subst
        )
  end;
  try match goal with
    [ Hx: matches ?g ?p EmptyString (Success (String ?a ?s)) |- _ ] =>
        let H := fresh "H" in (
          assert (suffix (String a s) EmptyString) as H
          by eauto using matches_suffix;
          inversion H; subst
        )
  end;
  try destruct2sep;
  eauto using matches, andb_true_intro, orb_true_intro.
Qed.

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
    assert (exists d, nullable g p1 d (Some true))
    as [? ?] by eauto using verifyrule_similar_to_nullable.
    assert (exists b cs', first g p2 cs b cs')
    as [? [cs2 ?]] by eauto.
    assert (exists b cs', first g p1 cs2 b cs')
    as [? [? ?]] by eauto.
    eauto using first.
  - (* PSequence p1 p2; where p1 is non-nullable *)
    assert (exists d, nullable g p1 d (Some false))
    as [? ?] by eauto using verifyrule_similar_to_nullable.
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
