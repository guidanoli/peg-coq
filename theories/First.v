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

Inductive first : grammar -> pat -> charset -> nat -> option (bool * charset) -> Prop :=
  | FEmpty :
      forall g cs d,
      first g PEmpty cs d (Some (true, cs))
  | FSet :
      forall g cs cs' d,
      first g (PSet cs') cs d (Some (false, cs'))
  | FSequenceNullableNone :
      forall g p1 p2 cs d,
      nullable g p1 d None ->
      first g (PSequence p1 p2) cs d None
  | FSequenceNullableSomeFalse :
      forall g p1 p2 cs d res,
      nullable g p1 d (Some false) ->
      first g p1 fullcharset d res ->
      first g (PSequence p1 p2) cs d res
  | FSequenceNullableSomeTrueFirst2None :
      forall g p1 p2 cs d,
      nullable g p1 d (Some true) ->
      first g p2 cs d None ->
      first g (PSequence p1 p2) cs d None
  | FSequenceNullableSomeTrueFirst1None :
      forall g p1 p2 cs d b2 cs2,
      nullable g p1 d (Some true) ->
      first g p2 cs d (Some (b2, cs2)) ->
      first g p1 cs2 d None ->
      first g (PSequence p1 p2) cs d None
  | FSequenceNullableSomeTrueFirstSome :
      forall g p1 p2 cs d b1 b2 cs1 cs2,
      nullable g p1 d (Some true) ->
      first g p2 cs d (Some (b2, cs2)) ->
      first g p1 cs2 d (Some (b1, cs1)) ->
      first g (PSequence p1 p2) cs d (Some (andb b1 b2, cs1))
  | FChoiceNone1 :
      forall g p1 p2 cs d,
      first g p1 cs d None ->
      first g (PChoice p1 p2) cs d None
  | FChoiceNone2 :
      forall g p1 p2 cs d,
      first g p2 cs d None ->
      first g (PChoice p1 p2) cs d None
  | FChoiceSome :
      forall g p1 p2 cs cs1 cs2 d b1 b2,
      first g p1 cs d (Some (b1, cs1)) ->
      first g p2 cs d (Some (b2, cs2)) ->
      first g (PChoice p1 p2) cs d (Some (orb b1 b2, unioncharset cs1 cs2))
  | FRepetitionNone :
      forall g p cs d,
      first g p cs d None ->
      first g (PRepetition p) cs d None
  | FRepetitionSome :
      forall g p cs d b cs',
      first g p cs d (Some (b, cs')) ->
      first g (PRepetition p) cs d (Some (true, unioncharset cs cs'))
  | FNotNone :
      forall g p cs d,
      tocharset p = None ->
      first g (PNot p) cs d (Some (true, cs))
  | FNotSome :
      forall g p cs cs' d,
      tocharset p = Some cs' ->
      first g (PNot p) cs d (Some (true, complementcharset cs'))
  | FNTZero :
      forall g i cs,
      first g (PNT i) cs 0 None
  | FNTSucc :
      forall g i p cs d res,
      nth_error g i = Some p ->
      first g p cs d res ->
      first g (PNT i) cs (S d) res
  .

Theorem first_deterministic :
  forall g p cs d res1 res2,
  first g p cs d res1 ->
  first g p cs d res2 ->
  res1 = res2.
Proof.
  intros * H1 H2.
  generalize dependent res2.
  induction H1; intros;
  inversion H2; subst;
  try pose_nullable_determinism;
  try match goal with
    [ Hx1: nth_error ?g ?i = _,
      Hx2: nth_error ?g ?i = _ |- _ ] =>
          rewrite Hx1 in Hx2;
          try destruct1
  end;
  try match goal with
    [ Hx1: tocharset ?p = _,
      Hx2: tocharset ?p = _ |- _ ] =>
        rewrite Hx1 in Hx2;
        try destruct1
  end;
  repeat match goal with
    [ IHx: forall resx, first ?g ?p ?cs ?d resx -> _ = resx,
      Hx: first ?g ?p ?cs ?d _ |- _ ] =>
          apply IHx in Hx;
          try destruct1
  end;
  try discriminate;
  eauto using first.
Qed.

Theorem first_nullable :
  forall g p cs cs' d b,
  matches g p EmptyString (Success EmptyString) ->
  first g p cs d (Some (b, cs')) ->
  b = true.
Proof.
  intros * Hm Hf.
  remember (Some (b, cs')).
  generalize dependent cs'.
  generalize dependent b.
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

Theorem first_Some_S_depth :
  forall g p cs d res,
  first g p cs d (Some res) ->
  first g p cs (S d) (Some res).
Proof.
  intros * H.
  remember (Some res).
  generalize dependent res.
  induction H; intros;
  subst;
  try discriminate;
  eauto using first, nullable_Some_S_depth.
Qed.

Theorem first_Some_depth_le :
  forall g p cs d d' res,
  first g p cs d (Some res) ->
  d <= d' ->
  first g p cs d' (Some res).
Proof.
  intros * H Hle.
  induction Hle;
  eauto using first_Some_S_depth.
Qed.

Theorem first_complete :
  forall g p cs,
  verifygrammarpat g p true ->
  exists d res, first g p cs d (Some res).
Proof.
  intros * Hvgp.
  assert (exists nb d b k, verifyrule g p d nb (Some b) k)
  as [nb [d [b [k Hvr]]]] by eauto using verifygrammarpat_verifyrule.
  remember (Some b) as res.
  generalize dependent b.
  clear Hvgp.
  generalize dependent cs.
  induction Hvr; intros;
  try discriminate;
  try destruct1;
  try (exists 0; eauto using first; fail).
  - (* PSequence p1 p2; where p1 is nullable *)
    assert (exists d, nullable g p1 d (Some true))
    as [d1n ?] by eauto using verifyrule_similar_to_nullable.
    assert (exists d res, first g p2 cs d (Some res))
    as [d2f [[b2 cs2] ?]] by eauto.
    assert (exists d res, first g p1 cs2 d (Some res))
    as [d1f [[b1 cs1] ?]] by eauto.
    pose (d1n + d1f + d2f) as dsum.
    assert (d1n <= dsum) by lia.
    assert (d1f <= dsum) by lia.
    assert (d2f <= dsum) by lia.
    exists dsum.
    assert (nullable g p1 dsum (Some true))
    by eauto using nullable_Some_depth_le.
    eauto using first, first_Some_depth_le.
  - (* PSequence p1 p2; where p1 is non-nullable *)
    assert (exists d, nullable g p1 d (Some false))
    as [d1n ?] by eauto using verifyrule_similar_to_nullable.
    assert (exists d res, first g p1 fullcharset d (Some res))
    as [d1f [[b1 cs1] ?]] by eauto.
    pose (d1n + d1f) as dsum.
    assert (d1n <= dsum) by lia.
    assert (d1f <= dsum) by lia.
    exists dsum.
    eauto using first, first_Some_depth_le, nullable_Some_depth_le.
  - (* PChoice p1 p2 *)
    assert (exists d res, first g p1 cs d (Some res))
    as [d1f [[b1 cs1] ?]] by eauto.
    assert (exists d res, first g p2 cs d (Some res))
    as [d2f [[b2 cs2] ?]] by eauto.
    pose (d1f + d2f) as dsum.
    assert (d1f <= dsum) by lia.
    assert (d2f <= dsum) by lia.
    exists dsum.
    eauto using first, first_Some_depth_le.
  - (* PRepetition p *)
    assert (exists d res, first g p cs d (Some res))
    as [d' [[? ?] ?]] by eauto.
    eauto using first.
  - (* PNot p *)
    exists 0.
    destruct (tocharset p) eqn:?;
    eauto using first.
  - (* PNT i *)
    assert (exists d res, first g p cs d (Some res))
    as [d' [[? ?] ?]] by eauto.
    eauto using first.
Qed.
