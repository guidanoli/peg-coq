From Coq Require Import Lists.List.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Peg Require Import Syntax.
From Peg Require Import Match.
From Peg Require Import Nullable.
From Peg Require Import Tactics.

Import ListNotations.

Definition charset : Type := (ascii -> bool).

(* Full charset *)
Definition fullcharset : charset :=
  (fun _ => true).

(* Charset with a single char *)
Definition singlecharset a : charset :=
  (fun b => (a =? b)%char).

(* Union of charsets *)
Definition unioncharset cs1 cs2 : charset :=
  (fun a => orb (cs1 a) (cs2 a)).

(* Set complement of a charset *)
Definition complementcharset cs : charset :=
  (fun a => negb (cs a)).

Definition tocharset p : option charset :=
  match p with
  | PChar a => Some (singlecharset a)
  | _ => None
  end.

Inductive first : grammar -> pat -> charset -> nat -> option (bool * charset) -> Prop :=
  | FEmpty :
      forall g cs d,
      first g PEmpty cs d (Some (true, cs))
  | FCharSet :
      forall g p cs cs' d,
      tocharset p = Some cs' ->
      first g p cs d (Some (false, cs'))
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
  | FSequenceNullableSomeTrueFirst2SomeFirst1None :
      forall g p1 p2 cs d b2 cs2,
      nullable g p1 d (Some true) ->
      first g p2 cs d (Some (b2, cs2)) ->
      first g p1 cs2 d None ->
      first g (PSequence p1 p2) cs d None
  | FSequenceNullableSomeTrueFirst2SomeFirst1Some :
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

Theorem first_correct :
  forall g p d b cs a s,
  first g p fullcharset d (Some (b, cs)) ->
  cs a = false ->
  matches g p (String a s) Failure.
Proof.
  intros * Hfirst Hcseq.
  generalize dependent s.
  generalize dependent a.
  remember (Some (b, cs)) as res.
  generalize dependent cs.
  generalize dependent b.
  remember fullcharset as flw.
  induction Hfirst;
  intros;
  try destruct1;
  unfold fullcharset in Hcseq;
  try discriminate.
  - (* FCharSet *)
    destruct p;
    try discriminate;
    simpl in *;
    destruct1;
    rewrite Ascii.eqb_neq in Hcseq;
    eauto using matches.
  - Abort.
