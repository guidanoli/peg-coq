From Coq Require Import Bool.
From Coq Require Import Strings.Ascii.
From Coq Require Import Logic.FunctionalExtensionality.
From Peg Require Import Tactics.

Definition charset : Type := (ascii -> bool).

(* Empty charset *)
Definition emptycharset : charset :=
  (fun _ => false).

(* Full charset *)
Definition fullcharset : charset :=
  (fun _ => true).

(* Union of charsets *)
Definition unioncharset cs1 cs2 : charset :=
  (fun a => orb (cs1 a) (cs2 a)).

Notation "cs1 'U' cs2" := (unioncharset cs1 cs2) (at level 120, right associativity).

(* Intersection of charsets *)
Definition intersectioncharset cs1 cs2 : charset :=
  (fun a => andb (cs1 a) (cs2 a)).

(* Set complement of a charset *)
Definition complementcharset cs : charset :=
  (fun a => negb (cs a)).

Lemma unioncharset_diag :
  forall cs, (cs U cs) = cs.
Proof.
  intros.
  extensionality a.
  eauto using orb_diag.
Qed.

Lemma unioncharset_assoc :
  forall cs1 cs2 cs3, (cs1 U (cs2 U cs3)) = ((cs1 U cs2) U cs3).
Proof.
  intros.
  extensionality a.
  eauto using orb_assoc.
Qed.

Lemma unioncharset_comm :
  forall cs1 cs2, (cs1 U cs2) = (cs2 U cs1).
Proof.
  intros.
  extensionality a.
  eauto using orb_comm.
Qed.

Lemma unioncharset_rep_l :
  forall cs1 cs2 cs3, ((cs1 U cs3) U (cs2 U cs3)) = ((cs1 U cs2) U cs3).
Proof.
  intros.
  extensionality a.
  unfold unioncharset.
  destruct (cs1 a);
  destruct (cs2 a);
  destruct (cs3 a);
  eauto.
Qed.

Lemma unioncharset_fullcharset_l :
  forall cs,
  (fullcharset U cs) = fullcharset.
Proof.
  intros.
  extensionality a.
  auto.
Qed.
