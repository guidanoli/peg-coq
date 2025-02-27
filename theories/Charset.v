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

Notation "cs1 '∪' cs2" := (unioncharset cs1 cs2) (at level 120, right associativity).

(* Intersection of charsets *)
Definition intersectioncharset cs1 cs2 : charset :=
  (fun a => andb (cs1 a) (cs2 a)).

Notation "cs1 '∩' cs2" := (intersectioncharset cs1 cs2) (at level 120, right associativity).

(* Set complement of a charset *)
Definition complementcharset cs : charset :=
  (fun a => negb (cs a)).

(* Disjoint charsets *)
Definition disjointcharsets cs1 cs2 : Prop :=
  (cs1 ∩ cs2) = emptycharset.

Lemma unioncharset_diag :
  forall cs, (cs ∪ cs) = cs.
Proof.
  intros.
  extensionality a.
  eauto using orb_diag.
Qed.

Lemma unioncharset_assoc :
  forall cs1 cs2 cs3, (cs1 ∪ (cs2 ∪ cs3)) = ((cs1 ∪ cs2) ∪ cs3).
Proof.
  intros.
  extensionality a.
  eauto using orb_assoc.
Qed.

Lemma unioncharset_comm :
  forall cs1 cs2, (cs1 ∪ cs2) = (cs2 ∪ cs1).
Proof.
  intros.
  extensionality a.
  eauto using orb_comm.
Qed.

Lemma unioncharset_rep_l :
  forall cs1 cs2 cs3, ((cs1 ∪ cs3) ∪ (cs2 ∪ cs3)) = ((cs1 ∪ cs2) ∪ cs3).
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
  (fullcharset ∪ cs) = fullcharset.
Proof.
  intros.
  extensionality a.
  auto.
Qed.

Lemma disjointcharsets_def :
  forall cs1 cs2,
  disjointcharsets cs1 cs2 ->
  ~ exists a, cs1 a = true /\ cs2 a = true.
Proof.
  intros * H.
  intros [a [H1 H2]].
  unfold disjointcharsets in H.
  apply equal_f with a in H.
  unfold intersectioncharset in H.
  unfold emptycharset in H.
  rewrite H1 in H.
  rewrite H2 in H.
  discriminate.
Qed.
