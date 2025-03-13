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

Notation "cs1 '∪' cs2" := (unioncharset cs1 cs2) (at level 130, right associativity).

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

Lemma unioncharset_emptycharset_l :
  forall cs,
  (emptycharset ∪ cs) = cs.
Proof.
  intros.
  extensionality a.
  auto.
Qed.

Lemma unioncharset_emptycharset_r :
  forall cs,
  (cs ∪ emptycharset) = cs.
Proof.
  intros.
  extensionality a.
  unfold emptycharset.
  unfold unioncharset.
  auto using orb_false_r.
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

Lemma unioncharset_intersectioncharset_simpl :
  forall cs1 cs2, (cs1 ∪ (cs1 ∩ cs2)) = cs1.
Proof.
  intros.
  unfold unioncharset.
  unfold intersectioncharset.
  extensionality a.
  destruct (cs1 a);
  destruct (cs2 a);
  auto.
Qed.

Inductive subcharseteq : charset -> charset -> Prop :=
  | SubCharSetEq :
      forall cs1 cs2,
      subcharseteq cs1 (cs1 ∪ cs2)
  .

Notation "cs1 '⊆' cs2" := (subcharseteq cs1 cs2) (at level 120, right associativity).

Lemma subcharseteq_refl :
  forall cs,
  cs ⊆ cs.
Proof.
  intros.
  assert (cs ⊆ (cs ∪ cs))
  as H by eauto using subcharseteq.
  rewrite unioncharset_diag in H.
  auto.
Qed.

Lemma subcharseteq_empty :
  forall cs,
  emptycharset ⊆ cs.
Proof.
  intros.
  assert (emptycharset ⊆ (emptycharset ∪ cs))
  as H by eauto using subcharseteq.
  rewrite unioncharset_emptycharset_l in H.
  auto.
Qed.

Lemma subcharseteq_trans :
  forall cs1 cs2 cs3,
  (cs1 ⊆ cs2) ->
  (cs2 ⊆ cs3) ->
  (cs1 ⊆ cs3).
Proof.
  intros * H12 H23.
  inversion H12; subst.
  inversion H23; subst.
  rewrite <- unioncharset_assoc.
  eauto using subcharseteq.
Qed.
