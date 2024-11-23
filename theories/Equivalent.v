From Peg Require Import Syntax.
From Peg Require Import Match.

Definition equivalent g p1 p2 :=
  forall s res, matches g p1 s res <-> matches g p2 s res.

Lemma equivalent_refl :
  forall g p1 p2,
  equivalent g p1 p2 ->
  equivalent g p2 p1.
Proof.
  unfold equivalent.
  intros * H s res.
  split; intro.
  - (* p2 -> p1 *)
    rewrite H.
    auto.
  - (* p1 -> p2 *)
    rewrite <- H.
    auto.
Qed.

Lemma equivalent_trans :
  forall g p1 p2 p3,
  equivalent g p1 p2 ->
  equivalent g p2 p3 ->
  equivalent g p1 p3.
Proof.
  unfold equivalent.
  intros * H12 H23 s res.
  split; intro.
  - (* p1 -> p3 *)
    rewrite <- H23.
    rewrite <- H12.
    auto.
  - (* p3 -> p1 *)
    rewrite H12.
    rewrite H23.
    auto.
Qed.

(**

 (a / b) / c ≡ a / (b / c)
 p? . p? ≡ (p . p?)?

 **)

Ltac invert_matches P :=
  match goal with
    [ Hx: matches _ P _ _ |- _ ] =>
        inversion Hx; subst
  end.

(* p ≡ p . ε *)
Lemma empty_is_sequence_neutral_element_right :
  forall g p,
  equivalent g p (PSequence p PEmpty).
Proof.
  unfold equivalent.
  intros.
  split; intro.
  - (* -> *)
    destruct res;
    eauto using matches.
  - (* <- *)
    inversion H; subst;
    try invert_matches PEmpty;
    eauto using matches.
Qed.

(* p ≡ ε . p *)
Lemma empty_is_sequence_neutral_element_left :
  forall g p,
  equivalent g p (PSequence PEmpty p).
Proof.
  unfold equivalent.
  intros.
  split; intro.
  - (* -> *)
    eauto using matches.
  - (* <- *)
    inversion H; subst;
    try invert_matches PEmpty;
    eauto using matches.
Qed.

(* ε . p ≡ p . ε *)
Lemma empty_in_sequence_is_commutable :
  forall g p,
  equivalent g (PSequence PEmpty p) (PSequence p PEmpty).
Proof.
  eauto using equivalent_refl,
              equivalent_trans,
              empty_is_sequence_neutral_element_left,
              empty_is_sequence_neutral_element_right.
Qed.

(* !ε / p ≡ p *)
Lemma fail_is_choice_neutral_left :
  forall g p,
  equivalent g (PChoice (PNot PEmpty) p) p.
Proof.
  unfold equivalent.
  intros.
  split; intro H.
  - (* -> *)
    inversion H; subst;
    try invert_matches (PNot PEmpty);
    try invert_matches PEmpty;
    eauto using matches.
  - (* <- *)
    eauto using matches.
Qed.

(* p / !ε ≡ p *)
Lemma fail_is_choice_neutral_right :
  forall g p,
  equivalent g (PChoice (PNot PEmpty) p) p.
Proof.
  unfold equivalent.
  intros.
  split; intro H.
  - (* -> *)
    inversion H; subst;
    try invert_matches (PNot PEmpty);
    try invert_matches PEmpty;
    eauto using matches.
  - (* <- *)
    eauto using matches.
Qed.

(* !ε / p ≡ p / !ε *)
Lemma fail_in_choice_is_commutative :
  forall g p,
  equivalent g (PChoice (PNot PEmpty) p) (PChoice (PNot PEmpty) p).
Proof.
  eauto using equivalent_refl,
              equivalent_trans,
              fail_is_choice_neutral_left,
              fail_is_choice_neutral_right.
Qed.


(* (a . b) . c ≡ a . (b . c) *)
Lemma sequence_is_associative :
  forall g p1 p2 p3,
  equivalent g (PSequence (PSequence p1 p2) p3) (PSequence p1 (PSequence p2 p3)).
Proof.
  unfold equivalent.
  intros.
  split; intro H.
  - (* -> *)
    inversion H; subst;
    invert_matches (PSequence p1 p2);
    eauto using matches.
  - (* <- *)
    inversion H; subst;
    try invert_matches (PSequence p2 p3);
    eauto using matches.
Qed.
