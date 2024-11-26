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

Ltac invert_matches P :=
  match goal with
    [ Hx: matches _ P _ _ |- _ ] =>
        inversion Hx; clear Hx; subst
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

Definition PFail := PNot PEmpty.

(* !ε / p ≡ p *)
Lemma fail_is_choice_neutral_left :
  forall g p,
  equivalent g (PChoice PFail p) p.
Proof.
  unfold equivalent.
  intros.
  split; intro H.
  - (* -> *)
    inversion H; subst;
    try invert_matches PFail;
    try invert_matches PEmpty;
    eauto using matches.
  - (* <- *)
    eauto using matches.
Qed.

(* p / !ε ≡ p *)
Lemma fail_is_choice_neutral_right :
  forall g p,
  equivalent g (PChoice PFail p) p.
Proof.
  unfold equivalent.
  intros.
  split; intro H.
  - (* -> *)
    inversion H; subst;
    try invert_matches PFail;
    try invert_matches PEmpty;
    eauto using matches.
  - (* <- *)
    eauto using matches.
Qed.

(* !ε / p ≡ p / !ε *)
Lemma fail_in_choice_is_commutative :
  forall g p,
  equivalent g (PChoice PFail p) (PChoice PFail p).
Proof.
  eauto using equivalent_refl,
              equivalent_trans,
              fail_is_choice_neutral_left,
              fail_is_choice_neutral_right.
Qed.

Definition associative (P : pat -> pat -> pat) :=
  forall g p1 p2 p3,
  equivalent g (P (P p1 p2) p3) (P p1 (P p2 p3)).

(* (a . b) . c ≡ a . (b . c) *)
Lemma sequence_is_associative :
  associative PSequence.
Proof.
  unfold associative.
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


(* (a / b) / c ≡ a / (b / c) *)
Lemma choice_is_associative :
  associative PChoice.
Proof.
  unfold associative.
  unfold equivalent.
  intros.
  split; intro H.
  - (* -> *)
    inversion H; subst;
    invert_matches (PChoice p1 p2);
    eauto using matches.
  - (* <- *)
    inversion H; subst;
    try invert_matches (PChoice p2 p3);
    eauto using matches.
Qed.

Definition POptional p := PChoice p PEmpty.

Lemma optional_always_succeeds :
  forall g p s res,
  matches g (POptional p) s res ->
  exists s', res = Success s'.
Proof.
  intros.
  invert_matches (POptional p);
  try invert_matches PEmpty;
  eauto.
Qed.

(* p? . p? ≡ (p . p?)? *)
Lemma bounded_repetition_optional :
  forall g p,
  equivalent g (PSequence (POptional p) (POptional p))
               (POptional (PSequence p (POptional p))).
Proof.
  intros.
  unfold equivalent.
  intros.
  split; intro H.
  - (* -> *)
    inversion H; subst.
    + (* p? succeeds *)
      repeat invert_matches (POptional p);
      repeat invert_matches PEmpty;
      try (pose_matches_determinism; discriminate);
      eauto using matches.
    + (* p? fails *)
      invert_matches (POptional p).
      invert_matches PEmpty.
  - (* <- *)
    inversion H; subst.
    + (* (p . p?) succeeds *)
      invert_matches (PSequence p (POptional p)).
      eauto using matches.
    + (* (p . p?) fails and ε succeeds *)
      invert_matches PEmpty.
      invert_matches (PSequence p (POptional p)).
      -- (* p succeeds but p? fails *)
        invert_matches (POptional p).
        invert_matches PEmpty.
      -- (* p fails *)
         eauto using matches.
Qed.
