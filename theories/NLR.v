From Coq Require Import Arith.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.
From Coq Require Import Classes.EquivDec.

From Peg Require Import Syntax.
From Peg Require Import Ncode.
From Peg Require Import NMatch.
From Peg Require Import NVerifyrule.

Set Implicit Arguments.


Inductive noleftrec : grammar -> pat -> bool -> Prop :=
  | NLREmpty :
      forall g,
      noleftrec g PEmpty true
  | NLRSet :
      forall g cs,
      noleftrec g (PSet cs) false
  | NLRSequenceSomeTrue :
      forall g p1 p2 nb,
      noleftrec g p1 true ->
      noleftrec g p2 nb ->
      noleftrec g (PSequence p1 p2) nb
  | NLRSequenceSomeFalse :
      forall g p1 p2, 
      noleftrec g p1 false ->
      noleftrec g (PSequence p1 p2) false
  | NLRChoice :
      forall g p1 p2 nb nb',
      noleftrec g p1 nb ->
      noleftrec g p2 nb' ->
      noleftrec g (PChoice p1 p2) (orb nb nb')
  | NLRRepetition :
      forall g p nb,
      noleftrec g p nb ->
      noleftrec g (PRepetition p) true
  | NLRNot :
      forall g p nb,
      noleftrec g p nb ->
      noleftrec g (PNot p) true
  | NLRAnd :
      forall g p nb,
      noleftrec g p nb ->
      noleftrec g (PAnd p) true
  | NLRNT :
      forall g i p nb,
      nth i g PEmpty = p ->
      noleftrec g p nb ->
      noleftrec g (PNT i) nb 
.


Lemma uniqueNLRnb: forall g p nb nb',
    noleftrec g p nb ->
    noleftrec g p nb' ->
    nb = nb'.
Proof.
  intros * H1.
  generalize dependent nb'.
  induction H1; intros * H2; inversion H2;
  subst; intuition; try congruence.
  repeat f_equal; auto.
Qed.


Lemma update_coher : forall g p lr i, 
  nth i lr Visiting = NotVisited ->
  (forall (n : nat) (nb' : bool),
     nth n lr Visiting = Visited nb' -> noleftrec g p nb') ->
  (forall (n : nat) (nb' : bool),
     nth n (update lr i Visiting) Visiting = Visited nb' -> noleftrec g p nb').
Proof.
  intros * H1 * H2 * H3.
  destruct (Nat.eq_dec n i); subst.
  - exfalso. erewrite update_eq in H3; try discriminate.
    eapply nth_overflow'; eauto. congruence.
  - erewrite update_neq in H3; eauto.
Qed.


Ltac simplOrb :=
    repeat rewrite Bool.orb_false_r;
    try rewrite Bool.orb_false_r in *;
    repeat rewrite Bool.orb_true_r;
    try rewrite Bool.orb_true_r in *;
    repeat rewrite Bool.orb_true_l;
    try rewrite Bool.orb_true_l in *;
    repeat rewrite Bool.orb_false_l;
    try rewrite Bool.orb_false_l in *.


Definition LRCoher (g : grammar) lr :=
  forall n nb, nth n lr Visiting = Visited nb -> noleftrec g (PNT n) nb.



Theorem NLRpreservation : forall g p lr nb onb lr',
    verifyrule g p lr nb (Some (onb, lr')) ->
    LRCoher g lr ->
    (exists nb', noleftrec g p nb' /\ onb = orb nb nb') /\ LRCoher g lr'.
Proof.
  unfold LRCoher.
  intros * HVR.
  remember (Some (onb, lr')) as res.
  generalize dependent onb.
  generalize dependent lr'.
  induction HVR;
  intros * HEqS; try discriminate;
  try (injection HEqS; intros; subst; clear HEqS); subst; split;
    repeat match goal with
    [H: forall _ _, Some _ = Some _ -> ?e -> _,
     H1: ?e |- _] =>
       specialize (H _ _ eq_refl H1) as [[? ?] ?] end;
    repeat match goal with
    [H: _ /\ _ |- _] => 
      destruct H as [? ?] end;
    subst; simplOrb; subst;
    eauto using noleftrec;
     try (eexists; split; eauto using noleftrec;
     simplOrb; try (rewrite Bool.orb_assoc); trivial; fail).
  - match goal with
    [H: forall _ _, _ = _ -> ?e -> _ |- _] =>
      specialize (H _ _ eq_refl); assert(HH: e) end.
    { intros * H1.
      destruct (Nat.eq_dec n i); subst.
      - exfalso. erewrite update_eq in H1; try discriminate.
        eapply nth_overflow'; eauto. congruence.
      - erewrite update_neq in H1; eauto. }
    specialize (IHHVR HH) as [[? [? ?]] ?].
    eexists; split; eauto using noleftrec.
    simplOrb; subst; trivial.
  - intros * H1.
    destruct (Nat.eq_dec n i); subst.
    + match goal with
      [H: forall _ _, _ = _ -> ?e -> _ |- _] =>
        specialize (H _ _ eq_refl); assert(HH: e) end.
      { intros * HH1.
        destruct (Nat.eq_dec n i); subst.
        - exfalso. erewrite update_eq in HH1; try discriminate.
          eapply nth_overflow'; eauto. congruence.
        - erewrite update_neq in HH1; eauto. }
      eapply IHHVR in HH.
      destruct HH as [[? [? ?]] ?].
      replace nb0 with nb' in *.
      * simplOrb; subst.
        econstructor.
        ** reflexivity.
        ** eauto.
      * clear IHHVR H3 H4.
        erewrite update_eq in H1; try congruence.
        replace (length lr') with (length lr).
        ** eapply nth_overflow'; eauto. congruence.
        ** erewrite <- update_len. eauto using sameLen.
    + rewrite update_neq in H1; trivial.
      match goal with
      [H: forall _ _, _ = _ -> ?e -> _ |- _] =>
        specialize (H _ _ eq_refl); assert(HH: e) end.
        { intros * HHH.
          destruct (Nat.eq_dec n1 i); subst.
          - exfalso. erewrite update_eq in HHH; try discriminate.
            eapply nth_overflow'; eauto. congruence.
          - erewrite update_neq in HHH; eauto. }
      apply IHHVR in HH.
      eapply HH. trivial.
Qed.


Lemma not_null_nt: forall g p n,
    not_nullable g p ->
    nth n g PEmpty = p ->
    not_nullable g (PNT n).
Proof.
  unfold not_nullable.
  intros * HNN Heq.
  inversion 1; subst.
  eapply HNN. eauto.
Qed.


Lemma nlr_nullable : forall g p,
   noleftrec g p false -> not_nullable g p.
Proof.
  intros * HNLR.
  remember false as nbF eqn:Heq.
  induction HNLR; try discriminate;
  intros *;
    eauto using not_null_set, not_null_seq2, not_null_seq1,
                not_null_choice, not_null_nt.
  apply Bool.orb_false_elim in Heq; destruct Heq; subst.
  eauto using not_null_choice.
Qed.


