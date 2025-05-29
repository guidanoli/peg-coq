From Coq Require Import Arith.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.
From Coq Require Import Classes.EquivDec.

From Peg Require Import Syntax.
From Peg Require Import NMatch.
From Peg Require Import NVerifyrule.


Inductive noleftrec : grammar -> pat -> bool -> list nat -> Prop :=
  | VREmpty :
      forall g,
      noleftrec g PEmpty true []
  | VRSet :
      forall g cs,
      noleftrec g (PSet cs) false []
  | VRSequenceSomeTrue :
      forall g p1 p2 ln ln' nb,
      noleftrec g p1 true ln ->
      noleftrec g p2 nb ln' ->
      noleftrec g (PSequence p1 p2) nb (ln ++ ln')
  | VRSequenceSomeFalse :
      forall g p1 p2 ln,
      noleftrec g p1 false ln ->
      noleftrec g (PSequence p1 p2) false ln
  | VRChoice :
      forall g p1 p2 ln ln' nb nb',
      noleftrec g p1 nb ln ->
      noleftrec g p2 nb' ln' ->
      noleftrec g (PChoice p1 p2) (orb nb nb') (ln ++ ln')
  | VRRepetition :
      forall g p ln nb,
      noleftrec g p nb ln ->
      noleftrec g (PRepetition p) true ln 
  | VRNot :
      forall g p ln nb,
      noleftrec g p nb ln ->
      noleftrec g (PNot p) true ln
  | VRAnd :
      forall g p ln nb,
      noleftrec g p nb ln ->
      noleftrec g (PAnd p) true ln
  | VRNT :
      forall g i p ln nb,
      nth i g PEmpty = p ->
      noleftrec g p nb ln ->
      noleftrec g (PNT i) nb (i :: ln)
.


Lemma NLRunique : forall g p ln nb ln' nb',
  noleftrec g p nb ln ->
  noleftrec g p nb' ln' ->
  nb = nb' /\ ln = ln'.
Proof.
  intros * H1.
  generalize dependent nb'.
  generalize dependent ln'.
  induction H1; intros * H2; inversion H2; subst;
  repeat match goal with
    [HI: forall _ _,  (noleftrec _ ?p _ _) -> _,
     H: noleftrec _ ?p _ _ |- _] =>
         apply HI in H; destruct H as [? ?]
  end; subst; try discriminate; eauto.
Qed.


Lemma NLRInherit : forall g p ln nb n,
  noleftrec g p nb ln ->
  In n ln ->
  exists nb' ln',
    noleftrec g (PNT n) nb' ln' /\ length ln' <= length ln.
Proof.
  induction 1; intros HIn;
  try (exfalso; eauto using in_nil; fail);
  try (apply IHnoleftrec in HIn; destruct HIn as [? [? ?]];
      eexists; eexists; eauto; fail).
  - apply in_app_or in HIn. destruct HIn as [H1 | H1].
    + apply IHnoleftrec1 in H1. destruct H1 as [? [? [? ?]]].
      eexists; eexists; split; eauto. rewrite app_length. lia.
    + apply IHnoleftrec2 in H1. destruct H1 as [? [? [? ?]]].
      eexists; eexists; split; eauto. rewrite app_length. lia.
  - apply in_app_or in HIn. destruct HIn as [H1 | H1].
    + apply IHnoleftrec1 in H1. destruct H1 as [? [? [? ?]]].
      eexists; eexists; split; eauto. rewrite app_length. lia.
    + apply IHnoleftrec2 in H1. destruct H1 as [? [? [? ?]]].
      eexists; eexists; split; eauto. rewrite app_length. lia.
  - apply in_inv in HIn. destruct HIn as [H1 | H1]; subst;
      eauto using noleftrec.
    apply IHnoleftrec in H1. destruct H1 as [? [? [? ?]]].
    eexists; eexists; split; eauto. simpl. lia.
Qed.


Lemma update_coher : forall g p lr i, 
  nth i lr Visiting = NotVisited ->
  (forall (n : nat) (nb' : bool),
     nth n lr Visiting = Visited nb' ->
       exists ln : list nat, noleftrec g p nb' ln) ->
  (forall (n : nat) (nb' : bool),
     nth n (update lr i Visiting) Visiting = Visited nb' ->
       exists ln : list nat, noleftrec g p nb' ln).
Proof.
  intros * H1 * H2 * H3.
  destruct (Nat.eq_dec n i); subst.
  - exfalso. erewrite update_eq in H3; try discriminate.
    eapply nth_overflow'; eauto. congruence.
  - erewrite update_neq in H3; eauto.
Qed.


Lemma NLRNoLoops : forall g ln nb n,
  noleftrec g (nth n g PEmpty) nb ln ->
  ~In n ln.
Proof.
  intros * HNL HIn.
  assert (noleftrec g (PNT n) nb (n :: ln)) by eauto using noleftrec.
  eapply NLRInherit in HNL; eauto.
  destruct HNL as [? [? [? ?]]].
  replace x0 with (n :: ln) in * by (eapply NLRunique; eauto).
  simpl in H1. lia.
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


Theorem NLRpreservation : forall g p lr nb onb lr',
    verifyrule g p lr nb (Some (onb, lr')) ->
    (forall n nb',
       nth n lr Visiting = Visited nb' ->
           (exists ln, noleftrec g (PNT n) nb' ln)) ->
    (exists ln nb', noleftrec g p nb' ln /\ onb = orb nb nb') /\
    (forall n nb',
       nth n lr' Visiting = Visited nb' ->
          (exists ln, noleftrec g (PNT n) nb' ln)).
Proof.
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
    [H: exists _, _ /\ _ |- _] => 
      destruct H as [? [? ?]] end;
    subst; simplOrb; subst;
    eauto using noleftrec;
     try (eexists; eexists; split; eauto using noleftrec;
     simplOrb; try (rewrite Bool.orb_assoc); trivial; fail).
  - match goal with
    [H: forall _ _, _ = _ -> ?e -> _ |- _] =>
      specialize (H _ _ eq_refl); assert(HH: e) end.
    { intros * H1.
      destruct (Nat.eq_dec n i); subst.
      - exfalso. erewrite update_eq in H1; try discriminate.
        eapply nth_overflow'; eauto. congruence.
      - erewrite update_neq in H1; eauto. }
    specialize (IHHVR HH) as [[? [? [? ?]]] ?].
    eexists; eexists; split; eauto using noleftrec.
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
      destruct HH as [[? [? [? ?]]] ?].
      replace nb'0 with nb' in *.
      * simplOrb; subst.
        eexists. econstructor.
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
  - eapply H2 in H. destruct H as [? ?].
    eexists; eexists. split; eauto. 
Qed.


        
