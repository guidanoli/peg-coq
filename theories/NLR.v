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


Inductive noleftrec : grammar -> pat -> bool -> list nat -> Prop :=
  | NLREmpty :
      forall g,
      noleftrec g PEmpty true []
  | NLRSet :
      forall g cs,
      noleftrec g (PSet cs) false []
  | NLRSequenceSomeTrue :
      forall g p1 p2 ln ln' nb,
      noleftrec g p1 true ln ->
      noleftrec g p2 nb ln' ->
      noleftrec g (PSequence p1 p2) nb (ln ++ ln')
  | NLRSequenceSomeFalse :
      forall g p1 p2 ln,
      noleftrec g p1 false ln ->
      noleftrec g (PSequence p1 p2) false ln
  | NLRChoice :
      forall g p1 p2 ln ln' nb nb',
      noleftrec g p1 nb ln ->
      noleftrec g p2 nb' ln' ->
      noleftrec g (PChoice p1 p2) (orb nb nb') (ln ++ ln')
  | NLRRepetition :
      forall g p ln nb,
      noleftrec g p nb ln ->
      noleftrec g (PRepetition p) true ln 
  | NLRNot :
      forall g p ln nb,
      noleftrec g p nb ln ->
      noleftrec g (PNot p) true ln
  | NLRAnd :
      forall g p ln nb,
      noleftrec g p nb ln ->
      noleftrec g (PAnd p) true ln
  | NLRNT :
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


Definition LRCoher (g : grammar) lr :=
  forall n nb, nth n lr Visiting = Visited nb ->
      exists ln, noleftrec g (PNT n) nb ln.


Theorem NLRpreservation : forall g p lr nb onb lr',
    verifyrule g p lr nb (Some (onb, lr')) ->
    LRCoher g lr ->
    (exists ln nb', noleftrec g p nb' ln /\ onb = orb nb nb') /\ LRCoher g lr'.
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
      replace nb0 with nb' in *.
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


Corollary LRCoherPres : forall g p lr nb nb' lr',
    verifyrule g p lr nb (Some (nb', lr')) ->
    LRCoher g lr ->
    LRCoher g lr'.
Proof.
  intros * HVR HLR.
  apply NLRpreservation in HVR; intuition eauto.
Qed.


Lemma LRCoherUpdate: forall g lr i,
    LRCoher g lr ->
    LRCoher g (update lr i Visiting).
Proof.
  unfold LRCoher; intros * H * Hnth.
  apply H. destruct (Nat.eq_dec n i); subst.
  - exfalso.
    specialize (update_eq2 lr i Visiting Visiting) as [? | ?];
      congruence.
  - rewrite update_neq in Hnth; auto.
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


Lemma nlr_nullable : forall g p ln,
   noleftrec g p false ln -> not_nullable g p.
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


Lemma In1 : forall lr ln ln',
    (forall i, nth i lr Visiting = Visiting -> ~ In i (ln ++ ln')) ->
    (forall i, nth i lr Visiting = Visiting -> ~ In i ln).
Proof.
  intros * HVis i HVis1 HIn.
  eapply HVis; eauto using in_or_app.
Qed.


Lemma In2 : forall lr ln ln',
    (forall i, nth i lr Visiting = Visiting -> ~ In i (ln ++ ln')) ->
    (forall i, nth i lr Visiting = Visiting -> ~ In i ln').
Proof.
  intros * HVis i HVis1 HIn.
  eapply HVis; eauto using in_or_app.
Qed.


Lemma NLR_VR: forall g p nb ln lr,
  noleftrec g p nb ln ->
  LRCoher g lr ->
  (forall i, nth i lr Visiting = Visiting -> ~In i ln) ->
  exists lr', verifyrule g p lr false (Some (nb, lr')).
Proof.
  intros * HNL.
  generalize dependent lr.
  induction HNL; intros * HLR HVis;
    eauto using verifyrule;
    try (eapply IHHNL in HVis; trivial; destruct HVis as [? ?];
         eauto using verifyrule, nb_false; fail).
  - specialize (In1 _ _ _ HVis) as H1.
    specialize (In2 _ _ _ HVis) as H2.
    apply IHHNL1 in H1; trivial. destruct H1 as [? ?]. clear IHHNL1.
    specialize (IHHNL2 x).
    assert (forall i : nat, nth i x Visiting = Visiting -> ~ In i ln').
    { intros * HVis1. eapply H2. eapply vrPvisiting; eauto. }
    apply IHHNL2 in H0; eauto using LRCoherPres.
    destruct H0 as [? ?]. clear IHHNL2.
    eauto using verifyrule.
  - specialize (In1 _ _ _ HVis) as H1.
    specialize (In2 _ _ _ HVis) as H2.
    apply IHHNL1 in H1; trivial. destruct H1 as [? ?]. clear IHHNL1.
    specialize (IHHNL2 x).
    assert (forall i : nat, nth i x Visiting = Visiting -> ~ In i ln').
    { intros * HVis1. eapply H2. eapply vrPvisiting; eauto. }
    apply IHHNL2 in H0; eauto using LRCoherPres.
    destruct H0 as [? ?]. clear IHHNL2.
    exists x0. eapply VRChoiceSome; eauto.
    rewrite Bool.orb_comm.
    apply nb_nb. auto.
  - destruct (nth i lr Visiting) eqn:?.
    + assert (HH: forall i0 : nat,
         nth i0 (update lr i Visiting) Visiting = Visiting -> ~ In i0 ln).
      { intros n HVis1.
        destruct (Nat.eq_dec n i); subst.
        - eauto using NLRNoLoops.
        - rewrite update_neq in HVis1; trivial.
          apply HVis in HVis1. eauto using in_cons. }
       apply IHHNL in HH; eauto using LRCoherUpdate.
       destruct HH as [? ?]. 
       eapply VRNTNotvisitedSome with (nb := false) in H0; eauto.
    + exfalso. apply HVis in Heqr. simpl in Heqr. intuition.
    + replace nb with (false || nb)%bool by auto using Bool.orb_false_l.
      eexists. eapply VRNTVisited.
      replace nb with b; trivial.
      apply HLR in Heqr. destruct Heqr as [? ?].
      inversion H0; subst.
      eapply NLRunique; eauto.
Qed.


