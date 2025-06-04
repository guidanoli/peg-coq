From Coq Require Import Arith.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.
From Coq Require Import Classes.EquivDec.

From Peg Require Import Syntax.
From Peg Require Import Ncode.
From Peg Require Import NMatch.
From Peg Require Import NVerifyrule.
From Peg Require Import VRcomp.
From Peg Require Import NLR.


Lemma verifygrammar_comp_S:
    forall g lr n lr'',
    verifygrammar_comp (S n) g lr = Some lr'' ->
    exists lr' nb,
      verifygrammar_comp n g lr = Some lr' /\
      verifyrule_comp (costG g lr' + costP (PNT n)) g (PNT n) lr' false =
        Some (Some (nb, lr'')).
Proof.
  intros * HVG.
  simpl in HVG.
  destruct (verifygrammar_comp n g lr) eqn:?; try (simpl; congruence).
  destruct (verifyrule_comp (costG g l + 1) g (PNT n) l false) eqn:?.
  - destruct r; try discriminate.
    destruct p.
    injection HVG; intros; subst; clear HVG.
    eexists; eexists; eauto.
  - exfalso.
    replace 1 with (costP (PNT n)) in Heqo0 by trivial.
    eapply VR_comp; eauto.
Qed.


Definition GrammarComplete g :=
  forall (n : nat),
    exists (nb : bool) (ln : list nat), noleftrec g (PNT n) nb ln.


Lemma vgcomp_ind: forall n g lr lr',
    verifygrammar_comp n g lr = Some lr' ->
    LRCoher g lr ->
    (forall i, i < n -> nth i lr Visiting = NotVisited) ->
    LRCoher g lr' /\
    (forall i, i < n -> exists nb, nth i lr' Visiting = Visited nb).
Proof.
  induction n; intros * HVG HLR HL1.
  - simpl in HVG. injection HVG; intros; subst. intuition; lia.
  - apply verifygrammar_comp_S in HVG.
    destruct HVG as [lrG [? [? ?]]].
    apply verifyrule_comp_sound in H0.
    specialize (IHn _ _ _ H HLR) as [? ?].
    + intros i Hlt. apply HL1. lia.
    + specialize (NLRpreservation H0 H1) as HN.
      destruct HN as [[? [? [? ?]]] ?].
      simplOrb; subst.
      split; trivial.
      intros i Hlt.
      assert (Hlt1: i <= n) by lia. clear Hlt.
      apply Lt.le_lt_or_eq_stt in Hlt1.
      destruct Hlt1.
      * apply H2 in H4. destruct H4 as [x ?].
        exists x. eapply vrinc; eauto. subst; congruence.
      * subst; eauto using VRAdd1.
Qed.


Lemma LRCoherRep : forall g,
    LRCoher g (repeat NotVisited (length g)).
Proof.
  unfold LRCoher.
  intros * Heq. exfalso.
  specialize (Nat.lt_ge_cases n (length g)) as [? | ?].
  - rewrite nth_indep with (d' := NotVisited) in Heq.
    + rewrite nth_repeat in Heq. discriminate.
    + rewrite repeat_length. trivial.
  - rewrite nth_overflow in Heq; try discriminate.
    rewrite repeat_length. trivial.
Qed.


Lemma nth_repeat_init: forall n,
  forall i : nat,
      i < n -> nth i (repeat NotVisited n) Visiting = NotVisited.
Proof.
  intros * Hlt.
  rewrite nth_indep with (d' := NotVisited).
  * rewrite nth_repeat. trivial.
  * rewrite repeat_length. trivial.
Qed.


Theorem VGcorrect: forall g lr,
  VG g = Some lr -> GrammarComplete g.
Proof.
  unfold VG.
  intros * HVG.
  apply vgcomp_ind in HVG; destruct HVG;
  auto using LRCoherRep, nth_repeat_init.
  unfold GrammarComplete. intros.
  specialize (Nat.lt_ge_cases n (length g)) as [? | ?].
  - apply H0 in H1. destruct H1. eauto.
  - eexists; eexists; eauto using nth_overflow, noleftrec.
Qed.


Theorem VGcomplete: forall g lr p,
  VG g = Some lr ->
  exists nb ln, noleftrec g p nb ln.
Proof.
  intros * HVG.
  apply VGcorrect in HVG.
  induction p; try breakEx;
  try (eexists; eexists; eauto using noleftrec; fail).
  - destruct x1; eauto using noleftrec.
  - specialize (HVG n); breakEx; eauto.
Qed.


Theorem VGcorrect_nonull: forall g lr',
  VG g = Some lr' ->
  (forall i, nth i lr' Visiting = Visited false -> not_nullable g (PNT i)).
Proof.
  unfold VG.
  intros * HVG.
  apply vgcomp_ind in HVG; destruct HVG as [H1 ?];
  auto using LRCoherRep, nth_repeat_init.
  unfold LRCoher in *.
  intros * HVis.
  apply H1 in HVis. destruct HVis.
  eauto using nlr_nullable.
Qed.


