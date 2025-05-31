From Coq Require Import Arith.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.
From Coq Require Import Classes.EquivDec.

From Peg Require Import Syntax.
From Peg Require Import NMatch.
From Peg Require Import NVerifyrule.
From Peg Require Import VRcomp.
From Peg Require Import NLR.


Fixpoint verifygrammar_comp n
    (g : grammar) (lr : list RuleStatus) : option (list RuleStatus) :=
  match n with
  | 0 => Some lr
  | S n' => match verifygrammar_comp n' g lr with
            | None => None
            | Some lr' =>
                match verifyrule_comp (costG g lr' + costP (PNT n'))
                                      g (PNT n') lr' false with
                | None => Some lr'   (* cannot happen *)
                | Some None => None
                | Some (Some (nb, lr'')) => Some lr''
                end
            end
  end.


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


Theorem VGcorrect: forall g lr',
  verifygrammar_comp (length g) g
    (repeat NotVisited (length g)) = Some lr' ->
  GrammarComplete g.
Proof.
  intros * HVG.
  apply vgcomp_ind in HVG; destruct HVG.
  - unfold GrammarComplete. intros.
    specialize (Nat.lt_ge_cases n (length g)) as [? | ?].
    + apply H0 in H1. destruct H1. eauto.
    + eexists; eexists; eauto using nth_overflow, noleftrec.
  - unfold LRCoher.
    intros * Heq. exfalso.
    specialize (Nat.lt_ge_cases n (length g)) as [? | ?].
    + rewrite nth_indep with (d' := NotVisited) in Heq.
      * rewrite nth_repeat in Heq. discriminate.
      * rewrite repeat_length. trivial.
    + rewrite nth_overflow in Heq; try discriminate.
      rewrite repeat_length. trivial.
  - intros * Hlt.
    rewrite nth_indep with (d' := NotVisited).
    * rewrite nth_repeat. trivial.
    * rewrite repeat_length. trivial.
Qed.

