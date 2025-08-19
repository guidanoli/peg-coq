From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Arith.
From Peg Require Import Syntax.

From Peg Require Import Syntax.
From Peg Require Import NMatch.
From Peg Require Import Ncode.
From Peg Require Import Tactics.
From Peg Require Import NVerifyrule.
From Peg Require Import NVerifygrammar.

Import ListNotations.


Ltac destructCond :=
  match goal with
  [H: (match ?cond with | _ => _ end)  = _ |- _] =>
    destruct cond eqn:?; try discriminate
end.


Lemma nullable_correct : forall g lr p,
    VG g = Some lr ->
    nullable lr p = false ->
    not_nullable g p.
Proof.
  induction p; intros HVG HNull; try discriminate;
  simpl in HNull;
  repeat destructCond;
      eauto using not_null_set, not_null_seq2, not_null_seq1,
        not_null_choice, VGcorrect_nonull.
  - specialize (proj1 (Bool.andb_false_iff _ _) HNull) as [? | ?];
      eauto using not_null_set, not_null_seq2, not_null_seq1,
        not_null_choice, VGcorrect_nonull.
  - specialize (Bool.orb_false_elim _ _ HNull).
    intros [? ?].
      eauto using not_null_set, not_null_seq2, not_null_seq1,
        not_null_choice, VGcorrect_nonull.
Qed.


(** CheckLoops predicate **)
(** Check whether a pattern has potential infinite loops **)

Inductive Pnoloops : list RuleStatus -> pat -> Prop :=
  | CLEmpty : forall lr, Pnoloops lr PEmpty
  | CLSet : forall lr cs, Pnoloops lr (PSet cs)
  | CLSequence : forall lr p1 p2,
      Pnoloops lr p1 ->
      Pnoloops lr p2 ->
      Pnoloops lr (PSequence p1 p2)
  | CLChoice : forall lr p1 p2,
      Pnoloops lr p1 ->
      Pnoloops lr p2 ->
      Pnoloops lr (PChoice p1 p2)
  | CLRepetition : forall lr p,
      nullable lr p = false ->
      Pnoloops lr p ->
      Pnoloops lr (PRepetition p)
  | CLNot : forall lr p,
      Pnoloops lr p ->
      Pnoloops lr (PNot p)
  | CLAnd : forall lr p,
      Pnoloops lr p ->
      Pnoloops lr (PAnd p)
  | CLNT : forall lr i,
      Pnoloops lr (PNT i)
  .



Lemma noloops_necessary :
  forall lr p,
  Pnoloops lr p ->
  noloops lr p = true.
Proof.
  induction 1; trivial; simpl;
    specialize (Bool.andb_true_l true); try congruence.
  rewrite H. trivial.
Qed.


Lemma noloops_sufficient :
  forall lr p,
  noloops lr p = true ->
  Pnoloops lr p.
Proof.
  induction p; intros Hnl; simpl in Hnl;
    try apply andb_prop in Hnl; intuition (auto using Pnoloops).
  destructCond.
  auto using Pnoloops.
Qed.


Lemma Gnoloops_complete_aux : forall n lr g,
  Gnoloops n lr g = true ->
  forall i, i < n -> Pnoloops lr (nth i g PEmpty).
Proof.
  induction n; intros * HGnl i Hlt; try lia.
  simpl in HGnl.
  destructCond.
  assert (Hlt1: i <= n) by lia. clear Hlt.
  specialize (Lt.le_lt_or_eq_stt _ _ Hlt1) as [? | ?]; subst;
    auto using noloops_sufficient.
Qed.

  
Lemma Gnoloops_complete : forall lr g,
  Gnoloops (length g) lr g = true ->
  forall n, Pnoloops lr (nth n g PEmpty).
Proof.
  intros * H n.
  specialize (Gnoloops_complete_aux _ _ _ H) as ?.
  specialize (Nat.lt_ge_cases n (length g)) as [? | ?]; auto.
  apply nth_overflow with (d := PEmpty) in H1.
  rewrite H1. auto using Pnoloops.
Qed.


Lemma well_formed_correct_aux : forall g lr,
  well_formed g  = Some lr ->
  forall N s p,
  String.length s < N ->
  Pnoloops lr p ->
  exists res, matches g p s res.
Proof with eauto using matches.
  intros * HWF.
  unfold well_formed in HWF.
  repeat destructCond.
  injection HWF; intro; subst; clear HWF.
  specialize (Gnoloops_complete _ _ Heqb) as ?.
  induction N; intros * Hlen; simpl in Hlen; try lia.
  generalize dependent s.
  specialize (VGcomplete _ _ p Heqr) as ?.
  breakEx.
  induction H0; intros * HSlen HNL; inversion HNL; subst...
  - destruct s...
    destruct (cs a) eqn:?...
  - specialize (IHnoleftrec1 Heqb Heqr H IHN _ HSlen H3).
    breakEx.
    destruct x...
    specialize (match_len _ _ _ _ H0) as ?.
    assert (HLen: String.length s0 < S N) by lia.
    specialize (IHnoleftrec2 Heqb Heqr H IHN _ HLen H4).
    breakEx...
  - specialize (IHnoleftrec Heqb Heqr H IHN _ HSlen H4).
    breakEx.
    destruct x...
    assert (String.length s0 < N) as Hlen0.
    { eapply NLR.nlr_nullable in H0.
      eapply (proj1 (notnull_len g p1)) in H1; eauto; try lia. }
    specialize (IHN s0 p2 Hlen0 H5).
    breakEx...
  - specialize (IHnoleftrec1 Heqb Heqr H IHN _ HSlen H3).
    breakEx.
    destruct x...
    specialize (IHnoleftrec2 Heqb Heqr H IHN _ HSlen H4).
    breakEx...
  - specialize (IHnoleftrec Heqb Heqr H IHN _ HSlen H4).
    breakEx.
    destruct x...
    assert (String.length s0 < N) as Hlen0.
    { eapply nullable_correct in H2; eauto.
      eapply (proj1 (notnull_len g p)) in H2; eauto; try lia. }
    specialize (IHN s0 _ Hlen0 HNL).
    breakEx...
  - specialize (IHnoleftrec Heqb Heqr H IHN _ HSlen H3).
    breakEx.
    destruct x...
  - specialize (IHnoleftrec Heqb Heqr H IHN _ HSlen H3).
    breakEx.
    destruct x...
  - assert (HNLnth: Pnoloops lr (nth i g PEmpty)) by eauto.
    specialize (IHnoleftrec Heqb Heqr H IHN _ HSlen HNLnth).
    breakEx...
Qed.


Corollary well_formed_correct : forall g lr,
  well_formed g  = Some lr ->
  forall s,
    exists res, matches g (nth 0 g PEmpty) s res.
Proof.
  intros * HWF s.
  eapply well_formed_correct_aux; eauto.
  unfold well_formed in HWF.
  repeat destructCond.
  injection HWF; intro; subst; clear HWF.
  eauto using Gnoloops_complete.
Qed.
  

