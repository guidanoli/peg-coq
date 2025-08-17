From Coq Require Import Arith.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.
From Coq Require Import Classes.EquivDec.

From Peg Require Import Syntax.
From Peg Require Import Ncode.
From Peg Require Import NMatch.
From Peg Require Import NVerifyrule.



Ltac destVR :=
  match goal with
  | [H: context [verifyrule_comp ?gas ?g ?p1 ?lr ?nb] |- _]
        => destruct (verifyrule_comp gas g p1 lr nb) as [[[? ?] | ] | ] eqn:Heq
  | [|- context [verifyrule_comp ?gas ?g ?p1 ?lr ?nb]]
        => destruct (verifyrule_comp gas g p1 lr nb) as [[[? ?] | ] | ] eqn:Heq
  end.


Ltac breakEx :=
  repeat match goal with
  [H: exists _, _ |- _] => destruct H as [? ?]
  end.


Lemma costP1 : forall p, 0 < costP p.
Proof. induction p; simpl; lia. Qed.


Lemma CostUpdateVIsitingP : forall lr g n,
    nth n lr Visiting = NotVisited ->
    costP (nth n g PEmpty) + costG g (update lr n Visiting) <= costG g lr.
Proof.
  induction lr; intros * Hn.
  - simpl in Hn. destruct n; discriminate.
  - simpl. destruct n; destruct a; destruct g; simpl; try lia;
     try discriminate; simpl in Hn;
     try (apply IHlr with (g := g) in Hn; simpl in Hn; lia);
     try (apply IHlr with (g := nil) in Hn; destruct n; simpl in Hn; lia).
Qed.


Lemma costUpdateVisited : forall lr g i nb,
  costG g (update lr i (Visited nb)) <= costG g lr.
Proof.
  induction lr; intros *.
  - simpl. destruct i; trivial.
  - destruct g.
    + simpl. destruct i; simpl.
      * simpl. destruct a; lia.
      * simpl. destruct a; specialize (IHlr nil i nb) as ?; lia.
    + simpl. destruct i; simpl; destruct a; try lia;
      specialize (IHlr g i nb) as ?; lia.
Qed.


Lemma costUpdateVisiting : forall lr g i,
  costG g (update lr i Visiting) <= costG g lr.
Proof.
  induction lr; intros *.
  - simpl. destruct i; trivial.
  - destruct g.
    + simpl. destruct i; simpl.
      * simpl. destruct a; lia.
      * simpl. destruct a; specialize (IHlr nil i) as ?; lia.
    + simpl. destruct i; simpl; destruct a; try lia;
      specialize (IHlr g i) as ?; lia.
Qed.


Lemma dimCost : forall gas g p lr lr' nb nb',
    verifyrule_comp gas g p lr nb = Some (Some (nb', lr')) ->
    costG g lr' <= costG g lr.
Proof.
  induction gas; intros * HVr; try discriminate.
  destruct p; simpl in HVr; simplsome; trivial;
    repeat match goal with
    [H : verifyrule_comp _ _ _ _ _ = Some _ |- _] =>
       eapply IHgas in H
    end; try lia.
  - destVR; try congruence.
    destruct b.
    + eapply IHgas in Heq.
      eapply IHgas in HVr.
      lia.
    + simplsome.
      eapply IHgas in Heq.
      trivial.
  - destVR; try congruence.
    eapply IHgas in Heq.
    eapply IHgas in HVr.
    lia.
  - destruct (nth n lr Visiting); try congruence.
    + destVR; try congruence.
      simplsome.
      apply IHgas in Heq; clear IHgas.
      specialize (costUpdateVisited l g n b) as ?.
      specialize (costUpdateVisiting lr g n) as ?.
      lia.
    + simplsome. trivial.
Qed.


Lemma VR_comp : forall gas g p lr nb,
    (costG g lr + costP p) <= gas ->
    verifyrule_comp gas g p lr nb <> None.
Proof.
  induction gas; intros * Hle.
  - specialize (costP1 p). lia.
  - destruct p.
    + simpl. congruence.
    + simpl. congruence.
    + simpl in Hle; simpl.
      destVR; try congruence.
      destruct b; try congruence.
      * eapply IHgas.
        eapply dimCost in Heq. lia.
      * exfalso. eapply IHgas; eauto. lia.
    + simpl in Hle; simpl.
      destVR; try congruence.
      * eapply IHgas.
        apply dimCost in Heq. lia.
      * exfalso. eapply IHgas; eauto. lia.
    + apply IHgas. simpl in Hle. lia.
    + apply IHgas. simpl in Hle. lia.
    + apply IHgas. simpl in Hle. lia.
    + simpl in Hle; simpl.
      destruct (nth n lr Visiting) eqn:?; try congruence.
      destVR; try congruence.
      exfalso.
      eapply IHgas; eauto.
      specialize (CostUpdateVIsitingP lr g n Heqr) as ?.
      lia.
Qed.



