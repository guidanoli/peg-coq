From Coq Require Import Arith.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.
From Coq Require Import Classes.EquivDec.

From Peg Require Import Syntax.
From Peg Require Import NMatch.
From Peg Require Import Ncode.

Require Extraction.


Ltac simplsome :=
  subst; repeat match goal with
  | [H: Some ?x = Some ?x |- _] => clear H
  | [H: Some _ = Some _ |- _] => injection H; intros; subst; clear H
  end; try discriminate.


Lemma nth_ndef: forall {T} (l: list T) n a def def',
    nth n l def = a ->
    a <> def ->
    nth n l def' = a.
Proof.
  intros * Heq Hneq.
  erewrite nth_indep; eauto.
  destruct (le_lt_dec (length l) n); trivial.
  eapply nth_overflow with (d := def) in l0.
  congruence.
Qed.


Lemma update_eq : forall {T} (l : list T) i a b,
    i < length l -> nth i (update l i a) b = a.
Proof.
  induction l; intros * Hlen.
  - simpl in *. lia.
  - induction i; trivial.
    simpl in *. apply IHl. lia.
Qed.


Lemma update_len: forall {T} (l : list T) idx val,
  length (update l idx val) = length l.
Proof.
  induction l; intros *; destruct idx; simpl; congruence.
Qed.


Lemma update_eq2 : forall {T} (l : list T) i a b,
  nth i (update l i a) b = a \/ nth i (update l i a) b = b.
Proof.
  intros *.
  destruct (le_lt_dec (length l) i).
  - right. apply nth_overflow. rewrite update_len. trivial.
  - left. auto using update_eq.
Qed.


Lemma nth_overflow':
  forall [A : Type] (l : list A) [n : nat] (a d : A),
  nth n l d = a -> a <> d -> n < length l.
Proof.
  intros * Hnth Hneq. destruct (le_lt_dec (length l) n); trivial.
  exfalso; apply Hneq. apply nth_overflow with (d := d) in l0.
  congruence.
Qed.


Lemma update_neq : forall {T} (l : list T) i n a b,
    i <> n -> nth i (update l n a) b = nth i l b.
Proof.
  induction l; intros * Hne.
  - simpl. destruct i; destruct n; simpl; trivial.
  - simpl. destruct i; destruct n; trivial.
    + exfalso. apply Hne. trivial.
    + simpl. apply IHl. lia.
Qed.


Lemma nth_nth_error: forall {T} n (l : list T) def res,
    nth n l def = res ->
    def <> res ->
    nth_error l n = Some res.
Proof.
  intros * Hnt Hneq.
  destruct (le_lt_dec (length l) n).
  - exfalso. eapply nth_overflow with (d := def) in l0. congruence.
  - rewrite nth_error_nth' with (d := def); auto; congruence.
Qed.


Inductive leRS : RuleStatus -> RuleStatus -> Prop :=
| LERRef : forall x, leRS x x
| LERNV : forall nb, leRS NotVisited (Visited nb).


Definition leLR (lr lr' : list RuleStatus) : Prop :=
    forall n, leRS (nth n lr Visiting) (nth n lr' Visiting).


Lemma leLRRef : forall lr, leLR lr lr.
Proof. intros lr n. auto using leRS. Qed.


Lemma leRSTrans : forall r r' r'',
    leRS r r' -> leRS r' r'' -> leRS r r''.
Proof.
  intros * H1 H2.
  destruct H1 eqn:?.
  - trivial.
  - inversion H2; subst. eauto using leRS.
 Qed.


Lemma leLRTrans : forall lr lr' lr'',
    leLR lr lr' -> leLR lr' lr'' -> leLR lr lr''.
Proof. intros * H1 H2 n. eauto using leRSTrans. Qed.


Definition dec_Rule : forall (r1 r2 : RuleStatus), {r1 = r2} + {r1 <> r2}.
Proof. repeat decide equality. Qed.


Fixpoint count_notvisited (l : list RuleStatus) : nat :=
  match l with
  | nil => 0
  | (NotVisited :: tl) => S (count_notvisited tl)
  | (_ :: tl) => count_notvisited tl
  end.


Lemma countlelen : forall l, count_notvisited l <= length l.
Proof.
  induction l; trivial.
  destruct a; simpl; lia.
Qed.


Lemma updateVisited: forall lr n nb,
  count_notvisited (update lr n (Visited nb)) <= count_notvisited lr.
Proof.
  induction lr; intros *.
  - destruct n; simpl; trivial.
  - destruct n; simpl; try specialize (IHlr n nb);
      destruct a; try lia.
Qed.

Lemma updateVisiting: forall lr n,
  nth n lr Visiting = NotVisited ->
  count_notvisited (update lr n Visiting) < count_notvisited lr.
Proof.
  induction lr; intros *.
  - destruct n; simpl; discriminate.
  - destruct n; simpl.
    + intros H; subst; lia.
    + intros H. specialize (IHlr _ H).
      destruct a; lia.
Qed.


Ltac simplOrb :=
    repeat rewrite Bool.orb_false_r;
    repeat rewrite Bool.orb_true_r;
    repeat rewrite Bool.orb_true_l;
    repeat rewrite Bool.orb_false_l.

Ltac breakEx :=
  repeat match goal with
  [H: exists _, _ |- _] => destruct H as [? ?]
  end.


Definition not_nullable g p := forall s, ~matches g p s (Success s).


Lemma match_len : forall g p,
  forall s s', matches g p s (Success s') -> String.length s' <= String.length s.
Proof.
  intros * Hm. eauto using Suffix.suffix_length_le, matches_suffix. Qed.


Lemma notnull_len : forall g p,
  not_nullable g p <->
  forall s s', matches g p s (Success s') -> String.length s' < String.length s.
Proof.
  intros *; split; intros H.
  - intros * Hm.
    specialize (matches_suffix _ _ _ _  Hm) as HL.
    specialize (Suffix.suffix_length_le _ _ HL) as HS.
    apply Lt.le_lt_or_eq_stt in HS.
    destruct HS; trivial.
    exfalso.
    replace s with s' in * by eauto using Suffix.suffix_length_eq.
    eapply H. eauto.
  - intros s HM.
    apply H in HM. lia.
Qed.


Definition stateCorrect g lr :=
  forall n, nth n lr Visiting = Visited false ->
            not_nullable g (PNT n).


Lemma stcorrupdate : forall g lr i,
    stateCorrect g lr -> stateCorrect g (update lr i Visiting).
Proof.
  unfold stateCorrect.
  intros * H n Hn.
  destruct (Nat.eq_dec n i); subst; apply H.
  - destruct (update_eq2 lr i Visiting Visiting); congruence.
  - rewrite update_neq in Hn; trivial.
Qed.


Lemma not_null_set : forall g set, not_nullable g (PSet set).
Proof.
  intros *.
  apply notnull_len.
  inversion 1; subst. simpl. lia.
Qed.


Lemma not_null_seq1 : forall g p1 p2,
  not_nullable g p1 -> not_nullable g (PSequence p1 p2).
Proof.
  intros * H.
  inversion 1; subst.
  apply match_len in H7; eauto.
  apply notnull_len in H4; eauto.
  lia.
Qed.


Lemma not_null_seq2 : forall g p1 p2,
  not_nullable g p2 -> not_nullable g (PSequence p1 p2).
Proof.
  intros * H.
  inversion 1; subst.
  apply match_len in H4; eauto.
  apply notnull_len in H7; eauto.
  lia.
Qed.


Lemma not_null_choice : forall g p1 p2,
  not_nullable g p1 ->
  not_nullable g p2 ->
  not_nullable g (PChoice p1 p2).
Proof.
  intros * H1 H2.
  inversion 1; subst.
  - apply H1 in H6. trivial.
  - apply H2 in H8. trivial.
Qed.


Ltac ff :=
  repeat match goal with
  [H: false = false -> _ |- _] => specialize (H eq_refl)
  end.

Ltac appHI :=
match goal with
    [IH: stateCorrect ?g ?lr -> _,
     H: stateCorrect ?g ?lr |- _] =>
          eapply IH in H; eauto;
          destruct H as [[? | ?] ?]; clear IH
    end.



