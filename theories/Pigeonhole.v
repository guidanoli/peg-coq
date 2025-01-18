(* Author: Roberto Ierusalimschy *)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.


Ltac solvein := intuition auto using in_eq, in_or_app, in_cons.


Fixpoint count (l : list nat) (x : nat) : nat :=
  match l with
  | [] => 0
  | h :: l' => if Nat.eq_dec h x then S (count l' x) else count l' x
  end.


Ltac destdec := repeat (simpl;
  try match goal with
  | [ |- context [Nat.eq_dec ?A ?B]  ] =>
    destruct (Nat.eq_dec A B); subst
  | [H: context [Nat.eq_dec ?A ?B] |- _] =>
    destruct (Nat.eq_dec A B); subst
  | [H: ?X <> ?X |- _ ] => exfalso; apply H
  end; auto).


Lemma c_h_eq: forall l (x : nat), count (x :: l) x = S (count l x).
Proof. induction l; intros *; destdec. Qed.


Lemma c_h_Neq: forall l (x y : nat),
  x <> y -> count (y :: l) x = count l x.
Proof. induction l; intros * H; destdec. Qed.


Lemma c_app: forall l1 l2 (x : nat),
    count (l1 ++ l2) x = count l1 x + count l2 x.
Proof. induction l1; intros *; destdec. Qed.


Lemma c_tail: forall x y l n,
    n <= count l x ->
    n <= count (y :: l) x.
Proof. intros *. destdec. Qed.


Lemma In_Neq: forall l (a x: nat), In x (a :: l) -> a <> x -> In x l.
Proof. intros * HIn HNeq. destruct HIn; trivial. contradiction. Qed.


Lemma In_count: forall (x : nat) l, In x l -> 0 < count l x.
Proof.
  induction l; intros * H.
  - contradiction.
  - destdec.
    + lia.
    + eauto using In_Neq.
 Qed.


Lemma CP_In_count: forall (x : nat) l, count l x = 0 -> ~In x l.
Proof.
  intros * H contra.
  apply In_count in contra.
  rewrite H in contra.
  inversion contra.
Qed.


Lemma count_In: forall (x : nat) l, 0 < count l x -> In x l.
Proof.
  induction l; simpl; intros * H.
  - lia.
  - destdec.
Qed.


Lemma InDec: forall (n : nat) l, {In n l} + {~In n l}.
Proof.
  induction l; solvein.
  destruct (Nat.eq_dec a n); subst; simpl; solvein.
Qed.


Lemma l_break: forall l (a : nat) n,
    count l a = S n ->
    exists l1 l2, l = l1 ++ a :: l2 /\ count l1 a = 0 /\ count l2 a = n.
Proof.
  induction l; intros * HIn; try discriminate.
  destruct (Nat.eq_dec a0 a); subst; simpl.
  - exists [], l. repeat split; trivial.
    simpl. rewrite c_h_eq in HIn. injection HIn; trivial.
  - rewrite c_h_Neq in HIn; trivial.
    specialize (IHl _ _ HIn) as [l1 [l2 [? [? ?]]]].
    subst.
    exists (a :: l1), l2. repeat split; trivial.
    rewrite c_h_Neq; trivial.
Qed.


Lemma l_break2: forall l (a : nat) n,
    count l a = S (S n) ->
    exists l1 l2 l3,
       l = l1 ++ (a :: l2) ++ (a :: l3) /\ count l1 a = 0 /\
              count l2 a = 0 /\ count l3 a = n.
Proof.
  intros * HC.
  apply l_break in HC.
  destruct HC as [l1 [l2' [Hl [HC1 HC2]]]].
  apply l_break in HC2.
  destruct HC2 as [l2 [l3 [Hl' [? ?]]]].
  exists l1, l2, l3. subst. repeat split; trivial.
Qed.


Lemma list1: forall (l : list nat), length l = 1 -> exists x, l = [x].
Proof.
  destruct l; simpl; try discriminate.
  destruct l; simpl; try discriminate.
  intros _. eauto.
Qed.


Lemma count_h_12: forall a b c l1 l2,
    count (l1 ++ a :: l2) b <= count (a :: l1 ++ c :: l2) b.
Proof.
  intros *. simpl. repeat rewrite c_app. simpl.
  destdec; lia.
Qed.


Lemma PredPred: forall a b, a < S b -> a <> b -> a < b.
Proof. lia. Qed.


Lemma forall_tail: forall a l N,
    (forall x : nat, In x (a :: l) -> x < S (S N)) ->
    ~In (S N) l ->
    (forall x : nat, In x l -> x < S N).
Proof.
  intros * HF HNIn x HIn.
  apply PredPred; try solvein.
  subst. eauto.
Qed.


Lemma S_m_1: forall n, S n - 1 = n. lia. Qed.

Lemma N01n: forall n, n = 0 \/ n = 1 \/ n >= 2.
Proof. lia. Qed.


Lemma InST1: forall a l,
    (forall x : nat, In x l -> x < 1) -> In a l -> 0 = a.
Proof. intros * HF HIn. specialize (HF a). apply HF in HIn. lia. Qed.


Ltac InS0 x :=
  replace x with 0 by
    (eapply InST1; try eassumption; solvein).


(*
** pigeonhole principle: N is the number of holes, numberered from 0 to N - 1;
** 'l' gives, for each pigeon, its hole.
*)
Lemma pombos_count : forall N (l : list nat),
  N < length l ->    (* more pigeons than holes? *)
  (forall x, In x l -> x < N) ->  (* all piegons in valid holes? *)
  exists A, 2 <= count l A.  (* there is a hole with at least 2 pigeons *)
Proof.
  induction N; intros * HLen HIn.
  - exfalso. destruct l.
    + apply Nat.lt_irrefl in HLen. trivial.
    + specialize (HIn n). apply (Nat.nlt_0_r n). apply HIn. solvein.
  - (* Three cases: hole N not used, used once, or used more than once *)
    specialize (N01n (count l N)) as [? | [? | ?]].
    + apply IHN; clear IHN; try lia.
      intros x HInX.
      apply PredPred; auto.
      apply CP_In_count in H.
      intros ?; subst. auto.
    + apply l_break in H.
      destruct H as [l1 [l2 [? [? ?]]]]; subst.
      assert (N < length (l1 ++ l2)).
      { clear IHN HIn.
        repeat rewrite app_length in *.
        simpl in *. lia. }
      assert (forall x : nat, In x (l1 ++ l2) -> x < N).
      { clear IHN HLen. intros x HInX.
        apply in_app_or in HInX.
        destruct HInX; apply PredPred; try (apply HIn; solvein).
        - intros contra; subst. apply CP_In_count in H0. contradiction.
        - intros contra; subst. apply CP_In_count in H1. contradiction.
      }
      specialize (IHN (l1 ++ l2) H H2) as [A ?].
      exists A.
      rewrite c_app in *.
      specialize (c_tail A N l2 (count l2 A)). lia.
   +  exists N. apply H.
Qed.


Theorem pigeonhole_principle : forall (l : list nat) n,
  length l > n ->
  (forall a, In a l -> a < n) ->
  exists A l1 l2 l3, l = l1 ++ A :: l2 ++ A :: l3.
Proof.
  intros * HL HF.
  specialize (pombos_count n l HL HF) as [A ?].
  assert (HEq: count l A = S (S (count l A - 2))) by lia.
  specialize (l_break2 l A (count l A - 2) HEq) as [l1 [l2 [l3 [? _]]]].
  exists A, l1, l2, l3.
  subst.
  trivial.
Qed.
