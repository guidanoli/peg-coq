From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Lia.
From Coq Require Import Arith.PeanoNat.
From Peg Require Import Tactics.
From Peg Require Import Pattern.
From Peg Require Import Grammar.
From Peg Require Import Match.
From Peg Require Import Suffix.
From Peg Require Import Pigeonhole.
From Peg Require Import Coherent.
From Peg Require Import Strong.

Import ListNotations.

(** VerifyRule predicate **)
(** Checks whether a pattern is nullable (or not), or contains left recursion **)
(** The d parameter is the call stack (D)epth, used to escape left-recursive rules **)
(** The nb parameter is used for tail calls in choices (stands for (N)ulla(B)le) **)
(** The k parameter is the call stac(K) of rules **)
(** res = None -> has LR **)
(** res = Some true -> no LR, nullable **)
(** res = Some false -> no LR, not nullable **)

Inductive verifyrule :
  grammar -> pat -> nat -> bool -> option bool -> list nat -> Prop :=

  | VREmpty :
      forall g d nb,
      verifyrule g PEmpty d nb (Some true) nil
  | VRChar :
      forall g a d nb,
      verifyrule g (PChar a) d nb (Some nb) nil
  | VRSequenceNone :
      forall g p1 p2 d nb k,
      verifyrule g p1 d false None k ->
      verifyrule g (PSequence p1 p2) d nb None k
  | VRSequenceSomeTrue :
      forall g p1 p2 d nb res k1 k2,
      verifyrule g p1 d false (Some true) k1 ->
      verifyrule g p2 d nb res k2 ->
      verifyrule g (PSequence p1 p2) d nb res k2
  | VRSequenceSomeFalse :
      forall g p1 p2 d nb k,
      verifyrule g p1 d false (Some false) k ->
      verifyrule g (PSequence p1 p2) d nb (Some nb) k
  | VRChoiceNone :
      forall g p1 p2 d nb k,
      verifyrule g p1 d nb None k ->
      verifyrule g (PChoice p1 p2) d nb None k
  | VRChoiceSome :
      forall g p1 p2 d nb nb' res k1 k2,
      verifyrule g p1 d nb (Some nb') k1 ->
      verifyrule g p2 d nb' res k2 ->
      verifyrule g (PChoice p1 p2) d nb res k2
  | VRRepetition :
      forall g p d nb res k,
      verifyrule g p d true res k ->
      verifyrule g (PRepetition p) d nb res k
  | VRNot :
      forall g p d nb res k,
      verifyrule g p d true res k ->
      verifyrule g (PNot p) d nb res k
  | VRNTZero :
      forall g i nb,
      verifyrule g (PNT i) O nb None nil
  | VRNTSucc :
      forall g i p d nb res k,
      nth_error g i = Some p ->
      verifyrule g p d nb res k ->
      verifyrule g (PNT i) (S d) nb res (i :: k)
  .

Goal
  forall g nb d,
  verifyrule g PEmpty d nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g a nb d,
  verifyrule g (PChar a) d nb (Some nb) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb d,
  verifyrule g (PSequence PEmpty PEmpty) d nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb d a,
  verifyrule g (PSequence (PChar a) PEmpty) d nb (Some nb) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb d a,
  verifyrule g (PSequence PEmpty (PChar a)) d nb (Some nb) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PSequence (PNT 0) PEmpty) 0 nb None nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PSequence PEmpty (PNT 0)) 0 nb None nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule [PNT 1; PEmpty; g] (PSequence (PNT 0) PEmpty) 1 nb None [0].
Proof.
  intros.
  eapply VRSequenceNone; eauto using verifyrule.
  eapply VRNTSucc; eauto using verifyrule.
  simpl.
  eauto.
Qed.

Goal
  forall g nb,
  verifyrule [PNT 1; g] (PSequence PEmpty (PNT 0)) 1 nb None [0].
Proof.
  intros.
  eapply VRSequenceSomeTrue; eauto using verifyrule.
  eapply VRNTSucc; eauto using verifyrule.
  simpl.
  eauto.
Qed.

Goal
  forall g nb d,
  verifyrule g (PChoice PEmpty PEmpty) d nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb d a,
  verifyrule g (PChoice (PChar a) PEmpty) d nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb d a,
  verifyrule g (PChoice PEmpty (PChar a)) d nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb d a,
  verifyrule g (PChoice (PChar a) (PChar a)) d nb (Some nb) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PChoice (PNT 0) PEmpty) 0 nb None nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PChoice PEmpty (PNT 0)) 0 nb None nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule (PNT 1 :: g) (PChoice (PNT 0) PEmpty) 1 nb None [0].
Proof.
  intros.
  eapply VRChoiceNone; eauto using verifyrule.
  eapply VRNTSucc; eauto using verifyrule.
  simpl.
  eauto.
Qed.

Goal
  forall nb a,
  verifyrule
  [(PChar a); (PChar a)]
  (PChoice (PNT 0) (PNT 1)) 1 nb (Some nb) [1].
Proof.
  intros.
  eapply VRChoiceSome;
  eapply VRNTSucc; simpl; eauto using verifyrule.
Qed.

Goal
  forall nb a,
  verifyrule
  [PNT 7; (PChar a)]
  (PChoice (PNT 0) (PNT 1)) 1 nb None [0].
Proof.
  intros.
  eapply VRChoiceNone;
  eapply VRNTSucc; simpl; eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PRepetition PEmpty) 0 nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb a,
  verifyrule g (PRepetition (PChar a)) 0 nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PRepetition (PNT 0)) 0 nb None nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule (PNT 1 :: g) (PRepetition (PNT 0)) 1 nb None [0].
Proof.
  intros.
  eapply VRRepetition.
  eapply VRNTSucc; simpl; eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PNot PEmpty) 0 nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb a,
  verifyrule g (PNot (PChar a)) 0 nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PNot (PNT 0)) 0 nb None nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule (PNT 1 :: g) (PNot (PNT 0)) 1 nb None [0].
Proof.
  intros.
  eapply VRNot.
  eapply VRNTSucc; simpl; eauto using verifyrule.
Qed.

Goal
  forall d,
  verifyrule [PNT 0] (PNT 0) d false None (repeat 0 d).
Proof.
  intros.
  induction d.
  - (* O *)
    eauto using verifyrule.
  - (* S d *)
    simpl.
    eapply VRNTSucc; simpl; auto.
Qed.

Lemma verifyrule_determinism :
  forall g p d nb res1 res2 k1 k2,
  verifyrule g p d nb res1 k1 ->
  verifyrule g p d nb res2 k2 ->
  res1 = res2 /\ k1 = k2.
Proof.
  intros * H1 H2.
  generalize dependent k2.
  generalize dependent res2.
  induction H1; intros;
  inversion H2; subst;
  try destruct2sep;
  try lia;
  auto;
  try match goal with
  [ IHx: forall res k, verifyrule ?g ?p ?d ?nb res k -> _ = res /\ _ = k,
    Hx: verifyrule ?g ?p ?d ?nb _ _ |- _ ] =>
      apply IHx in Hx;
      destruct Hx;
      try discriminate;
      try destruct1;
      subst;
      auto
  end.
Qed.

Ltac pose_verifyrule_determinism :=
  repeat match goal with
    [ Hx1: verifyrule ?g ?p ?d ?nb ?res1 ?k1,
      Hx2: verifyrule ?g ?p ?d ?nb ?res2 ?k2 |- _ ] =>
          assert (res1 = res2 /\ k1 = k2)
          as [? ?]
          by eauto using verifyrule_determinism;
          clear Hx2
  end.

Lemma verifyrule_S_depth :
  forall g p d nb nb' k,
  verifyrule g p d nb (Some nb') k ->
  verifyrule g p (S d) nb (Some nb') k.
Proof.
  intros * H.
  remember (Some nb').
  generalize dependent nb'.
  induction H; intros;
  try discriminate;
  eauto using verifyrule.
Qed.

Lemma verifyrule_depth_le_some_determinism :
  forall g p d d' nb nb' k,
  verifyrule g p d nb (Some nb') k ->
  d <= d' ->
  verifyrule g p d' nb (Some nb') k.
Proof.
  intros * H Hle.
  induction Hle;
  eauto using verifyrule_S_depth.
Qed.

Lemma verifyrule_depth_some_determinism :
  forall g p d d' nb b b' k k',
  verifyrule g p d nb (Some b) k ->
  verifyrule g p d' nb (Some b') k' ->
  b = b' /\ k = k'.
Proof.
  intros * H H'.
  destruct (Compare_dec.le_ge_dec d d') as [Hle|Hge];
  try unfold ge in *;
  match goal with
    [ Hx: ?d <= ?d',
      Hy: verifyrule ?g ?p ?d ?nb (Some ?b) ?k,
      Hz: verifyrule ?g ?p ?d' ?nb (Some ?b') ?k' |- _ ] =>
          assert (verifyrule g p d' nb (Some b) k)
          by eauto using verifyrule_depth_le_some_determinism
  end;
  pose_verifyrule_determinism;
  subst;
  destruct1;
  auto.
Qed.

Ltac pose_verifyrule_some_determinism :=
  repeat match goal with
    [ Hx1: verifyrule ?g ?p ?d1 ?nb (Some ?b1) ?k1,
      Hx2: verifyrule ?g ?p ?d2 ?nb (Some ?b2) ?k2 |- _ ] =>
          assert (b1 = b2 /\ k1 = k2)
          as [? ?]
          by eauto using verifyrule_depth_some_determinism;
          clear Hx2
  end.

Lemma verifyrule_length_k_le_depth :
  forall g p d nb res k,
  verifyrule g p d nb res k ->
  length k <= d.
Proof.
  intros * H.
  induction H; simpl; lia.
Qed.

Lemma verifyrule_length_k_eq_depth :
  forall g p d nb k,
  verifyrule g p d nb None k ->
  length k = d.
Proof.
  intros * H.
  remember None.
  induction H;
  try discriminate;
  simpl;
  auto.
Qed.

Lemma verifyrule_i_in_k_lt_length_g :
  forall g p d nb res k i,
  verifyrule g p d nb res k ->
  In i k ->
  i < length g.
Proof.
  intros * H Hin.
  generalize dependent i.
  induction H; intros;
  try contradiction;
  eauto;
  try match goal with
    [ Hx: In _ (_ :: _) |- _ ] =>
        destruct Hin;
        try subst;
        auto;
        apply nth_error_Some;
        intro;
        destruct2sep
  end.
Qed.

Inductive coherent_return_type_after_depth_increase : option bool -> option bool -> Prop :=
  | FromNone :
      forall res,
      coherent_return_type_after_depth_increase None res
  | FromSome :
      forall b,
      coherent_return_type_after_depth_increase (Some b) (Some b)
  .

Lemma coherent_return_type_after_depth_increase_transitive :
  forall res1 res2 res3,
  coherent_return_type_after_depth_increase res1 res2 ->
  coherent_return_type_after_depth_increase res2 res3 ->
  coherent_return_type_after_depth_increase res1 res3.
Proof.
  intros * H12 H23.
  inversion H12; subst;
  eauto using coherent_return_type_after_depth_increase.
Qed.

Lemma verifyrule_depth_decrease :
  forall g p d nb res k,
  verifyrule g p (S d) nb res k ->
  exists res' k',
  coherent_return_type_after_depth_increase res' res /\
  verifyrule g p d nb res' k'.
Proof.
  intros * H.
  remember (S d) as d'.
  generalize dependent d.
  induction H;
  intros;
  subst;
  try discriminate;
  try destruct1;
  try match goal with
    [ IHx: forall dx, ?d' = S dx -> _
      |- exists _ _, _ /\ verifyrule _ _ ?d' _ _ _ ] =>
          destruct d'
  end;
  repeat specialize_forall_eq;
  repeat specialize_eq_refl;
  repeat destruct_exists_hyp;
  repeat destruct_and_hyp;
  try match goal with
    [ Hx: coherent_return_type_after_depth_increase _ _ |- _ ] =>
        inversion Hx; subst
  end;
  eauto using verifyrule, coherent_return_type_after_depth_increase.
Qed.

Lemma verifyrule_depth_le_coherent_result_type :
  forall g p d d' nb res k,
  verifyrule g p d' nb res k ->
  d <= d' ->
  exists res' k',
  coherent_return_type_after_depth_increase res' res /\
  verifyrule g p d nb res' k'.
Proof.
  intros * Hv Hle.
  generalize dependent k.
  generalize dependent res.
  generalize dependent nb.
  generalize dependent p.
  generalize dependent g.
  induction Hle as [|d' Hle IH];
  intros.
  - (* d = d', prove for d' *)
    destruct res;
    eauto using coherent_return_type_after_depth_increase.
  - (* d <= d', prove for (S d') *)
    assert (exists res' k',
            coherent_return_type_after_depth_increase res' res /\
            verifyrule g p d' nb res' k')
    as [res' [k' [? ?]]]
    by eauto using verifyrule_depth_decrease.
    assert (exists res'' k'',
            coherent_return_type_after_depth_increase res'' res' /\
            verifyrule g p d nb res'' k'')
    as [res'' [k'' [? ?]]]
    by eauto.
    eauto using coherent_return_type_after_depth_increase_transitive.
Qed.

Lemma verifyrule_res_none_or_some_true :
  forall g p d res k,
  verifyrule g p d true res k ->
  res = None \/ res = Some true.
Proof.
  intros * H.
  remember true.
  induction H; subst; eauto using verifyrule.
  match goal with
    [ Hx: true = true -> Some _ = None \/ Some _ = Some true |- _ ] =>
      specialize (Hx (eq_refl true)) as [? | ?];
      try discriminate;
      try destruct1;
      auto
  end.
Qed.

Inductive same_result_type : bool -> option bool -> bool -> option bool -> Prop :=
  | SRTLeftRecursive :
      forall nb nb',
      same_result_type nb None nb' None
  | SRTNotNullable :
      forall nb nb',
      same_result_type nb (Some nb) nb' (Some nb')
  | SRTNullable :
      forall b b',
      same_result_type b (Some true) b' (Some true)
  .

Lemma verifyrule_nb_change :
  forall g p d nb nb' res k,
  verifyrule g p d nb res k ->
  exists res', same_result_type nb res nb' res' /\ verifyrule g p d nb' res' k.
Proof.
  intros * H.
  generalize dependent nb'.
  induction H;
  intros;
  try discriminate;
  eauto using verifyrule, same_result_type;
  try match goal with
    [ IHx: forall _, exists _, _ /\ _
      |- exists _, _ /\ verifyrule _ _ _ ?nbx _ _ ] =>
          specialize (IHx nbx) as [? [Hsrt ?]];
          inversion Hsrt;
          subst;
          eauto using verifyrule, same_result_type;
          fail
  end.
  try match goal with
    [ IHx1: forall _, exists _, _ /\ verifyrule _ ?p1 _ _ _ _,
      IHx2: forall _, exists _, _ /\ verifyrule _ ?p2 _ _ _ _
      |- exists res, _ /\ verifyrule ?g (PChoice ?p1 ?p2) ?d ?nbx res ?k ] =>
          specialize (IHx1 nbx) as [res' [Hsrt1 ?]];
          inversion Hsrt1;
          subst;
          match goal with
            [ _: verifyrule ?g ?p1 ?d ?nbx (Some ?b) _ |- _ ] =>
                specialize (IHx2 b) as [res'' [Hsrt2 ?]];
                inversion Hsrt2;
                subst;
                eauto using verifyrule, same_result_type
          end
  end.
Qed.

Lemma verifyrule_nb_change_none :
  forall g p d nb nb' k,
  verifyrule g p d nb None k ->
  verifyrule g p d nb' None k.
Proof.
  intros * H.
  eapply verifyrule_nb_change with (nb' := nb') in H as [res' [Hsrt H]].
  inversion Hsrt; subst.
  auto.
Qed.

Lemma verifyrule_nb_change_some :
  forall g p d nb nb' b k,
  verifyrule g p d nb (Some b) k ->
  exists b', verifyrule g p d nb' (Some b') k.
Proof.
  intros * H.
  eapply verifyrule_nb_change with (nb' := nb') in H as [res' [Hsrt H]].
  inversion Hsrt; subst;
  eauto.
Qed.

Ltac pose_verifyrule_nb_none :=
  try match goal with
    [ Hx1: verifyrule ?g ?p ?d _ None ?k,
      Hx2: verifyrule ?g ?p ?d ?nb _ _ |- _ ] =>
          assert (verifyrule g p d nb None k)
          by eauto using verifyrule_nb_change_none
  end.

Lemma verifyrule_k_independent_from_nb :
  forall g p d nb nb' res res' k k',
  verifyrule g p d nb res k ->
  verifyrule g p d nb' res' k' ->
  k = k'.
Proof.
  intros * H H'.
  generalize dependent k'.
  generalize dependent res'.
  generalize dependent nb'.
  induction H;
  intros;
  inversion H';
  subst;
  pose_verifyrule_nb_none;
  pose_verifyrule_determinism;
  try destruct2sep;
  try discriminate;
  try f_equal;
  eauto.
Qed.

Lemma verifyrule_nullable_approx :
  forall g p s d nb res k,
  matches g p s (Success s) ->
  verifyrule g p d nb res k ->
  res = None \/ res = Some true.
Proof.
  intros * Hm Hv.
  remember (Success s).
  generalize dependent k.
  generalize dependent res.
  generalize dependent nb.
  generalize dependent d.
  induction Hm; intros;
  inversion Hv; subst;
  try destruct1;
  try discriminate;
  try match goal with
  [ Hx: ?s = String _ ?s |- _ ] =>
    exfalso; induction s; congruence; fail
  end;
  try match goal with
  [ Hm1: matches _ _ ?s1 (Success ?s2),
    Hm2: matches _ _ ?s2 (Success ?s1) |- _ ] =>
        assert (s1 = s2) by
        (eauto using matches_suffix, suffix_antisymmetric);
        subst
  end;
  try destruct2sep;
  eauto using verifyrule_res_none_or_some_true;
  try match goal with
  [ IHx: _ -> forall d nb res k, verifyrule ?g ?p d nb res k -> _,
    Hx: verifyrule ?g ?p _ _ _ _ |- _ ] =>
      apply IHx in Hx; auto;
      destruct Hx; try discriminate; try destruct1;
      eauto using verifyrule_res_none_or_some_true;
      fail
  end.
Qed.

Theorem verifyrule_fast_forward_exists :
  forall g p d nb res k1 i k2,
  verifyrule g p d nb res (k1 ++ i :: k2) ->
  exists d' nb' res', verifyrule g (PNT i) d' nb' res' (i :: k2).
Proof.
  intros * H.
  remember (k1 ++ i :: k2) as k.
  generalize dependent k2.
  generalize dependent i.
  generalize dependent k1.
  induction H;
  intros;
  eauto using verifyrule;
  destruct k1;
  simpl in *;
  try discriminate;
  try destruct2;
  subst;
  eauto using verifyrule.
Qed.

Theorem verifyrule_fast_forward_none_exists :
  forall g p d nb k1 i k2,
  verifyrule g p d nb None (k1 ++ i :: k2) ->
  exists d' nb', verifyrule g (PNT i) d' nb' None (i :: k2).
Proof.
  intros * H.
  assert (exists d' nb' res', verifyrule g (PNT i) d' nb' res' (i :: k2))
  as [d' [nb' [res' ?]]]
  by eauto using verifyrule_fast_forward_exists.
  destruct res' as [b|]; eauto;
  remember (k1 ++ i :: k2) as k;
  generalize dependent k2;
  generalize dependent i;
  generalize dependent k1;
  generalize dependent nb';
  generalize dependent d';
  generalize dependent b;
  remember None as res;
  induction H;
  intros;
  eauto using verifyrule;
  destruct k1;
  simpl in *;
  try discriminate;
  try destruct2;
  eauto using verifyrule.
Qed.

Theorem verifyrule_fast_forward_none :
  forall g p nb nb' d k1 i k2,
  verifyrule g p d nb None (k1 ++ i :: k2) ->
  verifyrule g (PNT i) (1 + length k2) nb' None (i :: k2).
Proof.
  intros * H.
  assert (exists d' nb', verifyrule g (PNT i) d' nb' None (i :: k2))
  as [d' [nb'' ?]]
  by eauto using verifyrule_fast_forward_none_exists.
  assert (length (i :: k2) = d')
  by eauto using verifyrule_length_k_eq_depth.
  subst.
  simpl in *.
  eauto using verifyrule_nb_change_none.
Qed.

Theorem verifyrule_replace_end :
  forall g p d d' nb nb' k1 i k2 k3,
  verifyrule g p d nb None (k1 ++ i :: k2) ->
  verifyrule g (PNT i) d' nb' None (i :: k3) ->
  length k2 <= length k3 ->
  verifyrule g p (1 + length k1 + length k3) nb None (k1 ++ i :: k3).
Proof.
  intros * Hvp Hvi Hle.
  assert (d = 1 + length k1 + length k2).
  {
    apply verifyrule_length_k_eq_depth in Hvp.
    rewrite app_length in Hvp.
    simpl in Hvp.
    lia.
  }
  subst d.
  assert (d' = 1 + length k3).
  {
    apply verifyrule_length_k_eq_depth in Hvi.
    simpl in Hvi.
    lia.
  }
  subst d'.
  assert (1 + length k1 + length k2 <= 1 + length k1 + length k3) by lia.
  remember (1 + length k1 + length k2) as d.
  remember None as res.
  remember (k1 ++ i :: k2) as k.
  generalize dependent k3.
  generalize dependent k2.
  generalize dependent i.
  generalize dependent k1.
  generalize dependent nb'.
  induction Hvp;
  intros;
  subst;
  try discriminate;
  repeat specialize_eq_refl;
  eauto using verifyrule, verifyrule_depth_le_some_determinism.
  - (* PNT i *)
    destruct k1;
    simpl in *;
    try destruct1;
    try destruct2;
    eauto using verifyrule, verifyrule_nb_change_none, le_S_n.
Qed.

Theorem verifyrule_repetition_in_k :
  forall g p d k1 k2 k3 nb i,
  verifyrule g p d nb None (k1 ++ i :: k2 ++ i :: k3) ->
  exists d', verifyrule g p d' nb None (k1 ++ i :: k2 ++ i :: k2 ++ i :: k3).
Proof.
  intros * H.
  assert (verifyrule g (PNT i) (1 + length (k2 ++ i :: k3)) false None (i :: k2 ++ i :: k3))
  by eauto using verifyrule_fast_forward_none.
  assert (
    length k3 <= length (k2 ++ i :: k3)
  ).
  {
    rewrite app_length.
    simpl.
    lia.
  }
  assert (
    k1 ++ i :: k2 ++ i :: k2 ++ i :: k3 =
    (k1 ++ i :: k2) ++ i :: k2 ++ i :: k3
  ).
  {
    rewrite <- app_assoc.
    simpl.
    trivial.
  }
  assert (
    k1 ++ i :: k2 ++ i :: k3 =
    (k1 ++ i :: k2) ++ i :: k3
  ).
  {
    rewrite <- app_assoc.
    simpl.
    trivial.
  }
  match goal with
    [ Hverifyrule: verifyrule _ _ _ _ _ ?k,
      Heqk: ?k = _ |- _ ] =>
          rewrite Heqk in Hverifyrule
  end.
  match goal with
    [ Heqk: ?k = _
      |- exists _, verifyrule _ _ _ _ _ ?k ] =>
          rewrite Heqk
  end.
  eauto using verifyrule_replace_end.
Qed.

Theorem verifyrule_convergence_S_depth :
  forall g p d nb res k,
  length g < d ->
  verifyrule g p d nb res k ->
  exists k', verifyrule g p (S d) nb res k'.
Proof.
  intros * Hlt Hv.
  destruct res.
  - (* Some b *)
    eauto using verifyrule_depth_le_some_determinism.
  - (* None *)
    assert (length k = d)
    by eauto using verifyrule_length_k_eq_depth.
    subst d.
    assert (exists i k1 k2 k3, k = k1 ++ i :: k2 ++ i :: k3)
    as [i [k1 [k2 [k3 Heqk]]]]
    by eauto using pigeonhole_principle, verifyrule_i_in_k_lt_length_g.
    subst k.
    apply verifyrule_repetition_in_k in Hv as [d Hv].
    assert (length (k1 ++ i :: k2 ++ i :: k2 ++ i :: k3) = d)
    by eauto using verifyrule_length_k_eq_depth.
    subst d.
    match goal with
      [ Hx: verifyrule ?g ?p ?d ?nb None _
        |- exists k, verifyrule ?g ?p ?d' ?nb None k ] =>
            assert (d' <= d) by (repeat (rewrite app_length; simpl); lia)
    end.
    match goal with
      [ Hx: verifyrule _ _ ?d _ _ _, Hy: _ <= ?d |- _ ] =>
        specialize (verifyrule_depth_le_coherent_result_type _ _ _ _ _ _ _ Hx Hy) as [? [? [? ?]]]
    end.
    match goal with
      [ Hx: coherent_return_type_after_depth_increase _ _ |- _ ] =>
          inversion Hx; subst
    end.
    eauto.
Qed.

Theorem verifyrule_convergence :
  forall g p d d' nb res k,
  length g < d ->
  verifyrule g p d nb res k ->
  d <= d' ->
  exists k', verifyrule g p d' nb res k'.
Proof.
  intros * Hlt Hv Hle.
  induction Hle as [|d' Hle [k' IH]];
  eauto using verifyrule_convergence_S_depth, Nat.lt_le_trans.
Qed.

Ltac specialize_coherent :=
  match goal with
    [ Hx: coherent ?g ?p ?b, IHx: coherent ?g ?p ?b -> _ |- _ ] =>
        specialize (IHx Hx)
  end.

Lemma verifyrule_safe_grammar_yields_safe_pattern :
  forall g p nb,
  (forall r, In r g -> coherent g r true) ->
  (forall r nb, In r g -> exists d b k, verifyrule g r d nb (Some b) k) ->
  coherent g p true ->
  exists d b k, verifyrule g p d nb (Some b) k.
Proof.
  intros * Hgc Hgv Hpc.
  generalize dependent nb.
  induction p; intros;
  inversion Hpc; subst;
  repeat specialize_coherent;
  repeat destruct_exists_hyp;
  try (exists 1; eauto using verifyrule; fail);
  try match goal with
    [ Hx1: forall nb, exists _ _ _, verifyrule ?g ?p1 _ nb (Some _) _,
      Hx2: forall nb, exists _ _ _, verifyrule ?g ?p2 _ nb (Some _) _
      |- exists _ _ _, verifyrule ?g (_ ?p1 ?p2) _ ?nb _ _ ] =>
          specialize (Hx1 false);
          specialize (Hx2 nb);
          destruct Hx1 as [d1 [b1 [k1 ?]]];
          destruct Hx2 as [d2 [b2 [k2 ?]]];
          assert (d1 <= d1 + d2) by lia;
          assert (d2 <= d1 + d2) by lia;
          assert (verifyrule g p1 (d1 + d2) false (Some b1) k1)
          by eauto using verifyrule_depth_le_some_determinism;
          assert (verifyrule g p2 (d1 + d2) nb (Some b2) k2)
          by eauto using verifyrule_depth_le_some_determinism;
          destruct b1;
          eauto using verifyrule;
          fail
  end;
  try match goal with
    [ Hx1: forall nb, exists _ _ _, verifyrule ?g ?p1 _ nb (Some _) _,
      Hx2: forall nb, exists _ _ _, verifyrule ?g ?p2 _ nb (Some _) _
      |- exists _ _ _, verifyrule ?g (_ ?p1 ?p2) _ ?nb _ _ ] =>
          specialize (Hx1 nb);
          destruct Hx1 as [d1 [b1 [k1 ?]]];
          specialize (Hx2 b1);
          destruct Hx2 as [d2 [b2 [k2 ?]]];
          assert (d1 <= d1 + d2) by lia;
          assert (d2 <= d1 + d2) by lia;
          assert (verifyrule g p1 (d1 + d2) nb (Some b1) k1)
          by eauto using verifyrule_depth_le_some_determinism;
          assert (verifyrule g p2 (d1 + d2) b1 (Some b2) k2)
          by eauto using verifyrule_depth_le_some_determinism;
          destruct b1;
          eauto using verifyrule;
          fail
  end;
  try match goal with
  [ Hx: forall nb, exists _ _ _, verifyrule ?g ?p _ nb (Some _) _
    |- exists _ _ _, verifyrule ?g (_ ?p) _ ?nb _ _ ] =>
        specialize (Hx true);
        repeat destruct_exists_hyp;
        eauto using verifyrule;
        fail
  end;
  try match goal with
    [ Hnth: nth_error ?g ?n = Some ?p
      |- exists _ _ _, verifyrule g (PNT ?n) _ ?nb _ _ ] =>
        assert (In p g) by eauto using nth_error_In;
        assert (coherent g p true) by eauto;
        assert (exists d b k, verifyrule g p d nb (Some b) k)
        as [d [b [k ?]]] by eauto;
        eauto using verifyrule
  end.
Qed.

(** VerifyRule function with gas **)

Fixpoint verifyrule_comp g p d nb gas {struct gas} :=
  match gas with
  | O => None
  | S gas' => match p with
              | PEmpty => Some (Some true, nil)
              | PChar _ => Some (Some nb, nil)
              | PSequence p1 p2 => match verifyrule_comp g p1 d false gas' with
                                   | Some (Some true, _) => verifyrule_comp g p2 d nb gas'
                                   | Some (Some false, k) => Some (Some nb, k)
                                   | res => res
                                   end
              | PChoice p1 p2 => match verifyrule_comp g p1 d nb gas' with
                                 | Some (Some nb', _) => verifyrule_comp g p2 d nb' gas'
                                 | res => res
                                 end
              | PRepetition p' => verifyrule_comp g p' d true gas'
              | PNot p' => verifyrule_comp g p' d true gas'
              | PNT i => match nth_error g i with
                         | None => None
                         | Some p' => match d with
                                      | O => Some (None, nil)
                                      | S d' => match verifyrule_comp g p' d' nb gas' with
                                                    | Some (res, k) => Some (res, i :: k)
                                                    | None => None
                                                    end
                                      end
                         end
              end
  end.

Lemma verifyrule_comp_soundness :
  forall g p d nb gas res k,
  verifyrule_comp g p d nb gas = Some (res, k) ->
  verifyrule g p d nb res k.
Proof.
  intros * H.
  generalize dependent k.
  generalize dependent res.
  generalize dependent nb.
  generalize dependent d.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros;
  try discriminate;
  simpl in H;
  destruct p;
  try destruct1;
  eauto using verifyrule;
  try match goal with
    [ Hx: match nth_error ?g ?i with | _ => _ end = _ |- _ ] =>
        destruct (nth_error g i) eqn:?;
        try discriminate;
        match goal with
          [ Hx: match ?d with | _ => _ end = _ |- _ ] =>
              destruct d eqn:?;
              try destruct1;
              eauto using verifyrule
        end
  end;
  try match goal with
    [ Hx: match verifyrule_comp ?g ?p ?d ?nb ?gas with | _ => _ end = _ |- _ ] =>
        destruct (verifyrule_comp g p d nb gas) as [[[[]|]]|] eqn:?;
        try discriminate;
        try destruct1;
        eauto using verifyrule;
        fail
  end.
Qed.

Lemma verifyrule_comp_S_gas :
  forall g p d nb res k gas,
  verifyrule_comp g p d nb gas = Some (res, k) ->
  verifyrule_comp g p d nb (S gas) = Some (res, k).
Proof.
  intros.
  generalize dependent k.
  generalize dependent res.
  generalize dependent nb.
  generalize dependent d.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros;
  try discriminate;
  simpl in H;
  destruct p;
  try destruct1;
  remember (S gas) as gas';
  simpl;
  auto;
  try match goal with
      [ |- match nth_error ?g ?i with | _ => _ end = _ ] =>
        destruct (nth_error g i) eqn:?; auto;
        match goal with
          [ |- match ?d with | _ => _ end = _ ] =>
            destruct d; auto
        end
  end;
  try match goal with
    [ Hx: match verifyrule_comp ?g ?p ?d ?nb ?gas with | _ => _ end = _ |- _ ] =>
        let H := fresh in
        destruct (verifyrule_comp g p d nb gas) as [[[[]|]]|] eqn:H;
        try discriminate;
        try destruct1;
        apply IHgas in H;
        rewrite H;
        auto
  end.
Qed.

Lemma verifyrule_comp_le_gas :
  forall g p d nb gas1 gas2 res k,
  verifyrule_comp g p d nb gas1 = Some (res, k) ->
  gas1 <= gas2 ->
  verifyrule_comp g p d nb gas2 = Some (res, k).
Proof.
  intros * H Hle.
  induction Hle;
  auto using verifyrule_comp_S_gas.
Qed.

Lemma verifyrule_comp_termination :
  forall g p d nb,
  (forall r, In r g -> coherent g r true) ->
  coherent g p true ->
  exists gas res k,
  verifyrule_comp g p d nb gas = Some (res, k).
Proof.
  intros * Hgc Hpc.
  generalize dependent nb.
  generalize dependent p.
  generalize dependent g.
  induction d using strong_induction.
  intros.
  generalize dependent nb.
  generalize dependent d.
  generalize dependent g.
  induction p; intros;
  inversion Hpc; subst;
  try (exists 1; simpl; eauto; fail);
  try (
    let H := fresh in
    assert (exists gas res k, verifyrule_comp g p d true gas = Some (res, k))
    as [gas [res [k H]]] by auto;
    exists (1 + gas);
    simpl;
    rewrite H;
    eauto;
    fail
  ).
  - (* PSequence p1 p2 *)
    assert (exists gas res k, verifyrule_comp g p1 d false gas = Some (res, k))
    as [gas1 [res1 [k1 ?]]] by auto.
    assert (exists gas res k, verifyrule_comp g p2 d nb gas = Some (res, k))
    as [gas2 [res2 [k2 ?]]] by auto.
    assert (gas1 <= gas1 + gas2) by lia.
    assert (gas2 <= gas1 + gas2) by lia.
    assert (verifyrule_comp g p2 d nb (gas1 + gas2) = Some (res2, k2))
    by eauto using verifyrule_comp_le_gas.
    exists (1 + gas1 + gas2).
    simpl.
    let H := fresh in
    assert (verifyrule_comp g p1 d false (gas1 + gas2) = Some (res1, k1))
    as H by eauto using verifyrule_comp_le_gas;
    rewrite H.
    destruct res1 as [[|]|];
    eauto.
  - (* PChoice p1 p2 *)
    let H := fresh in
    assert (exists gas res k, verifyrule_comp g p1 d nb gas = Some (res, k))
    as [gas1 [res1 [k1 H]]] by auto;
    destruct res1 as [nb'|];
    try (
      exists (1 + gas1);
      simpl;
      rewrite H;
      eauto;
      fail
    ).
    assert (exists gas res k, verifyrule_comp g p2 d nb' gas = Some (res, k))
    as [gas2 [res2 [k2 ?]]] by auto.
    assert (gas1 <= gas1 + gas2) by lia.
    assert (gas2 <= gas1 + gas2) by lia.
    assert (verifyrule_comp g p2 d nb' (gas1 + gas2) = Some (res2, k2))
    by eauto using verifyrule_comp_le_gas.
    exists (1 + gas1 + gas2).
    simpl.
    let H := fresh in
    assert (verifyrule_comp g p1 d nb (gas1 + gas2) = Some (Some nb', k1))
    as H by eauto using verifyrule_comp_le_gas;
    rewrite H.
    eauto.
  - (* PNT n *)
    destruct d.
    + (* O *)
      exists 1. simpl.
      match goal with
        [ |- exists _ _, match ?x with | _ => _ end = _ ] =>
          destruct x; try discriminate; eauto
      end.
    + (* S d *)
      let H := fresh in
      assert (exists gas res k, verifyrule_comp g p d nb gas = Some (res, k))
      as [gas [res [k H]]] by eauto using nth_error_In;
      exists (1 + gas);
      simpl;
      match goal with
        [ Hx: ?lhs = ?rhs |- exists _ _, match ?lhs with | _ => _ end = _ ] =>
          rewrite Hx
      end;
      rewrite H;
      eauto.
Qed.

Lemma verifyrule_comp_gas_bounded :
  forall g p gas d nb,
  (forall r, In r g -> coherent g r true) ->
  coherent g p true ->
  gas >= pat_size p + d * (grammar_size g) ->
  exists res k,
  verifyrule_comp g p d nb gas = Some (res, k).
Proof.
  intros * Hgc Hpc Hge.
  generalize dependent nb.
  generalize dependent gas.
  generalize dependent p.
  generalize dependent g.
  induction d using strong_induction.
  intros.
  generalize dependent nb.
  generalize dependent d.
  generalize dependent gas.
  generalize dependent g.
  induction p; intros;
  inversion Hpc; subst;
  simpl in Hge;
  destruct gas;
  try match goal with
    [ Hx: 0 >= S _ |- _ ] =>
        inversion Hx
  end;
  try match goal with
    [ |- exists _ _, _ ?g (_ ?p) ?d _ (S ?gas) = _ ] =>
        assert (gas >= pat_size p + d * grammar_size g) by lia
  end;
  try match goal with
    [ |- exists _ _, _ ?g (_ ?p _) ?d _ (S ?gas) = _ ] =>
        assert (gas >= pat_size p + d * grammar_size g) by lia
  end;
  simpl;
  eauto.
  - (* PSequence p1 p2 *)
    assert (exists res k, verifyrule_comp g p1 d false gas = Some (res, k))
    as [res1 [? Hvrp1]] by eauto.
    assert (exists res k, verifyrule_comp g p2 d nb gas = Some (res, k))
    as [? [? ?]] by eauto.
    rewrite Hvrp1.
    destruct res1 as [[|]|]; eauto.
  - (* PChoice p1 p2 *)
    assert (exists res k, verifyrule_comp g p1 d nb gas = Some (res, k))
    as [res1 [? Hvrp1]] by eauto.
    assert (exists res k, verifyrule_comp g p2 d nb gas = Some (res, k))
    as [? [? ?]] by eauto.
    rewrite Hvrp1.
    destruct res1; eauto.
  - (* PNT i *)
    match goal with
      [ Hx: nth_error _ _ = Some _ |- _ ] =>
          rewrite Hx
    end.
    destruct d; eauto.
    assert (pat_size p <= grammar_size g)
    by eauto using nth_error_In, pat_size_le_grammar_size.
    assert (gas >= pat_size p + d * grammar_size g) by lia.
    assert (exists res k, verifyrule_comp g p d nb gas = Some (res, k))
    as [? [? Hvrp]] by eauto using nth_error_In.
    rewrite Hvrp.
    eauto.
Qed.

(** VerifyRule for lists of patterns

    Assumes all rules in g and rs are coherent

    lverifyrule g rs true === all rules in rs are not left-recursive
    lverifyrule g rs false === some rule in rs is left-recursive

**)

Inductive lverifyrule : grammar -> list pat -> bool -> Prop :=
  | LVNil :
      forall g,
      lverifyrule g nil true
  | LVConsSome :
      forall g r rs d nb k b,
      verifyrule g r d false (Some nb) k ->
      lverifyrule g rs b ->
      lverifyrule g (cons r rs) b
  | LVConsNone :
      forall g r rs d k,
      length g < d ->
      verifyrule g r d false None k ->
      lverifyrule g (cons r rs) false
  .

Lemma lverifyrule_determinism :
  forall g rs b1 b2,
  lverifyrule g rs b1 ->
  lverifyrule g rs b2 ->
  b1 = b2.
Proof.
  intros * H1 H2.
  generalize dependent b2.
  induction H1; intros;
  inversion H2; subst;
  try match goal with
    [ HSome : verifyrule ?g ?r ?dSome false (Some ?nb') ?kSome,
      HNone : verifyrule ?g ?r ?dNone false None ?kNone,
      Hlt : length ?g < ?dNone |- _ ] =>
          destruct (Compare_dec.le_ge_dec dSome dNone);
          match goal with
          | [ Hle : ?dSome <= ?dNone |- _ ] =>
                assert (verifyrule g r dNone false (Some nb') kSome)
                by eauto using verifyrule_depth_le_some_determinism
          | [ Hle : ?dSome >= ?dNone |- _ ] =>
                assert (dNone <= dSome) by lia;
                assert (exists k, verifyrule g r dSome false None k)
                as [? ?] by eauto using verifyrule_convergence
          end;
          pose_verifyrule_determinism;
          discriminate;
          fail
  end;
  eauto.
Qed.

Lemma lverifyrule_true_In_false :
  forall g rs r,
  lverifyrule g rs true ->
  In r rs ->
  exists d b k,
  verifyrule g r d false (Some b) k.
Proof.
  intros * Hlv HIn.
  generalize dependent r.
  generalize dependent g.
  induction rs; intros.
  - (* nil *)
    exfalso.
    eauto using in_nil.
  - (* cons r rs *)
    inversion Hlv; subst.
    simpl in HIn.
    destruct HIn.
    + (* r = r' *)
      subst.
      eauto.
    + (* In r rs *)
      eauto.
Qed.

Lemma lverifyrule_true_In :
  forall g rs r nb,
  lverifyrule g rs true ->
  In r rs ->
  exists d b k,
  verifyrule g r d nb (Some b) k.
Proof.
  intros * Hlv HIn.
  assert (exists d b k, verifyrule g r d false (Some b) k)
  as [d [? [k ?]]]
  by eauto using lverifyrule_true_In_false.
  assert (exists b', verifyrule g r d nb (Some b') k)
  as [? ?]
  by eauto using verifyrule_nb_change_some.
  eauto.
Qed.

Fixpoint lverifyrule_comp g rs gas :=
  match rs with
  | nil => Some true
  | cons r rs' => match verifyrule_comp g r (S (length g)) false gas with
                  | Some (Some _, _) => lverifyrule_comp g rs' gas
                  | Some (None, _) => Some false
                  | None => None
                  end
  end.

Lemma lverifyrule_comp_soundness :
  forall g rs gas b,
  lverifyrule_comp g rs gas = Some b ->
  lverifyrule g rs b.
Proof.
  intros * H.
  generalize dependent b.
  generalize dependent gas.
  generalize dependent g.
  induction rs;
  intros.
  - (* nil *)
    simpl in H.
    destruct1.
    eauto using lverifyrule.
  - (* cons r rs *)
    simpl in H.
    match goal with
      [ Hx: match ?x with | _ => _ end = _ |- _ ] =>
          destruct x as [[[|] ?]|] eqn:?;
          try destruct1;
          try discriminate;
          try match goal with
            [ Hx: verifyrule_comp ?g ?r ?d false ?gas = Some (?res, ?k) |- _ ] =>
                assert (verifyrule g r d false res k)
                by eauto using verifyrule_comp_soundness
          end;
          eauto using lverifyrule
    end.
Qed.

Lemma lverifyrule_comp_S_gas :
  forall g rs gas b,
  lverifyrule_comp g rs gas = Some b ->
  lverifyrule_comp g rs (S gas) = Some b.
Proof.
  intros * H.
  induction rs;
  simpl in H.
  - (* nil *)
    destruct1.
    auto.
  - (* cons r rs *)
    match goal with
      [ Hx: match ?x with | _ => _ end = _ |- _ ] =>
          destruct x as [[[|] ?]|] eqn:?;
          try discriminate;
          try destruct1;
          match goal with
            [ Hx: verifyrule_comp ?g ?r ?d ?nb ?gas = Some ?res |- _ ] =>
                assert (verifyrule_comp g r d nb (S gas) = Some res)
                as ? by eauto using verifyrule_comp_S_gas;
                unfold lverifyrule_comp;
                rewrite_match_subject_in_goal;
                fold lverifyrule_comp;
                eauto
          end
    end.
Qed.

Lemma lverifyrule_comp_le_gas :
  forall g rs gas1 gas2 b,
  lverifyrule_comp g rs gas1 = Some b ->
  gas1 <= gas2 ->
  lverifyrule_comp g rs gas2 = Some b.
Proof.
  intros * H Hle.
  induction Hle;
  eauto using lverifyrule_comp_S_gas.
Qed.

Lemma lverifyrule_comp_termination :
  forall g rs,
  lcoherent g g true ->
  lcoherent g rs true ->
  exists gas b,
  lverifyrule_comp g rs gas = Some b.
Proof.
  intros * Hg Hrs.
  induction rs as [|r rs].
  - (* nil *)
    exists 0.
    simpl.
    eauto.
  - (* cons r rs *)
    inversion Hrs; subst.
    match goal with
      [ Hx: lcoherent ?g ?rs true -> _, Hy: lcoherent ?g ?rs true |- _ ] =>
          specialize (Hx Hy) as [gas1 [resrs ?]]
    end.
    assert (exists gas res k, verifyrule_comp g r (S (length g)) false gas = Some (res, k))
    as [gas2 [res [k Hv]]]
    by eauto using verifyrule_comp_termination, lcoherent_true_In.
    simpl.
    assert (gas1 <= gas1 + gas2) by lia.
    assert (gas2 <= gas1 + gas2) by lia.
    assert (lverifyrule_comp g rs (gas1 + gas2) = Some resrs)
    as Hlv' by eauto using lverifyrule_comp_le_gas.
    assert (verifyrule_comp g r (S (length g)) false (gas1 + gas2) = Some (res, k))
    as Hv' by eauto using verifyrule_comp_le_gas.
    exists (gas1 + gas2).
    rewrite Hv'.
    destruct res;
    eauto.
Qed.

Lemma lverifyrule_comp_gas_bounded :
  forall g rs gas,
  lcoherent g g true ->
  lcoherent g rs true ->
  gas >= grammar_size rs + S (length g) * (grammar_size g) ->
  exists b, lverifyrule_comp g rs gas = Some b.
Proof.
  intros * Hg Hrs Hge.
  generalize dependent gas.
  induction rs as [|r rs];
  intros;
  inversion Hrs; subst;
  simpl;
  eauto.
  simpl in Hge.
  assert (gas >= grammar_size rs + S (length g) * grammar_size g) by lia.
  assert (exists b, lverifyrule_comp g rs gas = Some b)
  as [? ?] by eauto.
  assert (gas >= pat_size r + S (length g) * grammar_size g) by lia.
  assert (exists res k, verifyrule_comp g r (S (length g)) false gas = Some (res, k))
  as [res [? Hv]] by eauto using verifyrule_comp_gas_bounded, lcoherent_true_In.
  rewrite Hv.
  destruct res; eauto.
Qed.

Lemma lverifyrule_comp_termination_grammar :
  forall g,
  lcoherent g g true ->
  exists gas b,
  lverifyrule_comp g g gas = Some b.
Proof.
  intros.
  eauto using lverifyrule_comp_termination.
Qed.
