From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List.
From Coq Require Import Lia.
From Peg Require Import Syntax.
From Peg Require Import Tactics.
From Peg Require Import Match.
From Peg Require Import Coherent.
From Peg Require Import Verifyrule.
From Peg Require Import Suffix.

Import ListNotations.

(** Nullable predicate **)
(** A "nullable" pattern may match successfully without consuming any characters **)

Inductive nullable : grammar -> pat -> nat -> option bool -> Prop :=
  | NEmpty :
      forall g d,
      nullable g PEmpty d (Some true)
  | NSet :
      forall g f d,
      nullable g (PSet f) d (Some false)
  | NSequenceNone :
      forall g p1 p2 d,
      nullable g p1 d None ->
      nullable g (PSequence p1 p2) d None
  | NSequenceSomeFalse :
      forall g p1 p2 d,
      nullable g p1 d (Some false) ->
      nullable g (PSequence p1 p2) d (Some false)
  | NSequenceSomeTrue :
      forall g p1 p2 d res,
      nullable g p1 d (Some true) ->
      nullable g p2 d res ->
      nullable g (PSequence p1 p2) d res
  | NChoiceNone :
      forall g p1 p2 d,
      nullable g p1 d None ->
      nullable g (PChoice p1 p2) d None
  | NChoiceSomeFalse :
      forall g p1 p2 d res,
      nullable g p1 d (Some false) ->
      nullable g p2 d res ->
      nullable g (PChoice p1 p2) d res
  | NChoiceSomeTrue :
      forall g p1 p2 d,
      nullable g p1 d (Some true) ->
      nullable g (PChoice p1 p2) d (Some true)
  | NRepetition :
      forall g p d,
      nullable g (PRepetition p) d (Some true)
  | NNot :
      forall g p d,
      nullable g (PNot p) d (Some true)
  | NNTZero :
      forall g i p,
      nth_error g i = Some p ->
      nullable g (PNT i) O None
  | NNTSucc :
      forall g i p res d,
      nth_error g i = Some p ->
      nullable g p d res ->
      nullable g (PNT i) (S d) res
  .

(* ! {A <- A} |= A *)
Example nullable_ex1 :
  forall d b,
    ~ nullable
    [PNT 0]
    (PNT 0)
    d
    (Some b).
Proof.
  intros * H.
  remember (PNT 0) as p.
  remember [p] as g.
  remember (Some b) as res.
  induction H;
  try discriminate;
  try destruct1;
  simpl in H;
  destruct1;
  auto.
Qed.

(* G |= ε *)
Example nullable_ex2 :
  forall g d,
  nullable g PEmpty d (Some true).
Proof.
  intros.
  eauto using nullable.
Qed.

Example dot_charset : (ascii -> bool) :=
  (fun _ => true).

(* ! G |= . *)
Example nullable_ex3 :
  forall g d,
  nullable g (PSet dot_charset) d (Some false).
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= ε ε *)
Example nullable_ex5 :
  forall g d,
  nullable g (PSequence PEmpty PEmpty) d (Some true).
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= . ε *)
Example nullable_ex6 :
  forall g d,
  nullable g (PSequence (PSet dot_charset) PEmpty) d (Some false).
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= ε . *)
Example nullable_ex7 :
  forall g d,
  nullable g (PSequence PEmpty (PSet dot_charset)) d (Some false).
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= . . *)
Example nullable_ex8 :
  forall g d,
  nullable g (PSequence (PSet dot_charset) (PSet dot_charset)) d (Some false).
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= ε / ε *)
Example nullable_ex9 :
  forall g d,
  nullable g (PChoice PEmpty PEmpty) d (Some true).
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= . / ε *)
Example nullable_ex10 :
  forall g d,
  nullable g (PChoice (PSet dot_charset) PEmpty) d (Some true).
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= ε / . *)
Example nullable_ex11 :
  forall g d,
  nullable g (PChoice PEmpty (PSet dot_charset)) d (Some true).
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= . / . *)
Example nullable_ex12 :
  forall g d,
  nullable g (PChoice (PSet dot_charset) (PSet dot_charset)) d (Some false).
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= p* *)
Example nullable_ex13 :
  forall g p d,
  nullable g (PRepetition p) d (Some true).
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= !p *)
Example nullable_ex14 :
  forall g p d,
  nullable g (PNot p) d (Some true).
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! { P <- . P } |= P *)
Example nullable_ex15 :
  forall d,
  nullable
    [PSequence (PSet dot_charset) (PNT 0)]
    (PNT 0)
    (S d)
    (Some false).
Proof.
  intros.
  econstructor; simpl; eauto.
  eauto using nullable.
Qed.

(* { P <- . P / ε } |= P *)
Example nullable_ex16 :
  forall d,
  nullable
    [PChoice (PSequence (PSet dot_charset) (PNT 0)) PEmpty]
    (PNT 0)
    (S d)
    (Some true).
Proof.
  intros.
  econstructor; simpl; eauto.
  eauto using nullable.
Qed.

(* ! {} |= A *)
Example nullable_ex17 :
  forall d res,
  ~ nullable [] (PNT 0) d res.
Proof.
  intros * H.
  inversion H;
  subst;
  try discriminate.
Qed.

(* { A <- . A | ε ; B <- A A } |= A B *)
Example nullable_ex18 :
  forall d,
  nullable
  [PChoice (PSequence (PSet dot_charset) (PNT 0)) PEmpty; PSequence (PNT 0) (PNT 0)]
  (PSequence (PNT 0) (PNT 1))
  (S (S d))
  (Some true).
Proof.
  intros.
  repeat match goal with
         | [ |- nullable _ (PSequence _ _) _ _ ] => econstructor
         | [ |- nullable _ (PNT _) _ _ ] => econstructor; simpl; eauto
         | [ |- nullable _ (PChoice _ _) _ _ ] => eauto using nullable
         | _ => fail
         end.
Qed.

Lemma nullable_determinism :
  forall g p d res1 res2,
  nullable g p d res1 ->
  nullable g p d res2 ->
  res1 = res2.
Proof.
  intros * H1 H2.
  generalize dependent res2.
  induction H1;
  intros;
  inversion H2; subst;
  try destruct2sep;
  try match goal with
  [ IHx: forall resx, nullable ?g ?p ?d resx -> ?res1 = resx,
    Hx: nullable ?g ?p ?d ?res2 |- _ ] =>
        apply IHx in Hx;
        discriminate
  end;
  auto.
Qed.

Ltac pose_nullable_determinism :=
  match goal with
    [ Hx1: nullable ?g ?p ?d ?res1,
      Hx2: nullable ?g ?p ?d ?res2 |- _ ] =>
          assert (res1 = res2)
          by eauto using nullable_determinism;
          clear Hx2
  end.

Lemma nullable_Some_S_depth :
  forall g p d b,
  nullable g p d (Some b) ->
  nullable g p (S d) (Some b).
Proof.
  intros * H.
  remember (Some b) as res.
  generalize dependent b.
  induction H; intros;
  try discriminate;
  eauto using nullable.
Qed.

Lemma nullable_Some_depth_le :
  forall g p d d' b,
  nullable g p d (Some b) ->
  d <= d' ->
  nullable g p d' (Some b).
Proof.
  intros * H Hle.
  induction Hle;
  eauto using nullable_Some_S_depth.
Qed.

Lemma nullable_Some_determinism :
  forall g p d1 d2 b1 b2,
  nullable g p d1 (Some b1) ->
  nullable g p d2 (Some b2) ->
  b1 = b2.
Proof.
  intros.
  pose (d1 + d2) as dsum.
  assert (d1 <= dsum) by lia.
  assert (d2 <= dsum) by lia.
  assert (nullable g p dsum (Some b1))
  by eauto using nullable_Some_depth_le.
  assert (nullable g p dsum (Some b2))
  by eauto using nullable_Some_depth_le.
  pose_nullable_determinism.
  destruct1.
  eauto.
Qed.

Ltac pose_nullable_Some_determinism :=
  match goal with
    [ Hx1: nullable ?g ?p _ (Some ?b1),
      Hx2: nullable ?g ?p _ (Some ?b2) |- _ ] =>
          assert (b1 = b2)
          by eauto using nullable_Some_determinism;
          clear Hx2
  end.

Lemma verifyrule_similar_to_nullable :
  forall g p d b k,
  verifyrule g p d false (Some b) k ->
  nullable g p d (Some b).
Proof.
  intros * H.
  remember (Some b) as res.
  remember false as nb.
  generalize dependent b.
  induction H; intros;
  try destruct1;
  try discriminate;
  subst;
  eauto using nullable;
  try match goal with
    [ Hx: verifyrule _ _ _ false (Some ?nb') _ |- _ ] =>
        destruct nb'
  end;
  try match goal with
    [ Hx: verifyrule _ _ _ true (Some ?b) _ |- _ ] =>
        apply verifyrule_res_none_or_some_true in Hx as [|];
        try discriminate;
        try destruct1
  end;
  eauto using nullable.
Qed.

Lemma nullable_none_is_verifyrule_none :
  forall g p d,
  (forall r, In r g -> coherent g r true) ->
  coherent g p true ->
  nullable g p d None ->
  exists k, verifyrule g p d false None k.
Proof.
  intros * Hcg Hcp Hn.
  remember None as res.
  induction Hn;
  inversion Hcp;
  subst;
  try discriminate;
  try destruct2sep;
  try match goal with
    [ Hx: nth_error ?g ?i = Some ?p |- _ ] =>
        assert (In p g)
        by eauto using nth_error_In;
        assert (coherent g p true)
        by eauto
  end;
  repeat match goal with
    [ IHx: (forall r, In r ?g -> coherent ?g ?p ?b) -> _,
      Hx: forall r, In r ?g -> coherent ?g ?p ?b |- _ ] =>
        specialize (IHx Hx)
  end;
  repeat specialize_coherent;
  try specialize_eq_refl;
  try destruct_exists_hyp;
  eauto using verifyrule;
  try (
    assert (exists gas res k, verifyrule_comp g p1 d false gas = Some (res, k))
    as [gas [res' [k Hvcp1]]]
    by eauto using verifyrule_comp_termination;
    assert (verifyrule g p1 d false res' k)
    by eauto using verifyrule_comp_soundness;
    destruct res';
    eauto using verifyrule;
    assert (nullable g p1 d (Some b))
    by eauto using verifyrule_similar_to_nullable;
    pose_nullable_determinism;
    destruct1;
    eauto using verifyrule;
    fail
  ).
Qed.

Lemma string_not_infinite :
  forall a s,
  String a s = s ->
  False.
Proof.
  intros.
  induction s; congruence.
Qed.

Lemma nullable_Some_false_matches :
  forall g p d,
  nullable g p d (Some false) ->
  ~ exists s, matches g p s (Success s).
Proof.
  intros * Hnullable [s Hmatches].
  generalize dependent s.
  remember (Some false) as res.
  induction Hnullable;
  intros;
  inversion Hmatches;
  subst;
  try destruct2sep;
  try discriminate;
  try specialize_eq_hyp;
  try match goal with
    [ H12: matches _ _ ?s1 (Success ?s2),
      H21: matches _ _ ?s2 (Success ?s1) |- _ ] =>
          assert (suffix s1 s2)
          by eauto using matches_suffix;
          assert (suffix s2 s1)
          by eauto using matches_suffix;
          assert (s1 = s2)
          by eauto using suffix_antisymmetric;
          subst
  end;
  eauto using string_not_infinite.
Qed.

Lemma nullable_Some_false_proper_suffix :
  forall g p d s s',
  nullable g p d (Some false) ->
  matches g p s (Success s') ->
  proper_suffix s' s.
Proof.
  intros * Hnullable Hmatches.
  apply matches_suffix in Hmatches as Hsuffix.
  induction Hsuffix.
  - (* SuffixRefl *)
    exfalso.
    eauto using (nullable_Some_false_matches _ _ _ Hnullable).
  - (* SuffixChar *)
    eauto using suffix_is_proper_suffix_with_char.
Qed.

Lemma nullable_convergence :
  forall g p d d' res,
  (forall r, In r g -> coherent g r true) ->
  (forall r nb, In r g -> exists d b k, verifyrule g r d nb (Some b) k) ->
  coherent g p true ->
  length g < d ->
  nullable g p d res ->
  d <= d' ->
  nullable g p d' res.
Proof.
  intros * Hgc Hgv Hpc Hlt H Hle.
  assert (exists gas res k, verifyrule_comp g p d false gas = Some (res, k))
  as [? [? [? ?]]]
  by eauto using verifyrule_comp_termination.
  match goal with
    [ Hx: verifyrule_comp ?g ?p ?d false ?gas = Some (?res, ?k) |- _ ] =>
        assert (verifyrule g p d false res k)
        by eauto using verifyrule_comp_soundness
  end.
  assert (exists d b k, verifyrule g p d false (Some b) k)
  as [? [? [? ?]]]
  by eauto using verifyrule_safe_grammar_yields_safe_pattern.
  match goal with
    [ Hx: verifyrule ?g ?p ?d1 false (Some ?b) ?k1,
      Hy: verifyrule ?g ?p ?d2 false ?res ?k2,
      Hz: length ?g < ?d2 |- _ ] =>
          destruct (Compare_dec.le_ge_dec d1 d2);
          try match goal with
            [ Hw: ?d1 <= ?d2,
              Hv: length ?g < ?d2 |- _ ] =>
                  assert (verifyrule g p d2 false (Some b) k1)
                  by eauto using verifyrule_depth_le_some_determinism
          end;
          try match goal with
            [ Hw: ?d1 >= ?d2 |- _ ] =>
                assert (d2 <= d1) by lia;
                assert (exists k', verifyrule g p d1 false res k')
                as [? ?]
                by eauto using verifyrule_convergence;
                pose_verifyrule_determinism;
                subst
          end
  end;
  match goal with
    [ Hx: nullable ?g ?p ?d ?res,
      Hy: verifyrule ?g ?p ?d false (Some ?b) ?k |- _ ] =>
          assert (nullable g p d (Some b))
          by eauto using verifyrule_similar_to_nullable;
          pose_nullable_determinism;
          subst;
          assert (exists k', verifyrule g p d' false (Some b) k')
          as [? ?]
          by eauto using verifyrule_convergence;
          eauto using verifyrule_similar_to_nullable
  end.
Qed.

(** Nullable function with gas **)

Fixpoint nullable_comp g p d gas {struct gas} :=
  match gas with
  | O => None
  | S gas' => match p with
              | PEmpty => Some (Some true)
              | PSet _ => Some (Some false)
              | PSequence p1 p2 => match nullable_comp g p1 d gas' with
                                   | Some (Some true) => nullable_comp g p2 d gas'
                                   | ob => ob
                                   end
              | PChoice p1 p2 => match nullable_comp g p1 d gas' with
                                 | Some (Some false) => nullable_comp g p2 d gas'
                                 | ob => ob
                                 end
              | PRepetition _ => Some (Some true)
              | PNot _ => Some (Some true)
              | PNT i => match nth_error g i with
                         | Some p' => match d with
                                      | O => Some None
                                      | S d' => nullable_comp g p' d' gas'
                                      end
                         | None => None
                         end
              end
  end.

Lemma nullable_comp_soundness :
  forall g p d gas res,
  nullable_comp g p d gas = Some res ->
  nullable g p d res.
Proof.
  intros * H.
  generalize dependent res.
  generalize dependent d.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros; try discriminate.
  destruct p; eauto using nullable;
  try (simpl in H; discriminate; fail);
  try (
    simpl in H;
    try destruct (nullable_comp g p1 d gas)
    as [[[|]|]|] eqn:?;
    try discriminate;
    try destruct1;
    eauto using nullable;
    fail
  );
  try (
    simpl in H;
    destruct (nth_error g n) eqn:?;
    try discriminate;
    try destruct1;
    destruct d;
    try discriminate;
    try destruct1;
    assert (In p g) as HIn by (eauto using nth_error_In);
    eauto using nullable;
    fail
  ).
Qed.

Lemma nullable_comp_S_gas :
  forall g p d gas res,
  nullable_comp g p d gas = Some res ->
  nullable_comp g p d (S gas) = Some res.
Proof.
  intros * H.
  generalize dependent res.
  generalize dependent d.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros; try discriminate;
  destruct p; simpl in H;
  try destruct1;
  auto;
  try (
    destruct (nullable_comp g p1 d gas) as [[[|]|]|] eqn:Hn1;
    destruct (nullable_comp g p2 d gas) as [[[|]|]|] eqn:Hn2;
    try discriminate;
    destruct1;
    try apply IHgas in Hn1;
    try apply IHgas in Hn2;
    remember (S gas);
    simpl;
    repeat destruct_match_subject_in_goal;
    try destruct1;
    try discriminate;
    auto
  ).
  try (
    destruct (nth_error g n) eqn:Hn;
    remember (S gas);
    simpl;
    destruct_match_subject_in_goal;
    try destruct1;
    try discriminate;
    auto;
    destruct_match_subject_in_goal;
    auto
  ).
Qed.

Lemma nullable_comp_le_gas :
  forall g p d gas1 gas2 res,
  nullable_comp g p d gas1 = Some res ->
  gas1 <= gas2 ->
  nullable_comp g p d gas2 = Some res.
Proof.
  intros * H Hle.
  induction Hle;
  auto using nullable_comp_S_gas.
Qed.

(* Here, we could have used the max pat_size of the grammar
   instead of summing up the pat_size of each rule of the grammar,
   but the sum makes the proof of lower bound easier *)
Lemma nullable_comp_gas_bounded :
  forall g p d gas,
  (forall r, In r g -> coherent g r true) ->
  coherent g p true ->
  gas >= pat_size p + d * (grammar_size g) ->
  exists res, nullable_comp g p d gas = Some res.
Proof.
  intros * Hgc Hpc Hge.
  generalize dependent d.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros;
  try (destruct p; inversion Hge; fail);
  destruct p;
  inversion Hpc; subst;
  try (simpl; eauto; fail);
  try (
    simpl in Hge;
    assert (gas >= pat_size p1 + d * grammar_size g) by lia;
    assert (gas >= pat_size p2 + d * grammar_size g) by lia;
    assert (exists res, nullable_comp g p1 d gas = Some res) as [res1 Hn1] by auto;
    assert (exists res, nullable_comp g p2 d gas = Some res) by auto;
    simpl;
    rewrite Hn1;
    destruct res1 as [[|]|];
    eauto;
    fail
  );
  try (
    simpl in Hge;
    simpl;
    match goal with
      [ Hx: ?lhs = _ |-
        exists _, match ?lhs with | _ => _ end = _ ] =>
          rewrite Hx
    end;
    assert (In p g) as HIn by (eauto using nth_error_In);
    destruct d; eauto;
    specialize (pat_size_le_grammar_size _ _ HIn) as Hle;
    assert (gas >= pat_size p + d * grammar_size g) by lia;
    auto;
    fail
  ).
Qed.

(* Here, we don't care about any particular lower bound value.
   We just know there exists SOME gas for which nullable_comp
   gives SOME result. :-) *)
Lemma nullable_comp_termination :
  forall g p d,
  (forall r, In r g -> coherent g r true) ->
  coherent g p true ->
  exists gas b,
  nullable_comp g p d gas = Some b.
Proof.
  eauto using nullable_comp_gas_bounded.
Qed.
