From Coq Require Import Bool.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Peg Require Import Coherent.
From Peg Require Import Match.
From Peg Require Import Suffix.
From Peg Require Import Syntax.
From Peg Require Import Tactics.
From Peg Require Import Verifyrule.

Import ListNotations.


(** Nullable predicate **)
(** A "nullable" pattern may match successfully without consuming any characters **)

Inductive nullable : grammar -> pat -> bool -> Prop :=
  | NEmpty :
      forall g,
      nullable g PEmpty true
  | NSet :
      forall g cs,
      nullable g (PSet cs) false
  | NSequence1 :
      forall g p1 p2,
      nullable g p1 false ->
      nullable g (PSequence p1 p2) false
  | NSequence2 :
      forall g p1 p2 b,
      nullable g p1 true ->
      nullable g p2 b ->
      nullable g (PSequence p1 p2) b
  | NChoice1 :
      forall g p1 p2,
      nullable g p1 true ->
      nullable g (PChoice p1 p2) true
  | NChoice :
      forall g p1 p2 b,
      nullable g p1 false ->
      nullable g p2 b ->
      nullable g (PChoice p1 p2) b
  | NRepetition :
      forall g p,
      nullable g (PRepetition p) true
  | NNot :
      forall g p,
      nullable g (PNot p) true
  | NAnd :
      forall g p,
      nullable g (PAnd p) true
  | NNT :
      forall g i p b,
      nth_error g i = Some p ->
      nullable g p b ->
      nullable g (PNT i) b
  .

(* ! {A <- A} |= A *)
Example nullable_ex1 :
  forall b,
    ~ nullable
    [PNT 0]
    (PNT 0)
    b.
Proof.
  intros * H.
  remember (PNT 0) as p.
  remember [p] as g.
  induction H;
  try discriminate;
  try destruct1;
  simpl in H;
  destruct1;
  auto.
Qed.

(* G |= ε *)
Example nullable_ex2 :
  forall g,
  nullable g PEmpty true.
Proof.
  intros.
  eauto using nullable.
Qed.

Example PDot : pat := PSet (fun _ => true).

(* ! G |= . *)
Example nullable_ex3 :
  forall g,
  nullable g PDot false.
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= ε ε *)
Example nullable_ex5 :
  forall g,
  nullable g (PSequence PEmpty PEmpty) true.
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= . ε *)
Example nullable_ex6 :
  forall g,
  nullable g (PSequence PDot PEmpty) false.
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= ε . *)
Example nullable_ex7 :
  forall g,
  nullable g (PSequence PEmpty PDot) false.
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= . . *)
Example nullable_ex8 :
  forall g,
  nullable g (PSequence PDot PDot) false.
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= ε / ε *)
Example nullable_ex9 :
  forall g,
  nullable g (PChoice PEmpty PEmpty) true.
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= . / ε *)
Example nullable_ex10 :
  forall g,
  nullable g (PChoice PDot PEmpty) true.
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= ε / . *)
Example nullable_ex11 :
  forall g,
  nullable g (PChoice PEmpty PDot) true.
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= . / . *)
Example nullable_ex12 :
  forall g,
  nullable g (PChoice PDot PDot) false.
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= p* *)
Example nullable_ex13 :
  forall g p,
  nullable g (PRepetition p) true.
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= !p *)
Example nullable_ex14 :
  forall g p,
  nullable g (PNot p) true.
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= &p *)
Example nullable_ex14' :
  forall g p,
  nullable g (PAnd p) true.
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! { P <- . P } |= P *)
Example nullable_ex15 :
  nullable
    [PSequence PDot (PNT 0)]
    (PNT 0)
    false.
Proof.
  intros.
  econstructor; simpl; eauto.
  eauto using nullable.
Qed.

(* { P <- . P / ε } |= P *)
Example nullable_ex16 :
  nullable
    [PChoice (PSequence PDot (PNT 0)) PEmpty]
    (PNT 0)
    true.
Proof.
  intros.
  econstructor; simpl; eauto.
  eauto using nullable.
Qed.

(* ! {} |= A *)
Example nullable_ex17 :
  forall b,
  ~ nullable [] (PNT 0) b.
Proof.
  intros * H.
  inversion H;
  subst;
  try discriminate.
Qed.

(* { A <- . A | ε ; B <- A A } |= A B *)
Example nullable_ex18 :
  nullable
  [PChoice (PSequence PDot (PNT 0)) PEmpty; PSequence (PNT 0) (PNT 0)]
  (PSequence (PNT 0) (PNT 1))
  true.
Proof.
  intros.
  repeat match goal with
         | [ |- nullable _ (PSequence _ _) _ ] => econstructor
         | [ |- nullable _ (PNT _) _ ] => econstructor; simpl; eauto
         | [ |- nullable _ (PChoice _ _) _ ] => eauto using nullable
         | _ => fail
         end.
Qed.

Lemma nullable_determinism :
  forall g p b1 b2,
  nullable g p b1 ->
  nullable g p b2 ->
  b1 = b2.
Proof.
  intros * H1 H2.
  generalize dependent b2.
  induction H1;
  intros;
  inversion H2; subst;
  try destruct2sep;
  try match goal with
  [ IHx: forall bx, nullable ?g ?p bx -> ?b1 = bx,
    Hx: nullable ?g ?p ?b2 |- _ ] =>
        apply IHx in Hx;
        discriminate
  end;
  auto.
Qed.

Ltac pose_nullable_determinism :=
  match goal with
    [ Hx1: nullable ?g ?p ?b1,
      Hx2: nullable ?g ?p ?b2 |- _ ] =>
          assert (b1 = b2)
          by eauto using nullable_determinism;
          clear Hx2
  end.

Lemma verifyrule_similar_to_nullable :
  forall g p d b k,
  verifyrule g p d false (Some b) k ->
  nullable g p b.
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

Lemma string_not_infinite :
  forall a s,
  String a s = s ->
  False.
Proof.
  intros.
  induction s; congruence.
Qed.

Lemma nullable_false_matches :
  forall g p,
  nullable g p false ->
  ~ exists s, matches g p s (Success s).
Proof.
  intros * Hnullable [s Hmatches].
  generalize dependent s.
  remember false as b.
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

Lemma nullable_false_proper_suffix :
  forall g p s s',
  nullable g p false ->
  matches g p s (Success s') ->
  proper_suffix s' s.
Proof.
  intros * Hnullable Hmatches.
  apply matches_suffix in Hmatches as Hsuffix.
  induction Hsuffix.
  - (* SuffixRefl *)
    exfalso.
    eauto using (nullable_false_matches _ _ Hnullable).
  - (* SuffixChar *)
    eauto using suffix_is_proper_suffix_with_char.
Qed.

(** Nullable function with gas **)

Fixpoint nullable_comp g p gas {struct gas} :=
  match gas with
  | O => None
  | S gas' => match p with
              | PEmpty => Some true
              | PSet _ => Some false
              | PSequence p1 p2 => match nullable_comp g p1 gas' with
                                   | Some true => nullable_comp g p2 gas'
                                   | ob => ob
                                   end
              | PChoice p1 p2 => match nullable_comp g p1 gas' with
                                 | Some false => nullable_comp g p2 gas'
                                 | ob => ob
                                 end
              | PRepetition _ => Some true
              | PNot _ => Some true
              | PAnd _ => Some true
              | PNT i => match nth_error g i with
                         | Some p' => nullable_comp g p' gas'
                         | None => None
                         end
              end
  end.

Lemma nullable_comp_soundness :
  forall g p gas b,
  nullable_comp g p gas = Some b ->
  nullable g p b.
Proof.
  intros * H.
  generalize dependent b.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros; try discriminate.
  destruct p; eauto using nullable;
  try (simpl in H; discriminate; fail);
  try (
    simpl in H;
    try destruct (nullable_comp g p1 gas)
    as [[|]|] eqn:?;
    try discriminate;
    try destruct1;
    eauto using nullable;
    fail
  );
  try (
    simpl in H;
    destruct (nth_error g n) eqn:?;
    try discriminate;
    eauto using nullable;
    fail
  ).
Qed.

Lemma nullable_comp_S_gas :
  forall g p gas b,
  nullable_comp g p gas = Some b ->
  nullable_comp g p (S gas) = Some b.
Proof.
  intros * H.
  generalize dependent b.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros; try discriminate;
  destruct p; simpl in H;
  try destruct1;
  auto;
  try (
    destruct (nullable_comp g p1 gas) as [[|]|] eqn:Hn1;
    destruct (nullable_comp g p2 gas) as [[|]|] eqn:Hn2;
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
  );
  try (
    destruct (nth_error g n) eqn:Hn;
    remember (S gas);
    simpl;
    destruct_match_subject_in_goal;
    try destruct1;
    try discriminate;
    auto
  ).
Qed.

Lemma nullable_comp_le_gas :
  forall g p gas1 gas2 b,
  nullable_comp g p gas1 = Some b ->
  gas1 <= gas2 ->
  nullable_comp g p gas2 = Some b.
Proof.
  intros * H Hle.
  induction Hle;
  auto using nullable_comp_S_gas.
Qed.

Lemma nullable_comp_gas_exists :
  forall g p d b k,
  lcoherent g g true ->
  coherent g p true ->
  verifyrule g p d false (Some b) k ->
  exists gas, nullable_comp g p gas = Some b.
Proof.
  intros * Hgc Hpc Hpv.
  remember false as nb.
  remember (Some b) as res.
  generalize dependent b.
  induction Hpv; intros;
  inversion Hpc; subst;
  try discriminate;
  try destruct1;
  try (assert (b = true) by eauto using verifyrule_true_res_some_true; subst);
  try (exists 1; simpl; eauto; fail).
  - (* PSequence p1 p2, where p1 is nullable *)
    assert (exists gas, nullable_comp g p1 gas = Some true)
    as [gas1 ?] by eauto.
    assert (exists gas, nullable_comp g p2 gas = Some b)
    as [gas2 ?] by eauto.
    pose (gas1 + gas2) as gas.
    assert (gas1 <= gas) by lia.
    assert (gas2 <= gas) by lia.
    assert (nullable_comp g p1 gas = Some true)
    by eauto using nullable_comp_le_gas.
    assert (nullable_comp g p2 gas = Some b)
    by eauto using nullable_comp_le_gas.
    exists (S gas).
    simpl.
    rewrite_match_subject_in_goal.
    auto.
  - (* PSequence p1 p2, where p1 is non-nullable *)
    assert (exists gas, nullable_comp g p1 gas = Some false)
    as [gas ?] by eauto.
    exists (S gas).
    simpl.
    rewrite_match_subject_in_goal.
    auto.
  - (* PChoice p1 p2 *)
    assert (exists gas, nullable_comp g p1 gas = Some nb')
    as [gas1 ?] by eauto.
    destruct nb'.
    + (* p1 is nullable *)
      exists (S gas1).
      simpl.
      rewrite_match_subject_in_goal.
      assert (b = true)
      by eauto using verifyrule_true_res_some_true.
      subst.
      auto.
    + (* p1 is non-nullable *)
      assert (exists gas, nullable_comp g p2 gas = Some b)
      as [gas2 ?] by eauto.
      pose (gas1 + gas2) as gas.
      assert (gas1 <= gas) by lia.
      assert (gas2 <= gas) by lia.
      assert (nullable_comp g p1 gas = Some false)
      by eauto using nullable_comp_le_gas.
      assert (nullable_comp g p2 gas = Some b)
      by eauto using nullable_comp_le_gas.
      exists (S gas).
      simpl.
      rewrite_match_subject_in_goal.
      auto.
  - (* PNT i *)
    destruct2sep.
    match goal with
      [ Hx: nth_error _ _ = Some ?p |- _ ] =>
          assert (In p g) by eauto using nth_error_In;
          assert (coherent g p true) by eauto using lcoherent_true_In;
          assert (exists gas, nullable_comp g p gas = Some b)
          as [gas ?] by eauto;
          exists (S gas);
          simpl;
          rewrite Hx;
          auto
    end.
Qed.

Lemma nullable_comp_gas_bounded_by_depth :
  forall g p d b k gas,
  lcoherent g g true ->
  coherent g p true ->
  verifyrule g p d false (Some b) k ->
  gas >= pat_size p + d * (grammar_size g) ->
  nullable_comp g p gas = Some b.
Proof.
  intros * Hlc Hc Hv Hge.
  generalize dependent gas.
  remember false as nb.
  remember (Some b) as res.
  generalize dependent b.
  induction Hv; intros;
  inversion Hc; subst;
  try destruct1;
  simpl in Hge;
  destruct gas;
  try match goal with
    [ Hx: 0 >= S _ |- _ ] =>
        inversion Hx
  end;
  try discriminate;
  eauto.
  - (* PSequence p1 p2, where p1 is nullable *)
    assert (gas >= pat_size p1 + d * (grammar_size g)) by lia.
    assert (gas >= pat_size p2 + d * (grammar_size g)) by lia.
    assert (nullable_comp g p1 gas = Some true) by eauto.
    simpl.
    rewrite_match_subject_in_goal.
    eauto.
  - (* PSequence p1 p2, where p1 is non-nullable *)
    assert (gas >= pat_size p1 + d * (grammar_size g)) by lia.
    assert (nullable_comp g p1 gas = Some false) by eauto.
    simpl.
    rewrite_match_subject_in_goal.
    eauto.
  - (* PChoice p1 p2 *)
    assert (gas >= pat_size p1 + d * (grammar_size g)) by lia.
    assert (gas >= pat_size p2 + d * (grammar_size g)) by lia.
    assert (nullable_comp g p1 gas = Some nb') by eauto.
    simpl.
    rewrite_match_subject_in_goal.
    destruct nb'.
    + (* p1 is nullable *)
      assert (b = true)
      by eauto using verifyrule_true_res_some_true.
      subst.
      eauto.
    + (* p1 is non-nullable *)
    assert (gas >= pat_size p2 + d * (grammar_size g)) by lia.
    eauto.
  - (* PRepetition p *)
    assert (b = true)
    by eauto using verifyrule_true_res_some_true.
    subst.
    simpl.
    eauto.
  - (* PNot p *)
    assert (b = true)
    by eauto using verifyrule_true_res_some_true.
    subst.
    simpl.
    eauto.
  - (* PAnd p *)
    assert (b = true)
    by eauto using verifyrule_true_res_some_true.
    subst.
    simpl.
    eauto.
  - (* PNT i *)
    destruct2sep.
    simpl.
    rewrite_match_subject_in_goal.
    match goal with
      [ Hx: nth_error ?g _ = Some ?p |- _ ] =>
        assert (pat_size p <= grammar_size g)
        by eauto using pat_size_le_grammar_size, nth_error_In;
        assert (gas >= pat_size p + d * (grammar_size g)) by lia
    end.
    eauto using lcoherent_true_In, nth_error_In.
Qed.

Lemma nullable_comp_gas_bounded :
  forall g p d b k gas,
  lcoherent g g true ->
  coherent g p true ->
  verifyrule g p d false (Some b) k ->
  gas >= pat_size p + S (Datatypes.length g) * (grammar_size g) ->
  nullable_comp g p gas = Some b.
Proof.
  intros.
  assert (exists k', verifyrule g p (S (Datatypes.length g)) false (Some b) k')
  as [? ?] by eauto using verifyrule_Some_min_depth.
  eauto using nullable_comp_gas_bounded_by_depth.
Qed.
