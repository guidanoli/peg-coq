From Coq Require Import Lia.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Peg Require Import Syntax.
From Peg Require Import Match.
From Peg Require Import Coherent.
From Peg Require Import Verifyrule.
From Peg Require Import Checkloops.
From Peg Require Import Tactics.
From Peg Require Import Strong.
From Peg Require Import Suffix.
From Peg Require Import Nullable.

(** Verify Grammar

    verifygrammar g true === all rules are coherent, non-LR, and void of empty loops
    verifygrammar g false === some rules is either incoherent, LR, or has an empty loop

**)

Inductive verifygrammar : grammar -> bool -> Prop :=
  | VGIncoherent :
      forall g,
      lcoherent g g false ->
      verifygrammar g false
  | VGLeftRecursive :
      forall g,
      lcoherent g g true ->
      lverifyrule g g false ->
      verifygrammar g false
  | VGEmptyLoops :
      forall g,
      lcoherent g g true ->
      lverifyrule g g true ->
      lcheckloops g g true ->
      verifygrammar g false
  | VGSafe :
      forall g,
      lcoherent g g true ->
      lverifyrule g g true ->
      lcheckloops g g false ->
      verifygrammar g true
  .

Lemma verifygrammar_determinism :
  forall g b1 b2,
  verifygrammar g b1 ->
  verifygrammar g b2 ->
  b1 = b2.
Proof.
  intros * H1 H2.
  generalize dependent b2.
  induction H1;
  intros;
  inversion H2; subst;
  eauto using verifygrammar,
              lcoherent_determinism,
              lverifyrule_determinism,
              lcheckloops_determinism.
Qed.

Definition verifygrammar_comp g gas :=
  match lcoherent_func g g with
  | true => match lverifyrule_comp g g gas with
            | Some true => match lcheckloops_comp g g gas with
                           | Some false => Some true
                           | Some true => Some false
                           | None => None
                           end
            | res => res
            end
  | false => Some false
  end.

Lemma verifygrammar_comp_soundness :
  forall g gas b,
  verifygrammar_comp g gas = Some b ->
  verifygrammar g b.
Proof.
  intros * H.
  unfold verifygrammar_comp in H.
  repeat (destruct_match_subject_in_hyp; try discriminate);
  try destruct1;
  eauto using verifygrammar,
              lcoherent_func_soundness,
              lverifyrule_comp_soundness,
              lcheckloops_comp_soundness.
Qed.

Lemma verifygrammar_comp_S_gas :
  forall g gas b,
  verifygrammar_comp g gas = Some b ->
  verifygrammar_comp g (S gas) = Some b.
Proof.
  intros * H.
  unfold verifygrammar_comp in *.
  repeat (destruct_match_subject_in_hyp; try discriminate);
  try destruct1;
  auto;
  try match goal with
    [ Hx: lverifyrule_comp ?g ?g ?gas = Some ?b |- _ ] =>
        let H := fresh in (
          assert (lverifyrule_comp g g (S gas) = Some b)
          as H
          by eauto using lverifyrule_comp_S_gas;
          rewrite H;
          auto
        )
  end;
  try match goal with
    [ Hx: lcheckloops_comp ?g ?g ?gas = Some ?b |- _ ] =>
        let H := fresh in (
          assert (lcheckloops_comp g g (S gas) = Some b)
          as H
          by eauto using lcheckloops_comp_S_gas;
          rewrite H;
          auto
        )
  end.
Qed.

Lemma verifygrammar_comp_le_gas :
  forall g gas1 gas2 b,
  verifygrammar_comp g gas1 = Some b ->
  gas1 <= gas2 ->
  verifygrammar_comp g gas2 = Some b.
Proof.
  intros * H Hle.
  induction Hle;
  eauto using verifygrammar_comp_S_gas.
Qed.

Lemma verifygrammar_comp_termination :
  forall g,
  exists gas b,
  verifygrammar_comp g gas = Some b.
Proof.
  intros.
  unfold verifygrammar_comp.
  destruct (lcoherent_func g g) eqn:Hc;
  apply lcoherent_func_soundness in Hc as ?.
  + (* true *)
    assert (exists gas b, lverifyrule_comp g g gas = Some b)
    as [gasv [bv Hv]]
    by eauto using lverifyrule_comp_termination.
    assert (lverifyrule g g bv)
    by eauto using lverifyrule_comp_soundness.
    destruct bv.
    - (* true *)
      assert (exists gas b, lcheckloops_comp g g gas = Some b)
      as [gasl [bl Hl]]
      by eauto using lcheckloops_comp_termination.
      assert (lcheckloops g g bl)
      by eauto using lcheckloops_comp_soundness.
      pose (gasv + gasl) as gas.
      assert (gasv <= gas) by lia.
      assert (gasl <= gas) by lia.
      exists gas.
      assert (lverifyrule_comp g g gas = Some true)
      as Hv'
      by eauto using lverifyrule_comp_le_gas.
      rewrite Hv'.
      assert (lcheckloops_comp g g gas = Some bl)
      as Hl'
      by eauto using lcheckloops_comp_le_gas.
      rewrite Hl'.
      destruct bl;
      eauto.
    - (* false *)
      exists gasv.
      assert (lverifyrule_comp g g gasv = Some false)
      as Hv'
      by eauto using lverifyrule_comp_le_gas.
      rewrite Hv'.
      eauto.
  + (* false *)
    exists 0.
    eauto.
Qed.

Lemma verifygrammar_comp_gas_bounded :
  forall g gas,
  gas >= grammar_size g + S (Datatypes.length g) * grammar_size g ->
  exists b, verifygrammar_comp g gas = Some b.
Proof.
  intros.
  unfold verifygrammar_comp.
  destruct (lcoherent_func g g) eqn:?; eauto.
  assert (lcoherent g g true)
  by eauto using lcoherent_func_soundness.
  assert (gas >= grammar_size g + S (length g) * grammar_size g) by lia.
  assert (exists b, lverifyrule_comp g g gas = Some b)
  as [reslv Hlv] by eauto using lverifyrule_comp_gas_bounded.
  rewrite Hlv.
  destruct reslv; eauto.
  assert (lverifyrule g g true)
  by eauto using lverifyrule_comp_soundness.
  assert (exists b, lcheckloops_comp g g gas = Some b)
  as [reslcl Hlcl] by eauto using lcheckloops_comp_gas_bounded.
  rewrite Hlcl.
  destruct reslcl; eauto.
Qed.

(** Verify Grammar and initial pattern

    verifygrammarpat g p true === grammar is safe, and pattern is coherent and has no empty loops
    verifygrammarpat g p false === grammar is unsafe, or pattern is incoherent or has an empty loop

**)

Inductive verifygrammarpat : grammar -> pat -> bool -> Prop :=
  | VGPGrammar :
      forall g p,
      verifygrammar g false ->
      verifygrammarpat g p false
  | VGPIncoherentPat :
      forall g p,
      verifygrammar g true ->
      coherent g p false ->
      verifygrammarpat g p false
  | VGPPatWithEmptyLoop :
      forall g p d,
      verifygrammar g true ->
      coherent g p true ->
      checkloops g p d (Some true) ->
      verifygrammarpat g p false
  | VGPSafe :
      forall g p d,
      verifygrammar g true ->
      coherent g p true ->
      checkloops g p d (Some false) ->
      verifygrammarpat g p true
  .

Lemma verifygrammarpat_determinism :
  forall g p b1 b2,
  verifygrammarpat g p b1 ->
  verifygrammarpat g p b2 ->
  b1 = b2.
Proof.
  intros * H1 H2.
  generalize dependent b2.
  induction H1;
  intros;
  inversion H2; subst;
  eauto using verifygrammar_determinism,
              coherent_determinism,
              checkloops_determinism,
              checkloops_Some_determinism.
Qed.

Definition verifygrammarpat_comp g p gas :=
  match verifygrammar_comp g gas with
  | Some true => match coherent_func g p with
                 | true => match checkloops_comp g p (S (length g)) gas with
                           | Some (Some false) => Some true
                           | Some (Some true) => Some false
                           | _ => None
                           end
                 | false => Some false
                 end
  | res => res
  end.

Lemma verifygrammarpat_comp_soundness :
  forall g p gas b,
  verifygrammarpat_comp g p gas = Some b ->
  verifygrammarpat g p b.
Proof.
  intros * H.
  unfold verifygrammarpat_comp in H;
  repeat (destruct_match_subject_in_hyp; try discriminate);
  try destruct1;
  eauto using verifygrammarpat,
              verifygrammar_comp_soundness,
              coherent_func_soundness,
              checkloops_comp_soundness.
Qed.

Lemma verifygrammarpat_comp_S_gas :
  forall g p gas b,
  verifygrammarpat_comp g p gas = Some b ->
  verifygrammarpat_comp g p (S gas) = Some b.
Proof.
  intros * H.
  unfold verifygrammarpat_comp in *;
  repeat (destruct_match_subject_in_hyp; try discriminate);
  try destruct1;
  try match goal with
    [ Hx: verifygrammar_comp ?g ?gas = Some ?b |- _ ] =>
        let H := fresh in (
          assert (verifygrammar_comp g (S gas) = Some b)
          as H
          by eauto using verifygrammar_comp_S_gas;
          rewrite H;
          auto
        )
  end;
  try match goal with
    [ Hx: checkloops_comp ?g ?p ?d ?gas = Some ?b |- _ ] =>
        let H := fresh in (
          assert (checkloops_comp g p d (S gas) = Some b)
          as H
          by eauto using checkloops_comp_S_gas;
          rewrite H;
          auto
        )
  end.
Qed.

Lemma verifygrammarpat_comp_le_gas :
  forall g p gas1 gas2 b,
  verifygrammarpat_comp g p gas1 = Some b ->
  gas1 <= gas2 ->
  verifygrammarpat_comp g p gas2 = Some b.
Proof.
  intros * H Hle.
  induction Hle;
  eauto using verifygrammarpat_comp_S_gas.
Qed.

Lemma verifygrammarpat_comp_termination :
  forall g p,
  exists gas b,
  verifygrammarpat_comp g p gas = Some b.
Proof.
  intros.
  unfold verifygrammarpat_comp.
  assert (exists gas b, verifygrammar_comp g gas = Some b)
  as [gasvg [bvg Hvgc]]
  by eauto using verifygrammar_comp_termination.
  assert (verifygrammar g bvg)
  as Hvg
  by eauto using verifygrammar_comp_soundness.
  destruct bvg.
  - (* true *)
    inversion Hvg; subst.
    destruct (coherent_func g p) eqn:Hcp;
    apply coherent_func_soundness in Hcp as ?.
    + (* true *)
      pose (S (length g)) as d.
      assert (exists gas b, checkloops_comp g p d gas = Some b)
      as [gasl [rescl ?]]
      by eauto using checkloops_comp_termination, lcoherent_true_In.
      assert (checkloops g p d rescl)
      by eauto using checkloops_comp_soundness.
      assert (exists d b, checkloops g p d (Some b))
      as [d' [bl' ?]]
      by eauto using checkloops_safe_grammar, lcoherent_true_In, lverifyrule_true_In.
      assert (rescl = Some bl')
      by eauto using checkloops_Some_convergence, lcoherent_true_In, lverifyrule_true_In.
      subst rescl.
      pose (gasvg + gasl) as gas.
      assert (gasvg <= gas) by lia.
      assert (gasl <= gas) by lia.
      exists gas.
      assert (verifygrammar_comp g gas = Some true)
      as Hv'
      by eauto using verifygrammar_comp_le_gas.
      rewrite Hv'.
      assert (checkloops_comp g p d gas = Some (Some bl'))
      as Hl'
      by eauto using checkloops_comp_le_gas.
      subst d.
      rewrite Hl'.
      destruct bl';
      eauto.
    + (* false *)
      exists gasvg.
      assert (verifygrammar_comp g gasvg = Some true)
      as Hv'
      by eauto using verifygrammar_comp_le_gas.
      rewrite Hv'.
      eauto.
  - (* false *)
    exists gasvg.
    rewrite Hvgc.
    eauto.
Qed.

Definition verifygrammarpat_comp_min_gas g p :=
  pat_size p + grammar_size g + S (Datatypes.length g) * grammar_size g.

Lemma verifygrammarpat_comp_gas_bounded :
  forall g p gas,
  gas >= verifygrammarpat_comp_min_gas g p ->
  exists b, verifygrammarpat_comp g p gas = Some b.
Proof.
  intros.
  unfold verifygrammarpat_comp.
  unfold verifygrammarpat_comp_min_gas in H.
  assert (gas >= grammar_size g + S (Datatypes.length g) * grammar_size g) by lia.
  assert (exists b, verifygrammar_comp g gas = Some b)
  as [resvg Hvgc] by eauto using verifygrammar_comp_gas_bounded.
  rewrite Hvgc.
  destruct resvg; eauto.
  assert (verifygrammar g true)
  as Hvg by eauto using verifygrammar_comp_soundness.
  inversion Hvg; subst.
  destruct (coherent_func g p) eqn:?; eauto.
  assert (coherent g p true)
  by eauto using coherent_func_soundness.
  assert (gas >= pat_size p + S (length g) * grammar_size g) by lia.
  assert (exists b, checkloops_comp g p (S (length g)) gas = Some b)
  as [rescl Hcl] by eauto using checkloops_comp_gas_bounded, lcoherent_true_In.
  assert (exists d b, checkloops g p d (Some b))
  as [d [b ?]]
  by eauto using checkloops_safe_grammar, lcoherent_true_In, lverifyrule_true_In.
  assert (checkloops g p (S (length g)) rescl)
  by eauto using checkloops_comp_soundness.
  assert (rescl = Some b)
  by eauto using checkloops_Some_convergence, lcoherent_true_In, lverifyrule_true_In.
  rewrite Hcl.
  destruct rescl as [[|]|]; eauto.
Qed.

Definition verifygrammarpat_func g p :=
  let gas := verifygrammarpat_comp_min_gas g p in
  match (verifygrammarpat_comp g p gas) with
  | Some b => b
  | None => false
  end.

Lemma verifygrammarpat_func_correct :
  forall g p b,
  verifygrammarpat_func g p = b <-> verifygrammarpat g p b.
Proof.
  intros.
  unfold verifygrammarpat_func.
  remember (verifygrammarpat_comp_min_gas g p) as gas.
  assert (exists b, verifygrammarpat_comp g p gas = Some b)
  as [b' Hvgp] by (eapply verifygrammarpat_comp_gas_bounded; lia).
  rewrite Hvgp.
  assert (verifygrammarpat g p b')
  by eauto using verifygrammarpat_comp_soundness.
  split; intro.
  - (* -> *)
    subst.
    eauto using verifygrammarpat_comp_soundness.
  - (* <- *)
    eauto using verifygrammarpat_determinism.
Qed.

Theorem safe_match :
  forall g p d s,
  (forall r, In r g -> coherent g r true) ->
  (forall r nb, In r g -> exists d b k, verifyrule g r d nb (Some b) k) ->
  (forall r, In r g -> exists d, checkloops g r d (Some false)) ->
  coherent g p true ->
  checkloops g p d (Some false) ->
  exists res, matches g p s res.
Proof.
  intros * Hcg Hvg Hclg Hcp Hclp.
  remember (String.length s) as n.
  generalize dependent s.
  generalize dependent d.
  generalize dependent p.
  generalize dependent g.
  induction n using strong_induction;
  intros.
  assert (exists nb d' b k, verifyrule g p d' nb (Some b) k)
  as [nb [? [b [? Hvp]]]]
  by (exists true; eauto using verifyrule_safe_grammar_yields_safe_pattern).
  remember (Some b) as res in Hvp.
  generalize dependent b.
  generalize dependent s.
  generalize dependent d.
  generalize dependent n.
  induction Hvp;
  intros;
  inversion Hcp; subst;
  inversion Hclp; subst;
  try destruct1;
  try discriminate.
  - (* PEmpty *)
    eauto using matches.
  - (* PSet f *)
    destruct s;
    try match goal with
      [ |- exists _, matches _ (PSet ?f) (String ?a _) _ ] =>
        destruct (f a) eqn:?;
        subst
    end;
    eauto using matches.
  - (* PSequence p1 p2, with nullable p1 *)
    assert (exists res, matches g p1 s res) as [res1 ?] by eauto.
    destruct res1 as [|s'];
    eauto using matches.
    assert (suffix s' s)
    as Hsuffix
    by eauto using matches_suffix.
    destruct Hsuffix;
    match goal with
    | [ _: matches _ _ ?s (Success ?s) |- _ ] =>
          assert (exists res, matches g p2 s res) as [? ?] by eauto
    | [ _: matches _ _ (String ?a ?s) (Success ?s'),
        _: suffix ?s' ?s |- _ ] =>
          assert (exists res, matches g p2 s1 res)
          as [? ?]
          by eauto using
          suffix_is_proper_suffix_with_char,
          proper_suffix_length_lt
    end;
    eauto using matches.
  - (* PSequence p1 p2, with non-nullable p1 *)
    match goal with
      [ _: verifyrule ?g p1 ?d false (Some false) _ |- _ ] =>
          assert (nullable g p1 d (Some false))
          by eauto using verifyrule_similar_to_nullable
    end.
    assert (exists res, matches g p1 s res) as [res1 ?] by eauto.
    destruct res1 as [|s'];
    eauto using matches.
    assert (exists res, matches g p2 s' res)
    as [? ?]
    by eauto using
    proper_suffix_length_lt,
    nullable_Some_false_proper_suffix.
    eauto using matches.
  - (* PChoice p1 p2 *)
    assert (exists res, matches g p1 s res) as [res1 ?] by eauto.
    destruct res1 as [|s'];
    eauto using matches.
    assert (exists res, matches g p2 s res) as [? ?] by eauto.
    eauto using matches.
  - (* PRepetition p *)
    assert (exists res, matches g p s res) as [res ?] by eauto.
    destruct res as [|s'];
    eauto using matches.
    assert (exists res, matches g (PRepetition p) s' res)
    as [? ?]
    by eauto using
    proper_suffix_length_lt,
    nullable_Some_false_proper_suffix.
    eauto using matches.
  - (* PNot p *)
    assert (exists res, matches g p s res) as [res ?] by eauto.
    destruct res as [|s'];
    eauto using matches.
  - (* PNT i *)
    assert (In p g) by eauto using nth_error_In.
    assert (exists d, checkloops g p d (Some false))
    as [? ?] by eauto.
    assert (exists res, matches g p s res) as [? ?] by eauto.
    eauto using matches.
Qed.

Theorem lpredicates_safe_match :
  forall g p d s,
  lcoherent g g true ->
  lverifyrule g g true ->
  lcheckloops g g false ->
  coherent g p true ->
  checkloops g p d (Some false) ->
  exists res, matches g p s res.
Proof.
  eauto using safe_match, lcoherent_true_In, lverifyrule_true_In, lcheckloops_false_In.
Qed.

Theorem verifygrammar_safe_match :
  forall g p d s,
  verifygrammar g true ->
  coherent g p true ->
  checkloops g p d (Some false) ->
  exists res, matches g p s res.
Proof.
  intros * Hvg Hpc Hlp.
  inversion Hvg; subst.
  eauto using lpredicates_safe_match.
Qed.

Theorem verifygrammarpat_safe_match :
  forall g p s,
  verifygrammarpat g p true ->
  exists res, matches g p s res.
Proof.
  intros * Hvgp.
  inversion Hvgp; subst.
  eauto using verifygrammar_safe_match.
Qed.

Theorem verifygrammarpat_func_safe_match :
  forall g p s,
  verifygrammarpat_func g p = true ->
  exists res, matches g p s res.
Proof.
  intros * Hvgp.
  rewrite verifygrammarpat_func_correct in Hvgp.
  eauto using verifygrammarpat_safe_match.
Qed.

Theorem verifygrammarpat_verifyrule :
  forall g p,
  verifygrammarpat g p true ->
  exists nb d b k, verifyrule g p d nb (Some b) k.
Proof.
  intros * H.
  inversion H; subst.
  match goal with
    [ Hx: verifygrammar _ true |- _ ] =>
        inversion Hx; subst
  end.
  exists true.
  eauto using verifyrule_safe_grammar_yields_safe_pattern,
              lcoherent_true_In,
              lverifyrule_true_In.
Qed.
