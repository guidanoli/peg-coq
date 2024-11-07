From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Peg Require Import Syntax.
From Peg Require Import Nullable.
From Peg Require Import Tactics.
From Peg Require Import Coherent.
From Peg Require Import Verifyrule.

(** CheckLoops predicate **)
(** Check whether a pattern has potential infinite loops **)

Inductive checkloops : grammar -> pat -> nat -> option bool -> Prop :=
  | CLEmpty :
      forall g d,
      checkloops g PEmpty d (Some false)
  | CLChar :
      forall g a d,
      checkloops g (PChar a) d (Some false)
  | CLSequenceNone :
      forall g p1 p2 d,
      checkloops g p1 d None ->
      checkloops g (PSequence p1 p2) d None
  | CLSequenceSomeTrue :
      forall g p1 p2 d,
      checkloops g p1 d (Some true) ->
      checkloops g (PSequence p1 p2) d (Some true)
  | CLSequenceSomeFalse :
      forall g p1 p2 res d,
      checkloops g p1 d (Some false) ->
      checkloops g p2 d res ->
      checkloops g (PSequence p1 p2) d res
  | CLChoiceNone :
      forall g p1 p2 d,
      checkloops g p1 d None ->
      checkloops g (PChoice p1 p2) d None
  | CLChoiceSomeTrue :
      forall g p1 p2 d,
      checkloops g p1 d (Some true) ->
      checkloops g (PChoice p1 p2) d (Some true)
  | CLChoiceSomeFalse :
      forall g p1 p2 d res,
      checkloops g p1 d (Some false) ->
      checkloops g p2 d res ->
      checkloops g (PChoice p1 p2) d res
  | CLRepetitionLR :
      forall g p d,
      nullable g p d None ->
      checkloops g (PRepetition p) d None
  | CLRepetitionNullable :
      forall g p d,
      nullable g p d (Some true) ->
      checkloops g (PRepetition p) d (Some true)
  | CLRepetitionNotNullable :
      forall g p d res,
      nullable g p d (Some false) ->
      checkloops g p d res ->
      checkloops g (PRepetition p) d res
  | CLNot :
      forall g p d res,
      checkloops g p d res ->
      checkloops g (PNot p) d res
  | CLNT :
      forall g i d,
      checkloops g (PNT i) d (Some false)
  .

Theorem checkloops_determinism :
  forall g p d b1 b2,
  checkloops g p d b1 ->
  checkloops g p d b2 ->
  b1 = b2.
Proof.
  intros * H1 H2.
  generalize dependent b2.
  induction H1; intros;
  inversion H2; subst;
  try assert (Some true = Some false) by auto;
  try assert (Some false = Some true) by auto;
  try assert (Some false = None) by auto;
  try assert (None = Some false) by auto;
  try pose_nullable_determinism;
  try discriminate;
  auto.
Qed.

Ltac pose_checkloops_determinism :=
  match goal with
    [ Hx1: checkloops ?g ?p ?d ?res1,
      Hx2: checkloops ?g ?p ?d ?res2 |- _ ] =>
          assert (res1 = res2)
          by eauto using checkloops_determinism;
          clear Hx2
  end.

Theorem checkloops_Some_S_depth :
  forall g p d b,
  checkloops g p d (Some b) ->
  checkloops g p (S d) (Some b).
Proof.
  intros * H.
  remember (Some b) as res.
  generalize dependent b.
  induction H;
  intros;
  try destruct1;
  try discriminate;
  eauto using checkloops, nullable_Some_S_depth.
Qed.

Theorem checkloops_Some_depth_le :
  forall g p d d' b,
  checkloops g p d (Some b) ->
  d <= d' ->
  checkloops g p d' (Some b).
Proof.
  intros * H Hle.
  induction Hle;
  eauto using checkloops_Some_S_depth.
Qed.

Lemma checkloops_Some_determinism :
  forall g p d1 d2 b1 b2,
  checkloops g p d1 (Some b1) ->
  checkloops g p d2 (Some b2) ->
  b1 = b2.
Proof.
  intros * H1 H2.
  destruct (Compare_dec.le_ge_dec d1 d2);
  try match goal with
    [ Hge: ?x >= ?y |- _ ] =>
        assert (y <= x) by lia
  end;
  match goal with
    [ Hx: checkloops ?g ?p ?dx (Some ?bx),
      Hle: ?dx <= ?dy |- _ ] =>
          assert (checkloops g p dy (Some bx))
          by eauto using checkloops_Some_depth_le
  end;
  match goal with
    [ Hx1: checkloops ?g ?p ?d (Some ?b1),
      Hx2: checkloops ?g ?p ?d (Some ?b2) |- _ ] =>
          assert (Some b1 = Some b2)
          by eauto using checkloops_determinism
  end;
  destruct1;
  auto.
Qed.

Lemma checkloops_safe_grammar :
  forall g p,
  (forall r, In r g -> coherent g r true) ->
  (forall r nb, In r g -> exists d b k, verifyrule g r d nb (Some b) k) ->
  coherent g p true ->
  exists d b, checkloops g p d (Some b).
Proof.
  intros * Hgc Hgv Hpc.
  induction p;
  inversion Hpc; subst;
  repeat specialize_coherent;
  repeat destruct_exists_hyp;
  try match goal with
    [ Hx1: checkloops ?g ?p1 ?d1 (Some ?b1),
      Hx2: checkloops ?g ?p2 ?d2 (Some ?b2)
      |- exists _ _, checkloops ?g (_ ?p1 ?p2) _ _ ] =>
          assert (d1 <= d1 + d2) by lia;
          assert (d2 <= d1 + d2) by lia;
          assert (checkloops g p1 (d1 + d2) (Some b1))
          by eauto using checkloops_Some_depth_le;
          assert (checkloops g p2 (d1 + d2) (Some b2))
          by eauto using checkloops_Some_depth_le;
          destruct b1;
          eauto using checkloops;
          fail
  end;
  try match goal with
    [ Hx: coherent ?g ?p true,
      Hy: checkloops ?g ?p ?d' (Some ?b')
      |- exists _ _, checkloops ?g (PRepetition ?p) _ _ ] =>
          assert (exists d b k, verifyrule g p d false (Some b) k)
          as [d [b [k ?]]] by eauto using verifyrule_safe_grammar_yields_safe_pattern;
          assert (nullable g p d (Some b))
          by eauto using verifyrule_similar_to_nullable;
          assert (d <= d + d') by lia;
          assert (d' <= d + d') by lia;
          assert (nullable g p (d + d') (Some b))
          by eauto using nullable_Some_depth_le;
          assert (checkloops g p (d + d') (Some b'))
          by eauto using checkloops_Some_depth_le;
          destruct b;
          eauto using checkloops;
          fail
  end;
  try match goal with
    [ Hx: checkloops ?g ?p ?d (Some _)
      |- exists _ _, checkloops ?g (_ ?p) _ _ ] =>
          exists d;
          eauto using checkloops;
          fail
  end;
  try (exists 1; eauto using checkloops; fail).
Qed.

Lemma checkloops_convergence :
  forall g p d d' res,
  (forall r, In r g -> coherent g r true) ->
  (forall r nb, In r g -> exists d b k, verifyrule g r d nb (Some b) k) ->
  coherent g p true ->
  length g < d ->
  checkloops g p d res ->
  d <= d' ->
  checkloops g p d' res.
Proof.
  intros * Hgc Hgv Hpc Hlt Hcl Hle.
  generalize dependent d'.
  induction Hcl;
  intros;
  inversion Hpc; subst;
  eauto using checkloops, nullable_convergence.
Qed.

Lemma checkloops_Some_convergence :
  forall g p d d' b res,
  (forall r, In r g -> coherent g r true) ->
  (forall r nb, In r g -> exists d b k, verifyrule g r d nb (Some b) k) ->
  coherent g p true ->
  checkloops g p d (Some b) ->
  length g < d' ->
  checkloops g p d' res ->
  res = Some b.
Proof.
  intros * Hgc Hgv Hpc Hc Hlt Hc'.
  destruct (Compare_dec.le_ge_dec d d');
  match goal with
  | [ _: ?d <= ?d' |- _ ] =>
      assert (checkloops g p d' (Some b))
      by eauto using checkloops_Some_depth_le
  | [ _: ?d >= ?d' |- _ ] =>
      assert (d' <= d) by lia;
      assert (checkloops g p d res)
      by eauto using checkloops_convergence
  end;
  pose_checkloops_determinism;
  subst;
  eauto.
Qed.

(** CheckLoops function **)

Fixpoint checkloops_comp g p d gas {struct gas} :=
  match gas with
  | O => None
  | S gas' => match p with
              | PEmpty => Some (Some false)
              | PChar _ => Some (Some false)
              | PSequence p1 p2 => match checkloops_comp g p1 d gas' with
                                   | Some (Some false) => checkloops_comp g p2 d gas'
                                   | res => res
                                   end
              | PChoice p1 p2 => match checkloops_comp g p1 d gas' with
                                 | Some (Some false) => checkloops_comp g p2 d gas'
                                 | res => res
                                 end
              | PRepetition p' => match nullable_comp g p' d gas' with
                                  | Some (Some false) => checkloops_comp g p' d gas'
                                  | res => res
                                  end
              | PNot p' => checkloops_comp g p' d gas'
              | PNT _ => Some (Some false)
              end
  end.

Lemma checkloops_comp_soundness :
  forall g p d gas res,
  checkloops_comp g p d gas = Some res ->
  checkloops g p d res.
Proof.
  intros * H.
  generalize dependent res.
  generalize dependent d.
  generalize dependent p.
  generalize dependent g.
  induction gas; try discriminate; intros.
  destruct p;
  simpl in H;
  repeat destruct_match_subject_in_hyp;
  try destruct1;
  try discriminate;
  eauto using checkloops, nullable_comp_soundness.
Qed.

Lemma checkloops_comp_S_gas :
  forall g p d gas res,
  checkloops_comp g p d gas = Some res ->
  checkloops_comp g p d (S gas) = Some res.
Proof.
  intros * H.
  generalize dependent res.
  generalize dependent d.
  generalize dependent p.
  generalize dependent g.
  induction gas; try discriminate; intros.
  destruct p;
  simpl in H;
  repeat destruct_match_subject_in_hyp;
  try destruct1;
  try discriminate;
  remember (S gas) as gas';
  repeat match goal with
    [ Hx: checkloops_comp _ _ _ gas = Some _ |- _ ] =>
        apply IHgas in Hx
  end;
  try match goal with
    [ Hx: nullable_comp _ _ _ gas = Some _ |- _ ] =>
        apply nullable_comp_S_gas in Hx
  end;
  simpl;
  subst;
  try rewrite_match_subject_in_goal;
  eauto.
Qed.

Lemma checkloops_comp_le_gas :
  forall g p d gas gas' res,
  checkloops_comp g p d gas = Some res ->
  gas <= gas' ->
  checkloops_comp g p d gas' = Some res.
Proof.
  intros * H Hle.
  induction Hle;
  eauto using checkloops_comp_S_gas.
Qed.

Lemma checkloops_comp_termination :
  forall g p d,
  (forall r, In r g -> coherent g r true) ->
  coherent g p true ->
  exists gas res,
  checkloops_comp g p d gas = Some res.
Proof.
  intros * Hgc Hpc.
  induction p; intros;
  inversion Hpc; subst;
  repeat specialize_coherent;
  repeat destruct_exists_hyp;
  (* 2 recursive calls *)
  try match goal with
    [ Hx1: checkloops_comp ?g ?p1 ?d ?gas1 = Some ?res1,
      Hx2: checkloops_comp ?g ?p2 ?d ?gas2 = Some ?res2 |- _ ] =>
          assert (gas1 <= gas1 + gas2) by lia;
          assert (gas2 <= gas1 + gas2) by lia;
          assert (checkloops_comp g p1 d (gas1 + gas2) = Some res1)
          as Hx1' by eauto using checkloops_comp_le_gas;
          assert (checkloops_comp g p2 d (gas1 + gas2) = Some res2)
          by eauto using checkloops_comp_le_gas;
          exists (1 + gas1 + gas2);
          destruct res1 as [[|]|];
          simpl;
          rewrite Hx1';
          eauto;
          fail
  end;
  (* 1 recursive call + nullable_comp *)
  try match goal with
    [ Hx1: checkloops_comp ?g ?p1 ?d ?gas1 = Some ?res1 |- _ ] =>
        assert (exists gas res, nullable_comp g p1 d gas = Some res)
        as [gas2 [res2 ?]] by eauto using nullable_comp_termination;
        assert (gas1 <= gas1 + gas2) by lia;
        assert (gas2 <= gas1 + gas2) by lia;
        assert (checkloops_comp g p1 d (gas1 + gas2) = Some res1)
        as Hx1' by eauto using checkloops_comp_le_gas;
        assert (nullable_comp g p1 d (gas1 + gas2) = Some res2)
        as Hx2' by eauto using nullable_comp_le_gas;
        exists (1 + gas1 + gas2);
        simpl;
        rewrite Hx2';
        destruct res2 as [[|]|];
        eauto;
        fail
  end;
  (* 1 recursive call *)
  try match goal with
    [ Hx1: checkloops_comp ?g ?p1 ?d ?gas1 = Some ?res1 |- _ ] =>
        exists (1 + gas1);
        simpl;
        eauto;
        fail
  end;
  (* 0 recursive calls *)
  try (exists 1; simpl; eauto; fail).
Qed.

Ltac specialize_checkloops :=
  match goal with
    [ Hx: checkloops ?g ?p _ ?b, IHx: forall d, checkloops ?g ?p d ?b -> _ |- _ ] =>
        specialize (IHx _ Hx)
  end.

Lemma checkloops_comp_gas_bounded :
  forall g p gas d,
  (forall r, In r g -> coherent g r true) ->
  coherent g p true ->
  gas >= pat_size p + d * (grammar_size g) ->
  exists res,
  checkloops_comp g p d gas = Some res.
Proof.
  intros * Hgc Hpc Hge.
  generalize dependent gas.
  induction p; intros;
  inversion Hpc; subst;
  simpl in Hge;
  destruct gas;
  try match goal with
    [ Hx: 0 >= S _ |- _ ] =>
        inversion Hx
  end;
  try match goal with
    [ |- exists _, _ ?g (_ ?p) ?d (S ?gas) = _ ] =>
        assert (gas >= pat_size p + d * grammar_size g) by lia
  end;
  try match goal with
    [ |- exists _, _ ?g (_ ?p _) ?d (S ?gas) = _ ] =>
        assert (gas >= pat_size p + d * grammar_size g) by lia
  end;
  simpl;
  eauto.
  - (* PSequence p1 p2 *)
    assert (exists res, checkloops_comp g p1 d gas = Some res)
    as [res1 Hclp1] by eauto.
    assert (exists res, checkloops_comp g p2 d gas = Some res)
    as [? ?] by eauto.
    rewrite Hclp1.
    destruct res1 as [[|]|]; eauto.
  - (* PChoice p1 p2 *)
    assert (exists res, checkloops_comp g p1 d gas = Some res)
    as [res1 Hclp1] by eauto.
    assert (exists res, checkloops_comp g p2 d gas = Some res)
    as [? ?] by eauto.
    rewrite Hclp1.
    destruct res1 as [[|]|]; eauto.
  - (* PRepetition p *)
    assert (exists res, nullable_comp g p d gas = Some res)
    as [res Hnp] by eauto using nullable_comp_gas_bounded.
    rewrite Hnp.
    destruct res as [[|]|]; eauto.
Qed.

(** CheckLoops for lists of patterns

    Assumes all rules in g and rs are coherent and not left-recursive

    lcheckloops g rs true === some rule in rs has an empty loop
    lcheckloops g rs false === no rule in rs has an empty loop

**)

Inductive lcheckloops : grammar -> list pat -> bool -> Prop :=
  | LCLNil :
      forall g,
      lcheckloops g nil false
  | LCLConsSomeTrue :
      forall g r d rs,
      checkloops g r d (Some true) ->
      lcheckloops g (cons r rs) true
  | LCLConsSomeFalse :
      forall g r d rs b,
      checkloops g r d (Some false) ->
      lcheckloops g rs b ->
      lcheckloops g (cons r rs) b
  .

Lemma lcheckloops_determinism :
  forall g rs b1 b2,
  lcheckloops g rs b1 ->
  lcheckloops g rs b2 ->
  b1 = b2.
Proof.
  intros * H1 H2.
  generalize dependent b2.
  induction H1; intros;
  inversion H2; subst;
  try match goal with
    [ Hx1: checkloops ?g ?r ?d1 (Some ?b1),
      Hx2: checkloops ?g ?r ?d2 (Some ?b2) |- _ ] =>
          assert (b1 = b2)
          by eauto using checkloops_Some_determinism
  end;
  try discriminate;
  auto.
Qed.

Lemma lcheckloops_false_In :
  forall g rs r,
  lcheckloops g rs false ->
  In r rs ->
  exists d,
  checkloops g r d (Some false).
Proof.
  intros * Hcl HIn.
  generalize dependent r.
  generalize dependent g.
  induction rs;
  intros.
  - (* nil *)
    exfalso.
    eauto using in_nil.
  - (* cons r rs *)
    inversion Hcl; subst.
    simpl in HIn.
    destruct HIn;
    subst;
    eauto.
Qed.

Fixpoint lcheckloops_comp g rs gas :=
  match rs with
  | nil => Some false
  | cons r rs' => match checkloops_comp g r (S (length g)) gas with
                  | Some (Some false) => lcheckloops_comp g rs' gas
                  | Some (Some true) => Some true
                  | _ => None
                  end
  end.

Lemma lcheckloops_comp_soundness :
  forall g rs gas b,
  lcheckloops_comp g rs gas = Some b ->
  lcheckloops g rs b.
Proof.
  intros * H.
  generalize dependent b.
  generalize dependent gas.
  generalize dependent g.
  induction rs;
  intros;
  simpl in H.
  - (* nil *)
    destruct1.
    eauto using lcheckloops.
  - (* cons r rs *)
    match goal with
      [ Hx: match ?x with | _ => _ end = _ |- _ ] =>
          destruct x as [[[|]|]|] eqn:?;
          try destruct1;
          try discriminate;
          try match goal with
            [ Hx: checkloops_comp ?g ?r ?d ?gas = Some ?res |- _ ] =>
                assert (checkloops g r d res)
                by eauto using checkloops_comp_soundness
          end;
          eauto using lcheckloops
    end.
Qed.

Lemma lcheckloops_comp_S_gas :
  forall g rs gas b,
  lcheckloops_comp g rs gas = Some b ->
  lcheckloops_comp g rs (S gas) = Some b.
Proof.
  intros * H.
  generalize dependent b.
  generalize dependent gas.
  generalize dependent g.
  induction rs;
  intros;
  simpl in H.
  - (* nil *)
    destruct1.
    auto.
  - (* cons r rs *)
    match goal with
      [ Hx: match ?x with | _ => _ end = _ |- _ ] =>
          destruct x as [[[|]|]|] eqn:?;
          try discriminate;
          try destruct1;
          try match goal with
            [ Hx: checkloops_comp ?g ?r ?d ?gas = Some ?res |- _ ] =>
                assert (checkloops_comp g r d (S gas) = Some res)
                as ? by eauto using checkloops_comp_S_gas;
                unfold lcheckloops_comp;
                rewrite_match_subject_in_goal;
                fold lcheckloops_comp;
                eauto
          end
    end.
Qed.

Lemma lcheckloops_comp_le_gas :
  forall g rs gas1 gas2 b,
  lcheckloops_comp g rs gas1 = Some b ->
  gas1 <= gas2 ->
  lcheckloops_comp g rs gas2 = Some b.
Proof.
  intros * H Hle.
  induction Hle;
  eauto using lcheckloops_comp_S_gas.
Qed.

Lemma lcheckloops_comp_termination :
  forall g rs,
  lcoherent g g true ->
  lcoherent g rs true ->
  lverifyrule g g true ->
  exists gas b,
  lcheckloops_comp g rs gas = Some b.
Proof.
  intros * Hgc Hrsc Hgv.
  induction rs as [|r rs];
  intros.
  - (* nil *)
    exists 0.
    simpl.
    eauto.
  - (* cons r rs *)
    inversion Hrsc; subst.
    match goal with
      [ Hx: lcoherent ?g ?rs true -> _, Hy: lcoherent ?g ?rs true |- _ ] =>
          specialize (Hx Hy) as [gas1 [resrs ?]]
    end.
    assert (exists d b, checkloops g r d (Some b))
    as [d [b ?]]
    by eauto using checkloops_safe_grammar, lcoherent_true_In, lverifyrule_true_In.
    assert (exists gas res, checkloops_comp g r (S (length g)) gas = Some res)
    as [gas2 [res Hcl]]
    by eauto using checkloops_comp_termination, lcoherent_true_In.
    assert (checkloops g r (S (length g)) res)
    by eauto using checkloops_comp_soundness.
    assert (res = Some b)
    by eauto using checkloops_Some_convergence, lcoherent_true_In, lverifyrule_true_In.
    subst res.
    simpl.
    assert (gas1 <= gas1 + gas2) by lia.
    assert (gas2 <= gas1 + gas2) by lia.
    assert (lcheckloops_comp g rs (gas1 + gas2) = Some resrs)
    as Hlcl' by eauto using lcheckloops_comp_le_gas.
    assert (checkloops_comp g r (S (length g)) (gas1 + gas2) = Some (Some b))
    as Hcl' by eauto using checkloops_comp_le_gas.
    exists (gas1 + gas2).
    rewrite Hcl'.
    destruct b;
    eauto.
Qed.

Lemma lcheckloops_comp_gas_bounded :
  forall g rs gas,
  lcoherent g g true ->
  lcoherent g rs true ->
  lverifyrule g g true ->
  gas >= grammar_size rs + S (length g) * (grammar_size g) ->
  exists b, lcheckloops_comp g rs gas = Some b.
Proof.
  intros * Hgc Hrsc Hgv Hge.
  generalize dependent gas.
  induction rs as [|r rs];
  intros;
  inversion Hrsc; subst;
  simpl;
  eauto.
  simpl in Hge.
  assert (gas >= grammar_size rs + S (length g) * grammar_size g) by lia.
  assert (exists b, lcheckloops_comp g rs gas = Some b) as [? ?] by eauto.
  assert (gas >= pat_size r + S (length g) * grammar_size g) by lia.
  assert (exists b, checkloops_comp g r (S (length g)) gas = Some b)
  as [clres Hcl] by eauto using checkloops_comp_gas_bounded, lcoherent_true_In.
  rewrite Hcl.
  assert (exists d b, checkloops g r d (Some b))
  as [d [b ?]]
  by eauto using checkloops_safe_grammar, lcoherent_true_In, lverifyrule_true_In.
  assert (checkloops g r (S (length g)) clres)
  by eauto using checkloops_comp_soundness.
  assert (clres = Some b)
  by eauto using checkloops_Some_convergence, lcoherent_true_In, lverifyrule_true_In.
  subst clres.
  destruct b; eauto.
Qed.
