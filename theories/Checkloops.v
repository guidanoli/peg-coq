From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Peg Require Import Syntax.
From Peg Require Import Nullable.
From Peg Require Import Tactics.
From Peg Require Import Coherent.
From Peg Require Import Verifyrule.

(** CheckLoops predicate **)
(** Check whether a pattern has potential infinite loops **)

Inductive checkloops : grammar -> pat -> bool -> Prop :=
  | CLEmpty :
      forall g,
      checkloops g PEmpty false
  | CLSet :
      forall g f,
      checkloops g (PSet f) false
  | CLSequenceTrue :
      forall g p1 p2,
      checkloops g p1 true ->
      checkloops g (PSequence p1 p2) true
  | CLSequenceFalse :
      forall g p1 p2 b,
      checkloops g p1 false ->
      checkloops g p2 b ->
      checkloops g (PSequence p1 p2) b
  | CLChoiceTrue :
      forall g p1 p2,
      checkloops g p1 true ->
      checkloops g (PChoice p1 p2) true
  | CLChoiceFalse :
      forall g p1 p2 b,
      checkloops g p1 false ->
      checkloops g p2 b ->
      checkloops g (PChoice p1 p2) b
  | CLRepetitionNullable :
      forall g p,
      nullable g p true ->
      checkloops g (PRepetition p) true
  | CLRepetitionNotNullable :
      forall g p b,
      nullable g p false ->
      checkloops g p b ->
      checkloops g (PRepetition p) b
  | CLNot :
      forall g p b,
      checkloops g p b ->
      checkloops g (PNot p) b
  | CLNT :
      forall g i,
      checkloops g (PNT i) false
  .

Theorem checkloops_determinism :
  forall g p b1 b2,
  checkloops g p b1 ->
  checkloops g p b2 ->
  b1 = b2.
Proof.
  intros * H1 H2.
  generalize dependent b2.
  induction H1; intros;
  inversion H2; subst;
  try pose_nullable_determinism;
  try assert (true = false) by auto;
  try assert (false = true) by auto;
  try discriminate;
  auto.
Qed.

Ltac pose_checkloops_determinism :=
  match goal with
    [ Hx1: checkloops ?g ?p ?b1,
      Hx2: checkloops ?g ?p ?b2 |- _ ] =>
          assert (b1 = b2)
          by eauto using checkloops_determinism;
          clear Hx2
  end.

Lemma checkloops_safe_grammar :
  forall g p,
  lcoherent g g true ->
  lverifyrule g g true ->
  coherent g p true ->
  exists b, checkloops g p b.
Proof.
  intros * Hgc Hgv Hpc.
  induction p;
  inversion Hpc; subst;
  try match goal with
    [ |- exists b, checkloops ?g (_ ?p1 ?p2) b ] =>
        assert (exists b, checkloops g p1 b) as [[|] ?] by eauto;
        assert (exists b, checkloops g p2 b) as [? ?] by eauto
  end;
  try match goal with
    [ |- exists b, checkloops ?g (_ ?p) b ] =>
        assert (exists b, checkloops g p b) as [? ?] by eauto
  end;
  try match goal with
    [ |- exists bx, checkloops ?g (PRepetition ?p) bx ] =>
        assert (exists d b k, verifyrule g p d false (Some b) k)
        as [d [b [k ?]]] by eauto using
        verifyrule_safe_grammar_yields_safe_pattern,
        lcoherent_true_In,
        lverifyrule_true_In;
        assert (nullable g p b)
        by eauto using verifyrule_similar_to_nullable;
        destruct b
  end;
  eauto using checkloops.
Qed.

(** CheckLoops function **)

Fixpoint checkloops_comp g p gas {struct gas} :=
  match gas with
  | O => None
  | S gas' => match p with
              | PEmpty => Some false
              | PSet _ => Some false
              | PSequence p1 p2 => match checkloops_comp g p1 gas' with
                                   | Some false => checkloops_comp g p2 gas'
                                   | ob => ob
                                   end
              | PChoice p1 p2 => match checkloops_comp g p1 gas' with
                                 | Some false => checkloops_comp g p2 gas'
                                 | ob => ob
                                 end
              | PRepetition p' => match nullable_comp g p' gas' with
                                  | Some false => checkloops_comp g p' gas'
                                  | ob => ob
                                  end
              | PNot p' => checkloops_comp g p' gas'
              | PNT _ => Some false
              end
  end.

Lemma checkloops_comp_soundness :
  forall g p gas b,
  checkloops_comp g p gas = Some b ->
  checkloops g p b.
Proof.
  intros * H.
  generalize dependent b.
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
  forall g p gas b,
  checkloops_comp g p gas = Some b ->
  checkloops_comp g p (S gas) = Some b.
Proof.
  intros * H.
  generalize dependent b.
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
    [ Hx: checkloops_comp _ _ gas = Some _ |- _ ] =>
        apply IHgas in Hx
  end;
  try match goal with
    [ Hx: nullable_comp _ _ gas = Some _ |- _ ] =>
        apply nullable_comp_S_gas in Hx
  end;
  simpl;
  subst;
  try rewrite_match_subject_in_goal;
  eauto.
Qed.

Lemma checkloops_comp_le_gas :
  forall g p gas gas' b,
  checkloops_comp g p gas = Some b ->
  gas <= gas' ->
  checkloops_comp g p gas' = Some b.
Proof.
  intros * H Hle.
  induction Hle;
  eauto using checkloops_comp_S_gas.
Qed.

Lemma checkloops_comp_gas_exists :
  forall g p,
  lcoherent g g true ->
  lverifyrule g g true ->
  coherent g p true ->
  exists gas b,
  checkloops_comp g p gas = Some b.
Proof.
  intros * Hgc Hgv Hpc.
  induction p; intros;
  inversion Hpc; subst;
  repeat specialize_coherent;
  repeat destruct_exists_hyp;
  (* 2 recursive calls *)
  try match goal with
    [ Hx1: checkloops_comp ?g ?p1 ?gas1 = Some ?b1,
      Hx2: checkloops_comp ?g ?p2 ?gas2 = Some ?b2 |- _ ] =>
          pose (gas1 + gas2) as gas;
          assert (gas1 <= gas) by lia;
          assert (gas2 <= gas) by lia;
          assert (checkloops_comp g p1 gas = Some b1)
          as Hx1' by eauto using checkloops_comp_le_gas;
          assert (checkloops_comp g p2 gas = Some b2)
          by eauto using checkloops_comp_le_gas;
          exists (S gas);
          destruct b1;
          simpl;
          rewrite Hx1';
          eauto;
          fail
  end;
  (* 1 recursive call + nullable_comp *)
  try match goal with
    [ Hx1: checkloops_comp ?g ?p1 ?gas1 = Some ?b1 |- _ ] =>
        assert (exists d b k, verifyrule g p1 d false (Some b) k)
        as [d [b [k ?]]] by eauto using
        verifyrule_safe_grammar_yields_safe_pattern,
        lcoherent_true_In,
        lverifyrule_true_In;
        assert (exists gas, nullable_comp g p1 gas = Some b)
        as [gas2 ?] by eauto using nullable_comp_gas_bounded;
        pose (gas1 + gas2) as gas;
        assert (gas1 <= gas) by lia;
        assert (gas2 <= gas) by lia;
        assert (checkloops_comp g p1 gas = Some b1)
        as Hx1' by eauto using checkloops_comp_le_gas;
        assert (nullable_comp g p1 gas = Some b)
        as Hx2' by eauto using nullable_comp_le_gas;
        exists (S gas);
        simpl;
        rewrite Hx2';
        destruct b;
        eauto;
        fail
  end;
  (* 1 recursive call *)
  try match goal with
    [ Hx1: checkloops_comp ?g ?p1 ?gas1 = Some ?b1 |- _ ] =>
        exists (S gas1);
        simpl;
        eauto;
        fail
  end;
  (* 0 recursive calls *)
  try (exists 1; simpl; eauto; fail).
Qed.

Lemma checkloops_comp_gas_bounded :
  forall g p gas,
  lcoherent g g true ->
  coherent g p true ->
  lverifyrule g g true ->
  gas >= pat_size p + S (Datatypes.length g) * (grammar_size g) ->
  exists b, checkloops_comp g p gas = Some b.
Proof.
  intros * Hlc Hc Hlv Hge.
  generalize dependent gas.
  induction p; intros;
  inversion Hc; subst;
  simpl in Hge;
  destruct gas;
  try match goal with
    [ Hx: 0 >= S _ |- _ ] =>
        inversion Hx
  end;
  (* PEmpty, PSet f, PNT i *)
  try (simpl; eauto; fail);
  (* PNot p *)
  try (
    assert (gas >= pat_size p + S (length g) * grammar_size g) by lia;
    eauto;
    fail
  );
  (* PSequence p1 p2, PChoice p1 p2 *)
  try (
    assert (gas >= pat_size p1 + S (length g) * grammar_size g) by lia;
    assert (gas >= pat_size p2 + S (length g) * grammar_size g) by lia;
    assert (exists b, checkloops_comp g p1 gas = Some b)
    as [bc1 Hc1] by eauto;
    simpl;
    rewrite Hc1;
    destruct bc1;
    eauto;
    fail
  );
  (* PRepetition p *)
  try (
    assert (exists d b k, verifyrule g p d false (Some b) k)
    as [? [bv [? ?]]] by eauto using
    verifyrule_safe_grammar_yields_safe_pattern,
    lcoherent_true_In,
    lverifyrule_true_In;
    assert (gas >= pat_size p + S (Datatypes.length g) * grammar_size g) by lia;
    assert (nullable_comp g p gas = Some bv)
    as Hn by eauto using nullable_comp_gas_bounded;
    assert (gas >= pat_size p + S (length g) * grammar_size g) by lia;
    assert (exists b, checkloops_comp g p gas = Some b)
    as [bc' Hc'] by eauto;
    simpl;
    rewrite Hn;
    destruct bv;
    eauto;
    fail
  ).
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
      forall g r rs,
      checkloops g r true ->
      lcheckloops g (cons r rs) true
  | LCLConsSomeFalse :
      forall g r rs b,
      checkloops g r false ->
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
    [ Hx1: checkloops ?g ?r ?b1,
      Hx2: checkloops ?g ?r ?b2 |- _ ] =>
          assert (b1 = b2)
          by eauto using checkloops_determinism
  end;
  try discriminate;
  auto.
Qed.

Lemma lcheckloops_false_In :
  forall g rs r,
  lcheckloops g rs false ->
  In r rs ->
  checkloops g r false.
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
  | cons r rs' => match checkloops_comp g r gas with
                  | Some false => lcheckloops_comp g rs' gas
                  | Some true => Some true
                  | None => None
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
          destruct x as [[|]|] eqn:?;
          try destruct1;
          try discriminate;
          try match goal with
            [ Hx: checkloops_comp ?g ?r ?gas = Some ?b |- _ ] =>
                assert (checkloops g r b)
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
          destruct x as [[|]|] eqn:?;
          try discriminate;
          try destruct1;
          try match goal with
            [ Hx: checkloops_comp ?g ?r ?gas = Some ?b |- _ ] =>
                assert (checkloops_comp g r (S gas) = Some b)
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

Lemma lcheckloops_comp_gas_exists :
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
    assert (exists gas b, lcheckloops_comp g rs gas = Some b)
    as [gaslcl [blcl ?]] by eauto.
    assert (exists gas b, checkloops_comp g r gas = Some b)
    as [gascl [bcl ?]]
    by eauto using checkloops_comp_gas_exists, lcoherent_true_In.
    assert (checkloops g r bcl)
    by eauto using checkloops_comp_soundness.
    simpl.
    pose (gaslcl + gascl) as gas.
    assert (gaslcl <= gas) by lia.
    assert (gascl <= gas) by lia.
    assert (lcheckloops_comp g rs gas = Some blcl)
    as Hlcl' by eauto using lcheckloops_comp_le_gas.
    assert (checkloops_comp g r gas = Some bcl)
    as Hcl' by eauto using checkloops_comp_le_gas.
    exists gas.
    rewrite Hcl'.
    destruct bcl;
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
  assert (exists b, checkloops_comp g r gas = Some b)
  as [clres Hcl]
  by eauto using checkloops_comp_gas_bounded, lcoherent_true_In.
  rewrite Hcl.
  destruct clres;
  eauto.
Qed.
