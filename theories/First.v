From Coq Require Import Bool.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Peg Require Import Charset.
From Peg Require Import Checkloops.
From Peg Require Import Coherent.
From Peg Require Import Match.
From Peg Require Import Nullable.
From Peg Require Import Startswith.
From Peg Require Import Strong.
From Peg Require Import Suffix.
From Peg Require Import Syntax.
From Peg Require Import Tactics.
From Peg Require Import Verifygrammar.
From Peg Require Import Verifyrule.

Inductive first : grammar -> pat -> charset -> bool -> charset -> Prop :=
  | FEmpty :
      forall g cs,
      first g PEmpty cs true cs
  | FSet :
      forall g cs cs',
      first g (PSet cs') cs false cs'
  | FSequenceNullableSomeFalse :
      forall g p1 p2 cs b cs',
      nullable g p1 false ->
      first g p1 fullcharset b cs' ->
      first g (PSequence p1 p2) cs b cs'
  | FSequenceNullableSomeTrue :
      forall g p1 p2 cs b1 b2 cs1 cs2,
      nullable g p1 true ->
      first g p2 cs b2 cs2 ->
      first g p1 cs2 b1 cs1 ->
      first g (PSequence p1 p2) cs (andb b1 b2) cs1
  | FChoice :
      forall g p1 p2 cs cs1 cs2 b1 b2,
      first g p1 cs b1 cs1 ->
      first g p2 cs b2 cs2 ->
      first g (PChoice p1 p2) cs (orb b1 b2) (cs1 U cs2)
  | FRepetition :
      forall g p cs b cs',
      first g p cs b cs' ->
      first g (PRepetition p) cs true (cs U cs')
  | FNotNone :
      forall g p cs,
      tocharset p = None ->
      first g (PNot p) cs true cs
  | FNotSome :
      forall g p cs cs',
      tocharset p = Some cs' ->
      first g (PNot p) cs true (complementcharset cs')
  | FNT :
      forall g i p cs b cs',
      nth_error g i = Some p ->
      first g p cs b cs' ->
      first g (PNT i) cs b cs'
  .

Theorem first_determinism :
  forall g p cs b1 b2 cs1 cs2,
  first g p cs b1 cs1 ->
  first g p cs b2 cs2 ->
  b1 = b2 /\ cs1 = cs2.
Proof.
  intros * H1 H2.
  generalize dependent cs2.
  generalize dependent b2.
  induction H1; intros;
  inversion H2; subst;
  try pose_nullable_determinism;
  try destruct2sep;
  try destruct1sep;
  repeat match goal with
    [ IHx: forall bx csx, first ?g ?p ?cs bx csx -> _ = bx /\ _ = csx,
      Hx: first ?g ?p ?cs _ _ |- _ ] =>
          apply IHx in Hx;
          destruct Hx;
          subst
  end;
  try discriminate;
  eauto using first.
Qed.

Ltac pose_first_determinism :=
  match goal with
    [ _: first ?g ?p ?cs ?b1 ?cs1,
      _: first ?g ?p ?cs ?b2 ?cs2 |- _ ] =>
            assert (b1 = b2 /\ cs1 = cs2)
            as [? ?] by eauto using first_determinism
  end.

Theorem first_complete :
  forall g p cs,
  verifygrammarpat g p true ->
  exists b cs', first g p cs b cs'.
Proof.
  intros * Hvgp.
  assert (exists nb d b k, verifyrule g p d nb (Some b) k)
  as [nb [d [b [k Hvr]]]] by eauto using verifygrammarpat_verifyrule.
  remember (Some b) as res.
  generalize dependent cs.
  generalize dependent b.
  clear Hvgp.
  induction Hvr; intros;
  try discriminate;
  try destruct1;
  try (eauto using first; fail).
  - (* PSequence p1 p2; where p1 is nullable *)
    assert (nullable g p1 true)
    by eauto using verifyrule_similar_to_nullable.
    assert (exists b cs', first g p2 cs b cs')
    as [? [cs2 ?]] by eauto.
    assert (exists b cs', first g p1 cs2 b cs')
    as [? [? ?]] by eauto.
    eauto using first.
  - (* PSequence p1 p2; where p1 is non-nullable *)
    assert (nullable g p1 false)
    by eauto using verifyrule_similar_to_nullable.
    assert (exists b cs', first g p1 fullcharset b cs')
    as [? [? ?]] by eauto.
    eauto using first.
  - (* PChoice p1 p2 *)
    assert (exists b cs', first g p1 cs b cs')
    as [? [? ?]] by eauto.
    assert (exists b cs', first g p2 cs b cs')
    as [? [? ?]] by eauto.
    eauto using first.
  - (* PRepetition p *)
    assert (exists b cs', first g p cs b cs')
    as [? [? ?]] by eauto.
    eauto using first.
  - (* PNot p *)
    destruct (tocharset p) eqn:?;
    eauto using first.
  - (* PNT i *)
    assert (exists b cs', first g p cs b cs')
    as [? [? ?]] by eauto.
    eauto using first.
Qed.

Lemma first_false :
  forall g p cs cs',
  verifygrammarpat g p true ->
  first g p cs false cs' ->
  matches g p EmptyString Failure.
Proof.
  intros * Hvgp Hf.
  remember false as b in Hf.
  induction Hf;
  try match goal with
    [ Hx: ?b1 && ?b2 = false |- _ ] =>
        destruct b1;
        destruct b2;
        simpl in Hx
  end;
  try match goal with
    [ Hx: ?b1 || ?b2 = false |- _ ] =>
        destruct b1;
        destruct b2;
        simpl in Hx
  end;
  try match goal with
    [ _: verifygrammarpat ?g (_ ?p1 ?p2) true |- _ ] =>
      assert (verifygrammarpat g p1 true)
      by eauto using pat_le, verifygrammarpat_true_le;
      assert (verifygrammarpat g p2 true)
      by eauto using pat_le, verifygrammarpat_true_le;
      assert (exists res, matches g p1 EmptyString res)
      as [[|?] ?] by eauto using verifygrammarpat_safe_match
  end;
  try match goal with
    [ _: matches _ _ EmptyString (Success ?s) |- _ ] =>
        let H := fresh "H" in (
          assert (suffix s EmptyString)
          as H by eauto using matches_suffix;
          inversion H; subst
        )
  end;
  try match goal with
    [ Hvgp: verifygrammarpat ?g (PNT ?i) true,
      _: nth_error ?g ?i = Some ?p |- _ ] =>
          inversion Hvgp; subst;
          assert (verifygrammarpat g p true)
          by eauto using nth_error_In, verifygrammarpat_true_In
  end;
  try discriminate;
  eauto using matches.
Qed.

Lemma first_true :
  forall g p cs,
  verifygrammarpat g p true ->
  matches g p EmptyString (Success EmptyString) ->
  exists cs', first g p cs true cs'.
Proof.
  intros * Hvgp Hm.
  assert (exists b cs', first g p cs b cs')
  as [b [cs' ?]] by eauto using first_complete.
  destruct b.
  - (* true *)
    eauto.
  - (* false *)
    assert (matches g p EmptyString Failure)
    by eauto using first_false.
    pose_matches_determinism.
    discriminate.
Qed.

Lemma first_b_independence :
  forall g p cs1 cs1' cs2 cs2' b1 b2,
  first g p cs1 b1 cs1' ->
  first g p cs2 b2 cs2' ->
  b1 = b2.
Proof.
  intros * H1 H2.
  generalize dependent cs2'.
  generalize dependent b2.
  generalize dependent cs2.
  induction H1; intros;
  inversion H2; subst;
  try destruct2sep;
  try pose_nullable_determinism;
  try pose_first_determinism;
  try discriminate;
  repeat match goal with
    [ IHx: forall csx bx csx', first ?g ?p csx bx csx' -> _ = bx,
      Hx: first ?g ?p _ _ _ |- _ ] =>
          apply IHx in Hx
  end;
  subst;
  auto.
Qed.

Ltac pose_first_b_independence :=
  match goal with
    [ _: first ?g ?p ?cs1 ?b1 ?cs1',
      _: first ?g ?p ?cs2 ?b2 ?cs2' |- _ ] =>
          assert (b1 = b2)
          by eauto using first_b_independence
  end.

Lemma first_charseteq_determinism :
  forall g p cs1 cs1' cs2 cs2' b1 b2,
  first g p cs1 b1 cs1' ->
  first g p cs2 b2 cs2' ->
  charseteq cs1 cs2 ->
  b1 = b2 /\ charseteq cs1' cs2'.
Proof.
  intros * H1 H2 Hcseq.
  generalize dependent cs2'.
  generalize dependent b2.
  generalize dependent cs2.
  induction H1; intros;
  inversion H2; subst;
  try destruct1sep;
  try pose_nullable_determinism;
  try pose_first_determinism;
  try discriminate;
  subst;
  repeat match goal with
  [ Hx: charseteq ?cs ?csx,
    Hy: first ?g ?p ?csx ?bx ?csx',
    IHx: forall csx, charseteq ?cs csx ->
         forall bx csx', first ?g ?p csx bx csx' ->
         ?b = bx /\ charseteq ?cs' csx' |- _ ] =>
              assert (b = bx /\ charseteq cs' csx')
              as [? ?] by eauto;
              subst;
              clear IHx
  end;
  auto using charseteq, unioncharset_distrib.
Qed.

Ltac pose_first_charseteq_determinism :=
  match goal with
    [ _: first ?g ?p ?cs1 ?b1 ?cs1',
      _: first ?g ?p ?cs2 ?b2 ?cs2',
      _: charseteq ?cs1 ?cs2 |- _ ] =>
          assert (b1 = b2 /\ charseteq cs1' cs2')
          as [? ?] by eauto using first_charseteq_determinism
  end.

Lemma first_exists_if_follow_changes :
  forall g p csfollow csfollow' b csfirst,
  first g p csfollow b csfirst ->
  exists csfirst', first g p csfollow' b csfirst'.
Proof.
  intros.
  generalize dependent csfollow'.
  induction H; intros;
  eauto using first.
  - (* PSequence p1 p2, where p1 is nullable *)
    destruct (IHfirst1 csfollow') as [csmid ?].
    destruct (IHfirst2 csmid) as [? ?].
    eauto using first.
  - (* PChoice p1 p2 *)
    destruct (IHfirst1 csfollow') as [? ?].
    destruct (IHfirst2 csfollow') as [? ?].
    eauto using first.
  - (* PRepetition p *)
    destruct (IHfirst csfollow') as [? ?].
    eauto using first.
  - (* PNT i *)
    destruct (IHfirst csfollow') as [? ?].
    eauto using first.
Qed.

Lemma first_unioncharset :
  forall g p csfollow csfirst csextra b,
  first g p csfollow b csfirst ->
  exists csfirst', first g p (csfollow U csextra) b csfirst' /\
  (charseteq csfirst' csfirst \/ charseteq csfirst' (csfirst U csextra)).
Proof.
  intros * H.
  generalize dependent csextra.
  induction H; intros;
  eauto using first,
              charseteq,
              charseteq_refl,
              charseteq_comm,
              unioncharset_diag.
  - (* PSequence p1 p2, where p1 is nullable *)
    destruct (IHfirst1 csextra) as [csmid [? [|]]]; eauto using first.
    + (* first(p2) stays the same *)
      destruct (IHfirst2 csextra) as [? [? [|]]];
      assert (exists csfirst', first g p1 csmid b1 csfirst')
      as [? ?] by eauto using first_exists_if_follow_changes;
      pose_first_charseteq_determinism;
      subst;
      eauto using first.
    + (* first(p2) grows *)
      destruct (IHfirst2 csextra) as [? [? [|]]];
      assert (exists csfirst', first g p1 csmid b1 csfirst')
      as [? ?] by eauto using first_exists_if_follow_changes;
      pose_first_charseteq_determinism;
      subst;
      pose_charseteq_trans;
      eauto using first, charseteq_trans, charseteq_comm, charseteq.
  - (* PChoice p1 p2 *)
    destruct (IHfirst1 csextra) as [? [? [|]]];
    destruct (IHfirst2 csextra) as [? [? [|]]];
    pose_charseteq_union_distrib;
    eexists;
    split;
    eauto using first.
    + (* first(p1) stays the same, but first(p2) grows *)
      right.
      eauto using charseteq_trans, unioncharset_assoc.
    + (* first(p1) grows, but first(p2) stays the same *)
      right.
      eauto using charseteq_trans,
                  charseteq_refl,
                  unioncharset_assoc,
                  unioncharset_comm,
                  unioncharset_distrib.
    + (* first(p1) and first(p2) grow *)
      right.
      eauto using charseteq_trans, unioncharset_rep_l.
  - (* PRepetition p *)
    destruct (IHfirst csextra) as [? [? [|]]].
    + (* first(p) stays the same *)
      eexists;
      split;
      eauto using first.
      right.
      eauto using charseteq_trans,
                  charseteq_comm,
                  unioncharset_assoc,
                  unioncharset_comm,
                  unioncharset_distrib.
    + (* first(p) grows *)
      eexists;
      split;
      eauto using first.
      right.
      eauto using charseteq_trans,
                  unioncharset_distrib,
                  unioncharset_comm,
                  unioncharset_rep_l.
  - (* PNT i *)
    destruct (IHfirst csextra) as [? [? [|]]];
    eauto using first.
Qed.

Lemma first_feedback :
  forall g p csfollow b csfirst,
  first g p csfollow b csfirst ->
  exists csfirst', first g p (csfollow U csfirst) b csfirst' /\
  charseteq csfirst' csfirst.
Proof.
  intros * H.
  apply first_unioncharset with (csextra := csfirst) in H as [? [? [?|?]]];
  eauto using charseteq_trans, charseteq_comm, unioncharset_diag.
Qed.

Lemma first_success :
  forall g p s s' csfollow b csfirst,
  verifygrammarpat g p true ->
  matches g p s (Success s') ->
  startswith s' csfollow ->
  first g p csfollow b csfirst ->
  startswith s csfirst.
Proof.
  intros * Hvgp Hm Hsw Hf.
  remember (String.length s) as n.
  generalize dependent csfirst.
  generalize dependent b.
  generalize dependent csfollow.
  generalize dependent s'.
  generalize dependent s.
  generalize dependent p.
  generalize dependent g.
  induction n as [n IHn] using strong_induction.
  intros.
  assert (exists nb d b k, verifyrule g p d nb (Some b) k)
  as [? [? [bx [? Hvr]]]] by eauto using verifygrammarpat_verifyrule.
  remember (Some bx) as res.
  generalize dependent bx.
  generalize dependent n.
  generalize dependent csfirst.
  generalize dependent b.
  generalize dependent csfollow.
  generalize dependent s'.
  generalize dependent s.
  induction Hvr; intros;
  try destruct1;
  try discriminate;
  subst.
  - (* PEmpty *)
    inversion Hf; subst;
    inversion Hm; subst.
    auto.
  - (* PSet cs *)
    inversion Hf; subst;
    inversion Hm; subst.
    match goal with
      [ Hx: in_charset ?a ?cs |- _ ] =>
          inversion Hx; subst
    end.
    eauto using startswith.
  - (* PSequence p1 p2, where p1 is nullable *)
    assert (verifygrammarpat g p1 true)
    by eauto using pat_le, verifygrammarpat_true_le.
    assert (verifygrammarpat g p2 true)
    by eauto using pat_le, verifygrammarpat_true_le.
    assert (nullable g p1 true)
    by eauto using verifyrule_similar_to_nullable.
    inversion Hf; subst;
    inversion Hm; subst;
    pose_nullable_determinism;
    try discriminate.
    match goal with
      [ Hx1: matches ?g ?p1 ?s (Success ?smid),
        Hx2: matches ?g ?p2 ?smid (Success ?s') |- _ ] =>
            assert (smid = s \/ proper_suffix smid s) as [|]
            by eauto using matches_suffix, suffix_is_refl_or_proper_suffix;
            try subst smid
    end;
    eauto using startswith, proper_suffix_length_lt.
  - (* PSequence p1 p2, where p2 is non-nullable *)
    assert (verifygrammarpat g p1 true)
    by eauto using pat_le, verifygrammarpat_true_le.
    assert (nullable g p1 false)
    by eauto using verifyrule_similar_to_nullable.
    inversion Hf; subst;
    inversion Hm; subst;
    pose_nullable_determinism;
    try discriminate.
    eauto using startswith, startswith_fullcharset.
  - (* PChoice p1 p2 *)
    assert (verifygrammarpat g p1 true)
    by eauto using pat_le, verifygrammarpat_true_le.
    assert (verifygrammarpat g p2 true)
    by eauto using pat_le, verifygrammarpat_true_le.
    inversion Hf; subst;
    inversion Hm; subst;
    eauto using startswith, startswith_unioncharset.
  - (* PRepetition p *)
    assert (verifygrammarpat g p true)
    by eauto using pat_le, verifygrammarpat_true_le.
    inversion Hf; subst;
    inversion Hm; subst;
    eauto using startswith, startswith_unioncharset. (* move down *)
    inversion Hvgp; subst.
    match goal with
      [ Hx: checkloops _ (PRepetition _) false |- _ ] =>
        inversion Hx; subst
    end.
    match goal with
      [ _: matches ?g ?p ?s (Success ?s'),
        _: nullable ?g ?p false |- _ ] =>
          assert (proper_suffix s' s)
          by eauto using nullable_false_proper_suffix;
          assert (length s' < length s)
          by eauto using proper_suffix_length_lt;
          assert (startswith s' (csfollow U cs'))
          by eauto
    end.
    match goal with
      [ Hx: first g p ?csfollow ?b ?csfirst |- _ ] =>
          let cstmp := fresh "cs" in (
            eapply first_feedback in Hx as [cstmp [? ?]];
            assert (startswith s cstmp) by eauto
          )
    end.
    eauto using startswith_charseteq, startswith_unioncharset.
  - (* PNot p *)
    assert (verifygrammarpat g p true)
    by eauto using pat_le, verifygrammarpat_true_le.
    inversion Hf; subst;
    inversion Hm; subst;
    try match goal with
      [ Hx: tocharset ?p = Some _ |- _ ] =>
        destruct p; try discriminate;
        simpl in Hx;
        injection Hx as Hx; subst;
        match goal with
          [ Hy: matches ?g (PSet ?cs) _ Failure |- _ ] =>
              inversion Hy; subst;
              eauto using startswith,
                          startswith_complementcharset
        end
    end;
    eauto.
  - (* PNT i *)
    match goal with
      [ Hx: verifygrammarpat ?g (PNT ?i) true,
        _: nth_error ?g ?i = Some ?p |- _ ] =>
            inversion Hx; subst;
            assert (verifygrammarpat g p true)
            by eauto using nth_error_In, verifygrammarpat_true_In
    end.
    inversion Hf; subst;
    inversion Hm; subst;
    repeat destruct2sep;
    eauto.
Qed.
