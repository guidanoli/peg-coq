From Coq Require Import Bool.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Peg Require Import Charset.
From Peg Require Import Checkloops.
From Peg Require Import Coherent.
From Peg Require Import Equivalent.
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
  | FSequenceNullableFalse :
      forall g p1 p2 cs b cs',
      nullable g p1 false ->
      first g p1 fullcharset b cs' ->
      first g (PSequence p1 p2) cs b cs'
  | FSequenceNullableTrue :
      forall g p1 p2 cs b1 b2 cs1 cs2,
      nullable g p1 true ->
      first g p2 cs b2 cs2 ->
      first g p1 cs2 b1 cs1 ->
      first g (PSequence p1 p2) cs (andb b1 b2) cs1
  | FChoice :
      forall g p1 p2 cs cs1 cs2 b1 b2,
      first g p1 cs b1 cs1 ->
      first g p2 cs b2 cs2 ->
      first g (PChoice p1 p2) cs (orb b1 b2) (cs1 ∪ cs2)
  | FRepetition :
      forall g p cs b cs',
      first g p cs b cs' ->
      first g (PRepetition p) cs true (cs ∪ cs')
  | FNotNone :
      forall g p cs,
      tocharset p = None ->
      first g (PNot p) cs true cs
  | FNotSome :
      forall g p cs cs',
      tocharset p = Some cs' ->
      first g (PNot p) cs true (complementcharset cs')
  | FAnd :
      forall g p cs b cs',
      first g p fullcharset b cs' ->
      first g (PAnd p) cs b (cs ∩ cs')
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
  - (* PAnd p *)
    assert (exists b cs', first g p fullcharset b cs')
    as [? [? ?]] by eauto.
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
    [ _: verifygrammarpat ?g (_ ?p) true |- _ ] =>
      assert (verifygrammarpat g p true)
      by eauto using pat_le, verifygrammarpat_true_le
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

Lemma first_unioncharset :
  forall g p csfollow csfirst csextra b,
  first g p csfollow b csfirst ->
  exists csextra',
  (csextra' ⊆ csextra) /\
  first g p (csfollow ∪ csextra) b (csfirst ∪ csextra').
Proof.
  intros * H.
  generalize dependent csextra.
  induction H; intros.
  - (* PEmpty *)
    exists csextra.
    eauto using first, subcharseteq_refl.
  - (* PSet f *)
    exists emptycharset.
    rewrite unioncharset_emptycharset_r.
    eauto using first, subcharseteq_empty.
  - (* PSequence p1 p2, where p1 is non-nullable *)
    specialize (IHfirst csextra) as [? [? Hf]].
    rewrite unioncharset_fullcharset_l in Hf.
    eauto using first.
  - (* PSequence p1 p2, where p1 is nullable *)
    specialize (IHfirst1 csextra) as [csextra' [? ?]].
    specialize (IHfirst2 csextra') as [csextra'' [? ?]].
    eauto using first, subcharseteq_trans.
  - (* PChoice p1 p2 *)
    specialize (IHfirst1 csextra) as [csextra1 [? ?]].
    specialize (IHfirst2 csextra) as [csextra2 [? ?]].
    exists (csextra1 ∪ csextra2).
    split; eauto using subcharseteq_unioncharset.
    assert (((cs1 ∪ cs2) ∪ csextra1 ∪ csextra2) =
           ((cs1 ∪ csextra1) ∪ (cs2 ∪ csextra2))) as Haux.
    {
      extensionality a.
      unfold unioncharset.
      destruct (cs1 a);
      destruct (cs2 a);
      destruct (csextra1 a);
      destruct (csextra2 a);
      auto.
    }
    rewrite Haux.
    eauto using first.
  - (* PRepetition p *)
    specialize (IHfirst csextra) as [csextra' [? ?]].
    exists (csextra ∪ csextra').
    split; eauto using subcharseteq_unioncharset, subcharseteq_refl.
    assert (((cs ∪ cs') ∪ csextra ∪ csextra') =
            ((cs ∪ csextra) ∪ (cs' ∪ csextra'))) as Haux.
    {
      extensionality a.
      unfold unioncharset.
      destruct (cs a);
      destruct (cs' a);
      destruct (csextra a);
      destruct (csextra' a);
      auto.
    }
    rewrite Haux.
    eauto using first.
  - (* PNot p, where tocharset p = None *)
    eauto using first, subcharseteq_refl.
  - (* PNot p, where tocharset p = Some cs' *)
    exists emptycharset.
    split; eauto using subcharseteq_empty.
    rewrite unioncharset_emptycharset_r.
    eauto using first.
  - (* PAnd p *)
    specialize (IHfirst csextra) as [csextra' [Hs ?]].
    exists (csextra ∩ (cs' ∪ csextra')).
    split; eauto using subcharseteq_intersectioncharset_l.
    assert ((cs ∩ cs' ∪ csextra ∩ (cs' ∪ csextra')) =
            (((cs ∪ csextra) ∩ (cs' ∪ csextra'))))
    as Haux.
    {
      inversion Hs; subst.
      extensionality a.
      unfold unioncharset.
      unfold intersectioncharset.
      destruct (cs a) eqn:?;
      destruct (cs' a) eqn:?;
      destruct (csextra' a) eqn:?;
      destruct (cs2 a) eqn:?;
      auto.
    }
    rewrite Haux.
    eauto using first.
  - (* PNT i *)
    specialize (IHfirst csextra) as [csextra' [? ?]].
    eauto using first.
Qed.

Lemma first_feedback :
  forall g p csfollow b csfirst,
  first g p csfollow b csfirst ->
  first g p (csfollow ∪ csfirst) b csfirst.
Proof.
  intros * H.
  apply first_unioncharset with (csextra := csfirst) in H
  as [csextra' [? Hf]].
  assert ((csfirst ∪ csextra') = csfirst)
  as Haux by eauto using subcharseteq_unioncharset_eq.
  rewrite Haux in Hf.
  auto.
Qed.

Lemma first_success :
  forall g p s s' csfollow b csfirst,
  verifygrammarpat g p true ->
  matches g p s (Success s') ->
  s' = EmptyString \/ startswith s' csfollow ->
  first g p csfollow b csfirst ->
  s = EmptyString \/ startswith s csfirst.
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
    unfold startswith.
    auto.
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
    eauto using proper_suffix_length_lt.
  - (* PSequence p1 p2, where p2 is non-nullable *)
    assert (verifygrammarpat g p1 true)
    by eauto using pat_le, verifygrammarpat_true_le.
    assert (nullable g p1 false)
    by eauto using verifyrule_similar_to_nullable.
    inversion Hf; subst;
    inversion Hm; subst;
    pose_nullable_determinism;
    try discriminate.
    eauto using empty_or_startswith_fullcharset.
  - (* PChoice p1 p2 *)
    assert (verifygrammarpat g p1 true)
    by eauto using pat_le, verifygrammarpat_true_le.
    assert (verifygrammarpat g p2 true)
    by eauto using pat_le, verifygrammarpat_true_le.
    inversion Hf; subst;
    inversion Hm; subst;
    try assert (s = EmptyString \/ startswith s cs1) as [|] by eauto;
    try assert (s = EmptyString \/ startswith s cs2) as [|] by eauto;
    eauto using startswith_unioncharset.
  - (* PRepetition p *)
    assert (verifygrammarpat g p true)
    by eauto using pat_le, verifygrammarpat_true_le.
    inversion Hf; subst;
    inversion Hm; subst;
    try (
      destruct Hsw;
      eauto using startswith_unioncharset;
      fail
    ).
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
          assert (s' = EmptyString \/ startswith s' (csfollow ∪ cs'))
          by eauto
    end.
    match goal with
      [ Hx: first g p ?csfollow ?b ?csfirst |- _ ] =>
          let cstmp := fresh "cs" in (
            eapply first_feedback in Hx as ?;
            assert (s = EmptyString \/ startswith s csfirst) by eauto
          )
    end.
    match goal with
      [ Hx: ?s = EmptyString \/ startswith ?s ?cs2
        |- ?s = EmptyString \/ startswith ?s (?cs1 ∪ ?cs2) ] =>
            destruct Hx;
            eauto using startswith_unioncharset
    end.
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
              eauto using startswith_complementcharset
        end
    end;
    eauto.
  - (* PAnd p *)
    assert (verifygrammarpat g p true)
    by eauto using pat_le, verifygrammarpat_true_le.
    inversion Hf; subst;
    inversion Hm; subst;
    assert (s' = EmptyString \/ startswith s' cs')
    as [|] by eauto using empty_or_startswith_fullcharset;
    destruct Hsw;
    eauto using startswith_intersectioncharset.
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

Lemma first_failure :
  forall g p s csfirst,
  verifygrammarpat g p true ->
  first g p fullcharset false csfirst ->
  ~ startswith s csfirst ->
  matches g p s Failure.
Proof.
  intros * Hvgp Hf Hesw.
  assert (exists res, matches g p s res)
  as [[|s'] ?]
  by eauto using verifygrammarpat_safe_match.
  - (* Failure *)
    auto.
  - (* Success s' *)
    assert (s = EmptyString \/ startswith s csfirst)
    as [|]
    by eauto using first_success, empty_or_startswith_fullcharset.
    + (* s = EmptyString *)
      subst.
      eauto using first_false.
    + (* startswith s csfirst *)
      exfalso.
      auto.
Qed.

(* p1 / p2 -> (&[cs1] p1 / ![cs1] p2) *)
Lemma first_choice :
  forall g p1 p2 cs1 cs2 follow b s s',
  let p := PChoice p1 p2 in
  let p' := (PChoice (PSequence (PAnd (PSet cs1)) p1)
                     (PSequence (PNot (PSet cs1)) p2)) in
  verifygrammarpat g p true ->
  s' = EmptyString \/ startswith s' follow ->
  first g p1 fullcharset false cs1 ->
  first g p2 follow b cs2 ->
  disjointcharsets cs1 cs2 ->
  matches g p s (Success s') ->
  matches g p' s (Success s').
Proof.
  intros * Hvgp Hsw Hf1 Hf2 Hdcs Hm.
  assert (verifygrammarpat g p1 true)
  by eauto using verifygrammarpat_true_le, pat_le.
  assert (verifygrammarpat g p2 true)
  by eauto using verifygrammarpat_true_le, pat_le.
  assert (s' = EmptyString \/ startswith s' fullcharset)
  by eauto using empty_or_startswith_fullcharset.
  inversion Hm; subst.
  - (* p1 matches *)
    assert (s = EmptyString \/ startswith s cs1)
    as Hswcs1 by eauto using first_success.
    destruct s as [|a s''].
    + (* EmptyString *)
      assert (matches g p1 EmptyString Failure)
      by eauto using first_failure.
      pose_matches_determinism.
      discriminate.
    + (* String a s *)
      unfold startswith in Hswcs1.
      destruct Hswcs1 as [|Heqcs1a];
      try discriminate.
      eauto 6 using matches.
  - (* p1 fails but p2 matches *)
    destruct s as [|a s''].
    + (* EmptyString *)
      eauto 7 using matches.
    + (* String a s'' *)
      destruct (startswith_dec (String a s'') cs1) as [Hswcs1|Hswcs1];
      simpl in Hswcs1.
      -- (* cs1 a = true *)
         assert (~ exists a, cs1 a = true /\ cs2 a = true)
         by eauto using disjointcharsets_def.
         assert (cs2 a = false)
         by (destruct (cs2 a) eqn:?; auto; exfalso; eauto).
         assert (String a s'' = EmptyString \/ startswith (String a s'') cs2)
         as [|]
         by eauto using first_success;
         try discriminate.
         simpl in H4.
         destruct1sep.
      -- (* ~ startswith (String a s'') cs1 *)
         destruct (cs1 a) eqn:Heqcs1a; try contradiction.
         eauto 9 using matches.
 Qed.

(* on failure, p1 / p2 -> (&[cs1] p1 / ![cs1] p2) *)
Lemma first_choice_failure :
  forall g p1 p2 cs s,
  let p := PChoice p1 p2 in
  let p' := (PChoice (PSequence (PAnd (PSet cs)) p1)
                     (PSequence (PNot (PSet cs)) p2)) in
  matches g p s Failure ->
  matches g p' s Failure.
Proof.
  intros * Hm.
  inversion Hm; subst.
  econstructor;
  destruct s as [|a s']; eauto using matches;
  destruct (cs a) eqn:?; eauto using matches.
Qed.

Fixpoint first_comp g p cs gas :=
  match gas with
  | O => None
  | S gas' => match p with
              | PEmpty => Some (true, cs)
              | PSet cs' => Some (false, cs')
              | PSequence p1 p2 => match nullable_comp g p1 gas' with
                                   | Some false => first_comp g p1 fullcharset gas'
                                   | Some true => match first_comp g p2 cs gas' with
                                                  | Some (b2, cs2) => match first_comp g p1 cs2 gas' with
                                                                      | Some (b1, cs1) => Some (b1 && b2, cs1)
                                                                      | None => None
                                                                      end
                                                  | None => None
                                                  end
                                   | None => None
                                   end
              | PChoice p1 p2 => let res1 := first_comp g p1 cs gas' in
                                 let res2 := first_comp g p2 cs gas' in
                                 match res1, res2 with
                                 | Some (b1, cs1), Some (b2, cs2) => Some (b1 || b2, cs1 ∪ cs2)
                                 | _, _ => None
                                 end
              | PRepetition p => match first_comp g p cs gas' with
                                 | Some (_, cs') => Some (true, cs ∪ cs')
                                 | None => None
                                 end
              | PNot p => match tocharset p with
                          | Some cs' => Some (true, complementcharset cs')
                          | None => Some (true, cs)
                          end
              | PAnd p => match first_comp g p fullcharset gas' with
                          | Some (b, cs') => Some (b, cs ∩ cs')
                          | None => None
                          end
              | PNT i => match nth_error g i with
                         | Some p' => first_comp g p' cs gas'
                         | None => None
                         end
              end
  end.

Lemma first_comp_soundness :
  forall g p cs gas b cs',
  first_comp g p cs gas = Some (b, cs') ->
  first g p cs b cs'.
Proof.
  intros.
  generalize dependent cs'.
  generalize dependent b.
  generalize dependent cs.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros;
  simpl in H;
  try discriminate;
  destruct p;
  try destruct2;
  repeat destruct_match_subject_in_hyp;
  subst;
  try destruct1;
  try discriminate;
  eauto using first, nullable_comp_soundness.
Qed.

Lemma first_comp_S_gas :
  forall g p cs gas b cs',
  first_comp g p cs gas = Some (b, cs') ->
  first_comp g p cs (S gas) = Some (b, cs').
Proof.
  intros.
  generalize dependent cs'.
  generalize dependent b.
  generalize dependent cs.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros;
  simpl in H;
  try discriminate;
  destruct p;
  try destruct2;
  remember (S gas) as gas';
  simpl;
  auto;
  repeat destruct_match_subject_in_hyp;
  subst;
  try destruct2;
  repeat match goal with
  | [ Hx: nullable_comp _ _ gas = Some _ |- _ ] => apply nullable_comp_S_gas in Hx
  | [ Hx: first_comp _ _ _ gas = Some _ |- _ ] => apply IHgas in Hx
  end;
  repeat rewrite_match_subject_in_goal;
  try discriminate;
  auto.
Qed.

Lemma first_comp_le_gas :
  forall g p cs gas gas' b cs',
  first_comp g p cs gas = Some (b, cs') ->
  gas <= gas' ->
  first_comp g p cs gas' = Some (b, cs').
Proof.
  intros * H Hle.
  induction Hle;
  eauto using first_comp_S_gas.
Qed.

Lemma first_comp_gas_bounded_by_depth :
  forall g p nb d b k cs gas,
  lcoherent g g true ->
  coherent g p true ->
  verifyrule g p d nb (Some b) k ->
  gas >= pat_size p + d * (grammar_size g) ->
  exists b' cs', first_comp g p cs gas = Some (b', cs').
Proof.
  intros * Hlc Hc Hv Hge.
  generalize dependent gas.
  generalize dependent cs.
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
  try destruct2sep;
  try discriminate;
  simpl;
  eauto.
  - (* PSequence p1 p2, where p1 is nullable *)
    assert (gas >= pat_size p1 + d * (grammar_size g)) by lia.
    assert (gas >= pat_size p2 + d * (grammar_size g)) by lia.
    assert (nullable_comp g p1 gas = Some true)
    as Hncomp by eauto using nullable_comp_gas_bounded_by_depth.
    rewrite Hncomp.
    assert (exists b' cs', first_comp g p2 cs gas = Some (b', cs'))
    as [? [cs2 Hf2]] by eauto.
    rewrite Hf2.
    assert (exists b' cs', first_comp g p1 cs2 gas = Some (b', cs'))
    as [? [? Hf1]] by eauto.
    rewrite Hf1.
    eauto.
  - (* PSequence p1 p2, where p1 is non-nullable *)
    assert (gas >= pat_size p1 + d * (grammar_size g)) by lia.
    assert (nullable_comp g p1 gas = Some false)
    as Hncomp by eauto using nullable_comp_gas_bounded_by_depth.
    rewrite Hncomp.
    eauto.
  - (* PChoice p1 p2 *)
    assert (gas >= pat_size p1 + d * (grammar_size g)) by lia.
    assert (gas >= pat_size p2 + d * (grammar_size g)) by lia.
    assert (exists b' cs', first_comp g p1 cs gas = Some (b', cs'))
    as [? [? Hf1]] by eauto.
    rewrite Hf1.
    assert (exists b' cs', first_comp g p2 cs gas = Some (b', cs'))
    as [? [? Hf2]] by eauto.
    rewrite Hf2.
    eauto.
  - (* PRepetition p *)
    assert (gas >= pat_size p + d * (grammar_size g)) by lia.
    assert (exists b' cs', first_comp g p cs gas = Some (b', cs'))
    as [? [? Hf]] by eauto.
    rewrite Hf.
    eauto.
  - (* PNot p *)
    destruct (tocharset p);
    eauto.
  - (* PAnd p *)
    assert (gas >= pat_size p + d * (grammar_size g)) by lia.
    assert (exists b' cs', first_comp g p fullcharset gas = Some (b', cs'))
    as [? [? Hf]] by eauto.
    rewrite Hf.
    eauto.
  - (* PNT i *)
    match goal with
      [ Hx: nth_error ?g ?i = Some ?p |- _ ] =>
          assert (In p g) by eauto using nth_error_In;
          assert (coherent g p true) by eauto using lcoherent_true_In;
          assert (pat_size p <= grammar_size g) by eauto using pat_size_le_grammar_size;
          assert (gas >= pat_size p + d * (grammar_size g)) by lia;
          rewrite Hx
    end.
    eauto.
Qed.

Lemma first_comp_gas_bounded :
  forall g p cs gas,
  verifygrammarpat g p true ->
  gas >= pat_size p + (S (Datatypes.length g)) * (grammar_size g) ->
  exists b' cs', first_comp g p cs gas = Some (b', cs').
Proof.
  intros * Hvgp Hge.
  inversion Hvgp; subst.
  match goal with
    [ Hx: verifygrammar _ true |- _ ] =>
        inversion Hx; subst
  end.
  assert (exists nb d b k, verifyrule g p d nb (Some b) k)
  as [nb [? [b [? ?]]]]
  by eauto using verifygrammarpat_verifyrule.
  assert (exists k', verifyrule g p (S (Datatypes.length g)) nb (Some b) k')
  as [? ?] by eauto using verifyrule_Some_min_depth.
  eauto using first_comp_gas_bounded_by_depth.
Qed.
