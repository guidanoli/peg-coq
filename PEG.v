From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.

(** Syntax **)
(************)

Inductive pat : Type :=
  | PEmpty : pat
  | PChar : ascii -> pat
  | PAnyChar : pat
  | PSequence : pat -> pat -> pat
  | PChoice : pat -> pat -> pat
  | PKleene : pat -> pat
  | PNot : pat -> pat
  .

(** Semantics **)
(***************)

(** Match predicate **)

Inductive MatchResult : Type :=
  | Failure : MatchResult
  | Success : string -> MatchResult
  .

Inductive matches : pat -> string -> MatchResult -> Prop :=
  | MEmpty :
      forall s,
      matches PEmpty s (Success s)
  | MChar1 :
      forall a,
      matches (PChar a) EmptyString Failure
  | MChar2 :
      forall a s,
      matches (PChar a) (String a s) (Success s)
  | MChar3 :
      forall a1 a2 s,
      a1 <> a2 ->
      matches (PChar a1) (String a2 s) Failure
  | MAnyChar1 :
      matches PAnyChar EmptyString Failure
  | MAnyChar2 :
      forall a s,
      matches PAnyChar (String a s) (Success s)
  | MSequence1 :
      forall p1 p2 s,
      matches p1 s Failure ->
      matches (PSequence p1 p2) s Failure
  | MSequence2 :
      forall p1 p2 s s' res,
      matches p1 s (Success s') ->
      matches p2 s' res ->
      matches (PSequence p1 p2) s res
  | MChoice1 :
      forall p1 p2 s s',
      matches p1 s (Success s') ->
      matches (PChoice p1 p2) s (Success s')
  | MChoice2 :
      forall p1 p2 s res,
      matches p1 s Failure ->
      matches p2 s res ->
      matches (PChoice p1 p2) s res
  | MKleene1 :
      forall p s,
      matches p s Failure ->
      matches (PKleene p) s (Success s)
  | MKleene2 :
      forall p s s' res,
      matches p s (Success s') ->
      matches (PKleene p) s' res ->
      matches (PKleene p) s res
  | MNot1 :
      forall p s,
      matches p s Failure ->
      matches (PNot p) s (Success s)
  | MNot2 :
      forall p s s',
      matches p s (Success s') ->
      matches (PNot p) s Failure
  .

Ltac destruct1 :=
  match goal with
  [ H: ?C _ = ?C _ |- _ ] =>
      inversion H; clear H; subst
  end.

Ltac apply_matches_IH :=
  match goal with [
    IHx: forall r, matches ?p ?s r -> _ = r,
    Hx: matches ?p ?s _ |- _
  ] =>
    apply IHx in Hx
  end.

(** Match predicate determinism **)

Theorem match_det :
  forall p s res1 res2,
  matches p s res1 ->
  matches p s res2 ->
  res1 = res2.
Proof.
  intros p s res1 res2 H1 H2.
  generalize dependent res2.
  induction H1;
  intros res2 H2;
  inversion H2; subst;
  try apply_matches_IH;
  try contradiction;
  try discriminate;
  try destruct1;
  try apply_matches_IH;
  auto.
Qed.

Ltac pose_matches_det :=
  match goal with
  [ H1: matches ?p ?s ?r1,
    H2: matches ?p ?s ?r2 |- _ ] =>
        pose (match_det p s r1 r2 H1 H2)
  end.

Example kleene_infinite_loop :
  forall p s,
  matches p s (Success s) ->
  ~ (exists res, matches (PKleene p) s res).
Proof.
  intros p s H1 [res H2].
  remember (PKleene p).
  induction H2;
  try destruct1;
  try pose_matches_det;
  try discriminate;
  try destruct1;
  auto.
Qed.

Ltac destruct2 :=
  match goal with
  [ H: ?C _ _ = ?C _ _ |- _ ] =>
      inversion H; clear H; subst
  end.

Theorem string_not_recursive :
  forall s a,
  ~ (s = String a s).
Proof.
  intros s a H.
  induction s.
  - discriminate.
  - destruct2.
    auto.
Qed.

Theorem append_empty :
  forall s,
  append s EmptyString = s.
Proof.
  intros.
  induction s.
  - simpl. trivial.
  - simpl. rewrite IHs. trivial.
Qed.

Theorem append_comm :
  forall s1 s2 s3,
  append s1 (append s2 s3) = append (append s1 s2) s3.
Proof.
  intros.
  induction s1.
  - simpl. trivial.
  - simpl. rewrite IHs1. trivial.
Qed.

(** Match prefix theorem **)

Theorem matches_prefix :
  forall p s res s2,
  matches p s res ->
  res = Success s2 ->
  (exists s1, s = append s1 s2).
Proof.
  intros.
  generalize dependent s2.
  induction H;
  intros;
  subst;
  try destruct1;
  try discriminate;
  try match goal with
    [ |- exists s1, ?s2 = append s1 ?s2 ] =>
        exists EmptyString
  end;
  try match goal with
    [ |- exists s1, String ?a ?s2 = append s1 ?s2 ] =>
        exists (String a EmptyString)
  end;
  auto;
  repeat match goal with
  [ IHx: forall sb, Success ?sx = Success sb -> exists sa, ?sy = append sa sb |- _ ] =>
      assert (Success sx = Success sx) as Haux;
      trivial;
      specialize (IHx sx Haux);
      clear Haux;
      destruct IHx
  end;
  subst;
  try match goal with
  [ |- exists sx, (append ?sa (append ?sb ?sc)) = (append sx ?sc) ] =>
      exists (append sa sb);
      apply append_comm
  end.
Qed.

Theorem matches_prefix2 :
  forall p s s2,
  matches p s (Success s2) ->
  (exists s1, s = append s1 s2).
Proof.
  intros.
  eauto using matches_prefix.
Qed.

Theorem length_append :
  forall s1 s2,
  length (append s1 s2) = length s1 + length s2.
Proof.
  intros.
  induction s1.
  - auto.
  - simpl. rewrite IHs1. trivial.
Qed.

Theorem n_eq_m_plus_n :
  forall n m,
  n = m + n ->
  m = 0.
Proof.
  intros n.
  induction n;
  intros.
  - rewrite <- plus_n_O in H.
    auto.
  - apply IHn.
    rewrite <- plus_n_Sm in H.
    injection H as H.
    trivial.
Qed.

Theorem length_zero :
  forall s,
  length s = 0 ->
  s = EmptyString.
Proof.
  intros.
  induction s.
  - trivial.
  - simpl in H. discriminate.
Qed.

Theorem empty_prefix :
  forall s s',
  s = append s' s ->
  s' = EmptyString.
Proof.
  intros.
  specialize (length_append s' s) as Hlen.
  rewrite <- H in Hlen.
  specialize (n_eq_m_plus_n _ _ Hlen) as Hlen0.
  auto using length_zero.
Qed.

Theorem append_is_empty :
  forall s s',
  append s s' = EmptyString ->
  s = EmptyString /\ s' = EmptyString.
Proof.
  intros s.
  induction s;
  intros.
  - simpl in H.
    split; auto.
  - simpl in H.
    discriminate.
Qed.

Theorem mutual_prefixes :
  forall s s' s1 s2,
  s = append s1 s' ->
  s' = append s2 s ->
  s = s'.
Proof.
  intros s s' s1 s2 Hs Hs'.
  rewrite Hs in Hs'.
  rewrite append_comm in Hs'.
  apply empty_prefix in Hs'.
  apply append_is_empty in Hs' as [Hs2 Hs1].
  rewrite Hs1 in Hs.
  auto.
Qed.

Lemma mutual_match_suffixes :
  forall p1 p2 s1 s2,
  matches p1 s1 (Success s2) ->
  matches p2 s2 (Success s1) ->
  s1 = s2.
Proof.
  intros.
  repeat match goal with
  [ Hx: matches _ _ (Success _) |- _ ] =>
      apply matches_prefix2 in Hx;
      destruct Hx
  end.
  eauto using mutual_prefixes.
Qed.

(** Nullable pattern definition **)

(*
  If a pattern may match a string without consuming any
  characters, then it is nullable.
*)
Definition nullable p := exists s, matches p s (Some s).

(** Nullable pattern function **)

(*
  Computable version of nullable
*)
Fixpoint nullable_comp p :=
  match p with
  | PEmpty => true
  | PChar _ => false
  | PAnyChar => false
  | PSequence p1 p2 => nullable_comp p1 && nullable_comp p2
  | PChoice p1 p2 => nullable_comp p1 || nullable_comp p2
  | PKleene _ => true
  | PNot _ => true
  end.

Ltac apply_string_not_rec :=
  match goal with
  [ Hx: ?s = String ?a ?s |- _ ] =>
    exfalso;
    apply (string_not_recursive _ _ Hx)
  end.

Ltac injection_some :=
  match goal with
    [ Hx: Some _ = Some _ |- _ ] =>
    injection Hx as Hx
  end.

(** Nullable pattern function soundness **)

Theorem nullable_comp_sound :
  forall p, nullable p -> nullable_comp p = true.
Proof.
  intros.
  unfold nullable in H.
  destruct H as [s H].
  remember (Some s) as res eqn:Hres.
  generalize dependent Hres.
  induction H; intro Hres;
  auto;
  try discriminate;
  try injection_some;
  try apply_string_not_rec;
  subst;
  try match goal with
  [ Hx1: matches _ ?s1 (Some ?s2),
    Hx2: matches _ ?s2 (Some ?s1) |- _ ] =>
        specialize (mutual_match_suffixes _ _ _ _ Hx1 Hx2);
        intro;
        subst
  end;
  try repeat match goal with
  [ Hx: ?a = ?a -> _ |- _ ] =>
      assert (a = a) as Haux;
      trivial;
      apply Hx in Haux;
      clear Hx;
      rename Haux into Hx
  end;
  simpl;
  auto using andb_true_intro, orb_true_intro.
Qed.
