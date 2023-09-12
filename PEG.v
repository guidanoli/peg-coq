From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.

Inductive pat : Type :=
  | PEmpty : pat
  | PChar : ascii -> pat
  | PAnyChar : pat
  | PSequence : pat -> pat -> pat
  | PChoice : pat -> pat -> pat
  | PKleene : pat -> pat
  | PNot : pat -> pat
  .

Inductive matches : pat -> string -> option string -> Prop :=
  | MEmpty :
      forall s,
      matches PEmpty s (Some s)
  | MChar1 :
      forall a,
      matches (PChar a) EmptyString None
  | MChar2 :
      forall a s,
      matches (PChar a) (String a s) (Some s)
  | MChar3 :
      forall a1 a2 s,
      a1 <> a2 ->
      matches (PChar a1) (String a2 s) None
  | MAnyChar1 :
      matches PAnyChar EmptyString None
  | MAnyChar2 :
      forall a s,
      matches PAnyChar (String a s) (Some s)
  | MSequence1 :
      forall p1 p2 s,
      matches p1 s None ->
      matches (PSequence p1 p2) s None
  | MSequence2 :
      forall p1 p2 s s' res,
      matches p1 s (Some s') ->
      matches p2 s' res ->
      matches (PSequence p1 p2) s res
  | MChoice1 :
      forall p1 p2 s s',
      matches p1 s (Some s') ->
      matches (PChoice p1 p2) s (Some s')
  | MChoice2 :
      forall p1 p2 s res,
      matches p1 s None ->
      matches p2 s res ->
      matches (PChoice p1 p2) s res
  | MKleene1 :
      forall p s,
      matches p s None ->
      matches (PKleene p) s (Some s)
  | MKleene2 :
      forall p s s' res,
      matches p s (Some s') ->
      matches (PKleene p) s' res ->
      matches (PKleene p) s res
  | MNot1 :
      forall p s,
      matches p s None ->
      matches (PNot p) s (Some s)
  | MNot2 :
      forall p s s',
      matches p s (Some s') ->
      matches (PNot p) s None
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
  matches p s (Some s) ->
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

Theorem append_comm :
  forall s1 s2 s3,
  append s1 (append s2 s3) = append (append s1 s2) s3.
Proof.
  intros.
  induction s1.
  - simpl. trivial.
  - simpl. rewrite IHs1. trivial.
Qed.

Theorem matches_prefix :
  forall p s res s2,
  matches p s res ->
  res = Some s2 ->
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
  [ IHx: forall sb, Some ?sx = Some sb -> exists sa, ?sy = append sa sb |- _ ] =>
      assert (Some sx = Some sx) as Haux;
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
