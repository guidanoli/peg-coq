From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.

(** Syntax **)
(************)

Inductive pat : Type :=
  | PEmpty : pat
  | PChar : ascii -> pat
  | PAnyChar : pat
  | PSequence : pat -> pat -> pat
  | PChoice : pat -> pat -> pat
  | PRepetition : pat -> pat
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
  | MRepetition1 :
      forall p s,
      matches p s Failure ->
      matches (PRepetition p) s (Success s)
  | MRepetition2 :
      forall p s s' res,
      matches p s (Success s') ->
      matches (PRepetition p) s' res ->
      matches (PRepetition p) s res
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

Example infinite_loop :
  forall p s,
  matches p s (Success s) ->
  ~ (exists res, matches (PRepetition p) s res).
Proof.
  intros p s H1 [res H2].
  remember (PRepetition p).
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

Lemma string_not_recursive :
  forall s a,
  ~ (s = String a s).
Proof.
  intros s a H.
  induction s.
  - discriminate.
  - destruct2.
    auto.
Qed.

Lemma append_empty :
  forall s,
  append s EmptyString = s.
Proof.
  intros.
  induction s.
  - simpl. trivial.
  - simpl. rewrite IHs. trivial.
Qed.

Lemma append_comm :
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

Lemma length_append :
  forall s1 s2,
  length (append s1 s2) = length s1 + length s2.
Proof.
  intros.
  induction s1.
  - auto.
  - simpl. rewrite IHs1. trivial.
Qed.

Lemma n_eq_m_plus_n :
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

Lemma length_zero :
  forall s,
  length s = 0 ->
  s = EmptyString.
Proof.
  intros.
  induction s.
  - trivial.
  - simpl in H. discriminate.
Qed.

Lemma empty_prefix :
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

Lemma append_is_empty :
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

Lemma mutual_prefixes :
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

(** Match function with gas **)

Fixpoint matches_comp p s gas {struct gas} :=
  match gas with
  | O => None
  | S gas' => match p with
              | PEmpty => Some (Success s)
              | PChar a => match s with
                           | EmptyString => Some Failure
                           | String a' s' => if (a =? a')%char
                                             then Some (Success s')
                                             else Some Failure
                           end
              | PAnyChar => match s with
                            | EmptyString => Some Failure
                            | String _ s' => Some (Success s')
                            end
              | PSequence p1 p2 => match matches_comp p1 s gas' with
                                   | Some (Success s') => matches_comp p2 s' gas'
                                   | res => res
                                   end
              | PChoice p1 p2 => match matches_comp p1 s gas' with
                                 | Some Failure => matches_comp p2 s gas'
                                 | res => res
                                 end
              | PRepetition p' => match matches_comp p' s gas' with
                                 | Some Failure => Some (Success s)
                                 | Some (Success s') => matches_comp p s' gas'
                                 | None => None
                                 end
              | PNot p' => match matches_comp p' s gas' with
                           | Some Failure => Some (Success s)
                           | Some (Success _) => Some Failure
                           | None => None
                           end
              end
  end.

Ltac injection_subst :=
  match goal with
  [ Hx: ?C _ = ?C _ |- _ ] =>
      injection Hx as Hx;
      try subst
  end.

Theorem matches_comp_correct :
  forall p s gas res,
  matches_comp p s gas = Some res ->
  matches p s res.
Proof with eauto using matches.
  intro p.
  induction p;
  intros;
  destruct gas;
  simpl in H;
  try discriminate.
  - injection_subst.
    constructor.
  - destruct s as [|a' s].
    + injection_subst.
      constructor.
    + destruct (ascii_dec a a').
      -- subst.
         rewrite Ascii.eqb_refl in H.
         injection_subst.
         constructor.
      -- assert ((a =? a')%char = false) as Haux by (apply Ascii.eqb_neq; trivial).
         rewrite Haux in H.
         injection_subst...
  - destruct s;
    injection_subst;
    constructor.
  - remember (matches_comp p1 s gas) as gres1 eqn:Hgres1.
    symmetry in Hgres1.
    destruct gres1 as [res1|];
    try discriminate.
    apply IHp1 in Hgres1.
    destruct res1.
    + injection_subst...
    + apply IHp2 in H...
  - remember (matches_comp p1 s gas) as gres1 eqn:Hgres1.
    symmetry in Hgres1.
    destruct gres1 as [res1|];
    try discriminate.
    apply IHp1 in Hgres1.
    destruct res1;
    try injection_subst...
  - remember (matches_comp p s gas) as gres' eqn:Hgres'.
    destruct gres' as [res'|];
    try discriminate.
    Abort.

(** Nullable pattern definition **)

(*
  If a pattern may match a string without consuming any
  characters, then it is nullable.
*)
Definition nullable p := exists s, matches p s (Success s).

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
  | PRepetition _ => true
  | PNot _ => true
  end.

Ltac apply_string_not_rec :=
  match goal with
  [ Hx: ?s = String ?a ?s |- _ ] =>
    exfalso;
    apply (string_not_recursive _ _ Hx)
  end.

(** Nullable pattern function soundness **)

Theorem nullable_comp_sound :
  forall p, nullable p -> nullable_comp p = true.
Proof.
  intros.
  unfold nullable in H.
  destruct H as [s H].
  remember (Success s) as res eqn:Hres.
  generalize dependent Hres.
  induction H; intro Hres;
  auto;
  try discriminate;
  try injection_subst;
  try apply_string_not_rec;
  subst;
  try match goal with
  [ Hx1: matches _ ?s1 (Success ?s2),
    Hx2: matches _ ?s2 (Success ?s1) |- _ ] =>
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

Lemma nullable_comp_false :
  forall p,
  nullable_comp p = false -> ~ nullable p.
Proof.
  intros p H1 H2.
  apply nullable_comp_sound in H2.
  rewrite H1 in H2.
  discriminate.
Qed.

(** Well-formed definition **)

(*
  A pattern is well-formed iff, for any input string,
  the match procedure yields a result.
*)
Definition wf p :=
  forall s, exists res, matches p s res.

(** Well-formed function **)

(*
  A computational version of wf.
*)
Fixpoint wf_comp p :=
  match p with
  | PEmpty => true
  | PChar _ => true
  | PAnyChar => true
  | PSequence p1 p2 => wf_comp p1 && wf_comp p2
  | PChoice p1 p2 => wf_comp p1 && wf_comp p2
  | PRepetition p => wf_comp p && negb (nullable_comp p)
  | PNot p => wf_comp p
  end.

(** Well-formed function safety **)

Theorem wf_comp_safe :
  forall p, wf_comp p = true -> wf p.
Proof with eauto using matches.
  intros p H.
  unfold wf.
  induction p;
  intro s;
  simpl in H;
  try match goal with
    [ H: _ && _ = true |- _ ] =>
      apply andb_prop in H as [H1 H2]
  end;
  repeat match goal with
    [ Hx: ?a, IHx: ?a -> ?b |- _ ] =>
      specialize (IHx Hx)
  end...
  - (* PChar *)
    induction s as [| a' s]...
    destruct (ascii_dec a a')...
    subst...
  - (* PAnyChar *)
    induction s...
  - (* PSequence *)
    specialize (IHp1 s).
    destruct IHp1 as [res1 IHp1].
    destruct res1 as [s1 |]...
    specialize (IHp2 s0).
    destruct IHp2 as [res2 IHp2]...
  - (* PChoice *)
    specialize (IHp1 s).
    destruct IHp1 as [res1 IHp1].
    destruct res1 as [s1 |]...
    specialize (IHp2 s).
    destruct IHp2 as [res2 IHp2]...
  - (* PRepetition *)
    rewrite negb_true_iff in H2.
    apply nullable_comp_false in H2.
    unfold nullable in H2.
    Abort.