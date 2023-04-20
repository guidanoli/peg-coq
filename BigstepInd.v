From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
Open Scope string.

(* Parsing Expression *)
Inductive Exp : Type :=
  | ETrue : Exp (* Always matches *)
  | EFalse : Exp (* Never matches *)
  | EAny : Exp (* Matches any ASCII character *)
  | ETerminal : ascii -> Exp (* Matches an ASCII character *)
  | ENonTerminal : nat -> Exp (* Matches a non-terminal *)
  | ESequence : Exp -> Exp -> Exp (* Matches two subexpressions in sequence *)
  | EOrderedChoice : Exp -> Exp -> Exp (* Matches one of two subexpressions *)
  | ENotPredicate : Exp -> Exp (* Matches if subexpression doesn't *)
  | EKleeneStar : Exp -> Exp (* Matches a subexpression as many times as possible *)
  .

Notation "A ';' B" := (ESequence A B) (at level 70, right associativity).
Notation "A '//' B" := (EOrderedChoice A B) (at level 90, right associativity).
Notation "'!' A" := (ENotPredicate A) (at level 60, right associativity).
Notation "A '~'" := (EKleeneStar A) (at level 60, right associativity).

(* Parsing Expression Grammar
   Each PEG is composed of a finite set of parsing rule *)
Definition PEG : Type := list Exp.

(* Match an expression
   Given a PEG, a parsing expression, and an input string,
   can either result in success (with `Some` leftover string)
   or failure (with `None` left) *)
Inductive Match : PEG -> Exp -> string -> option string -> Prop :=
  | METrue :
      forall peg s,
      Match peg ETrue s (Some s)
  | MEFalse :
      forall peg s,
      Match peg EFalse s None
  | MEAny1 :
      forall peg a s,
      Match peg EAny (String a s) (Some s)
  | MEAny2 :
      forall peg,
      Match peg EAny EmptyString None
  | METerminal1 :
      forall peg a s,
      Match peg (ETerminal a) (String a s) (Some s)
  | METerminal2 :
      forall peg a a' s,
      a <> a' ->
      Match peg (ETerminal a) (String a' s) None
  | METerminal3 :
      forall peg a,
      Match peg (ETerminal a) EmptyString None
  | MENonTerminal :
      forall peg i s e res,
      nth_error peg i = Some e ->
      Match peg e s res ->
      Match peg (ENonTerminal i) s res
  | MESequence1 :
      forall peg e1 e2 s s' res,
      Match peg e1 s (Some s') ->
      Match peg e2 s' res ->
      Match peg (e1; e2) s res
  | MESequence2 :
      forall peg e1 e2 s,
      Match peg e1 s None ->
      Match peg (e1; e2) s None
  | MEOrderedChoice1 :
      forall peg e1 e2 s s',
      Match peg e1 s (Some s') ->
      Match peg (e1 // e2) s (Some s')
  | MEOrderedChoice2 :
      forall peg e1 e2 s res,
      Match peg e1 s None ->
      Match peg e2 s res ->
      Match peg (e1 // e2) s res
  | MENotPredicate1 :
      forall peg e s,
      Match peg e s None ->
      Match peg (!e) s (Some s)
  | MENotPredicate2 :
      forall peg e s s',
      Match peg e s (Some s') ->
      Match peg (!e) s None
  | MEKleeneStar1 :
      forall peg e s s',
      Match peg (e; e~) s (Some s') ->
      Match peg (e~) s (Some s')
  | MEKleeneStar2 :
      forall peg e s,
      Match peg e s None ->
      Match peg (e~) s (Some s)
  .

(* Invert Match proposition with Exp e *)
Ltac match_exp e :=
  match goal with
  | H: Match _ e _ _ |- _ =>
      inversion H; subst; eauto using Match
  end.

(* Try establishing the equality e1 = e2 from
   x = c e1 and x = c e2 *)
Ltac trivial_congruence :=
  match goal with
  [ H1: ?x = ?c ?e1,
    H2: ?x = ?c ?e2 |- _ ] =>
        rewrite -> H1 in H2;
        assert (e1 = e2);
        try (congruence; trivial);
        clear H2;
        subst
  end.

(* Parsing a string against a parsing expression
   in the context of a PEG always outputs the same result *)
Theorem match_deterministic :
  forall peg e s r1 r2,
  Match peg e s r1 ->
  Match peg e s r2 ->
  r1 = r2.
Proof.
  intros peg e s r1 r2 H1 H2.
  generalize dependent r2.
  induction H1; intros r2 H';
  inversion H'; subst;
  try congruence;
  try trivial_congruence;
  try match goal with
  [ IH: forall r, Match ?peg (?e; ?e') ?s r -> Some _ = r,
    H: Match ?peg ?e ?s None |- _ ] =>
        assert (Match peg (e; e') s None);
        eauto using Match
  end;
  try match goal with
  [ IH: forall r, Match ?peg ?e ?s r -> None = r,
    H: Match peg (?e; ?e') ?s (Some _) |- _ ] =>
        inversion H; subst
  end;
  try match goal with
  [ IH: forall r, Match ?peg ?e ?s r -> _ = r,
    H: Match ?peg ?e ?s _ |- _ ] =>
      apply IH in H
  end;
  try discriminate;
  try match goal with
    [ H: ?c ?e1 = ?c ?e2 |- _ ] =>
        assert (e1 = e2);
        try (congruence; trivial);
        clear H;
        subst
  end;
  auto.
Qed.

(* Use match_deterministic to discriminate
   different result types *)
Ltac discriminate_results :=
  match goal with
  [ H1: Match ?peg ?e ?s (Some ?s'),
    H2: Match ?peg ?e ?s None |- _ ] =>
        assert (Some s' = None);
        eauto using match_deterministic;
        discriminate
  end.

(* Use match_deterministic to unify
   two successful (Some) results *)
Ltac unify_results :=
   match goal with
   [ H1: Match ?peg ?e ?s (Some ?s1),
     H2: Match ?peg ?e ?s (Some ?s2) |- _ ] =>
         assert (Some s1 = Some s2) as Haux;
         eauto using match_deterministic;
         assert (s1 = s2);
         try congruence;
         clear Haux;
         subst
   end.

(* Two parsing expressions are said equivalent in the
   context of some PEG iff for every input string,
   they output the same result *)
Definition equivalent (peg : PEG) (e1 e2 : Exp) : Prop :=
  forall s res,
  Match peg e1 s res <-> Match peg e2 s res.

(* Proving that the sequence expression is associative *)
Theorem sequence_assoc :
  forall peg e1 e2 e3,
  equivalent peg (e1; (e2; e3))
                 ((e1; e2); e3).
Proof.
  intros.
  constructor;
  intros H;
  inversion H; subst;
  try match_exp (e1; e2);
  try match_exp (e2; e3);
  eauto using Match.
Qed.

(* Proving that the ordered choice expression is associative *)
Theorem ordered_choice_assoc :
  forall peg e1 e2 e3,
  equivalent peg (e1 // (e2 // e3))
                 ((e1 // e2) // e3).
Proof.
  intros.
  constructor;
  intros H;
  inversion H; subst;
  try match_exp (e1 // e2);
  try match_exp (e2 // e3);
  eauto using Match.
Qed.

(* Show that a false first choice is useless *)
Theorem first_choice_false :
  forall peg e,
  equivalent peg e (EFalse // e).
Proof.
  intros.
  constructor;
  intros H.
  - (* -> *)
    eauto using Match.
  - (* <- *)
    inversion H; subst;
    eauto using Match;
    match_exp EFalse.
Qed.

(* Show that a true first choice is enough *)
Theorem first_choice_true :
  forall peg e,
  equivalent peg ETrue (ETrue // e).
Proof.
  intros.
  constructor;
  intros H.
  - (* -> *)
    match_exp ETrue.
  - (* <- *)
    match_exp (ETrue // e).
    match_exp (ETrue).
Qed.

(* Show that a false second choice is useless *)
Theorem second_choice_false :
  forall peg e,
  equivalent peg e (e // EFalse).
Proof.
  intros.
  constructor;
  intros H.
  - (* -> *)
    destruct res; econstructor; eauto using Match.
  - (* <- *)
    inversion H; subst; auto.
    destruct res; auto.
    match_exp EFalse.
Qed.

(* Show that a true first sequence part is useless *)
Theorem first_part_true :
  forall peg e,
  equivalent peg e (ETrue; e).
Proof.
  intros.
  constructor;
  intros H;
  inversion H; subst;
  eauto using Match;
  match_exp ETrue.
Qed.

(* Show that a false first sequence part is enough *)
Theorem first_part_false :
  forall peg e,
  equivalent peg EFalse (EFalse; e).
Proof.
  intros.
  constructor;
  intros H;
  inversion H; subst;
  eauto using Match;
  match_exp EFalse.
Qed.

Theorem choice_sequence_distributive_left :
  forall peg e1 e2 e3,
  equivalent peg (e1; (e2 // e3))
                 ((e1; e2) // (e1; e3)).
Proof.
  intros.
  constructor;
  intros H;
  inversion H; subst;
  try match_exp (e2 // e3);
  try match_exp (e1; e2);
  try match_exp (e1; e3);
  try unify_results;
  try discriminate_results;
  eauto using Match.
Qed.

Theorem append_assoc :
  forall s1 s2 s3,
  (s1 ++ s2) ++ s3 = s1 ++ (s2 ++ s3).
Proof.
  intros.
  induction s1 as [|a s1 IH].
  - (* EmptyString *) trivial.
  - (* String a s1 *) simpl. rewrite IH. trivial.
Qed.

Theorem result_suffix :
  forall peg e s res s2,
  Match peg e s res ->
  res = Some s2 ->
  exists s1, s = s1 ++ s2.
Proof.
  intros.
  generalize dependent s2.
  induction H;
  subst;
  intros s2 Hs2;
  try match goal with
  [ H: Some _ = Some _ |- _ ] =>
      injection H as H;
      subst
  end;
  try match goal with
  [ |- exists s1, ?s2 = s1 ++ ?s2 ] =>
      exists "";
      trivial
  end;
  try match goal with
  [ |- exists s1, String ?a ?s2 = s1 ++ ?s2 ] =>
      exists (String a EmptyString);
      trivial
  end;
  try match goal with
  [ IH1: forall sx, Some ?s' = Some sx -> exists sy, ?s = sy ++ sx,
    IH2: forall sx, ?res = Some sx -> exists sy, ?s' = sy ++ sx,
    H1: ?res = Some ?s2 |- exists s1, ?s = s1 ++ ?s2 ] =>
      apply IH2 in H1;
      destruct H1 as [sk H1];
      assert (Some s' = Some s') as H2; trivial;
      apply IH1 in H2;
      destruct H2 as [sm H2];
      exists (sm ++ sk);
      rewrite H1 in H2;
      rewrite append_assoc
  end;
  try discriminate;
  eauto.
Qed.

(* And predicate *)
Definition EAndPredicate (e : Exp) : Exp :=
  !!e.

Notation "'&' A" := (EAndPredicate A) (at level 60, right associativity).

(* If-then-else expression *)
Definition EIf (e1 e2 e3 : Exp) : Exp :=
  &e1; e2 // !e1; e3.

Notation "'if&' A 'then' B 'else' C" := (EIf A B C) (at level 60, right associativity).

(* If the condition is true, then
   the whole 'if-then-else' is equivalent to the 'then' *)
Theorem if_condition_succeeds :
  forall peg e1 e2 e3 s s' res,
  Match peg e1 s (Some s') ->
  Match peg e2 s res ->
  Match peg (if& e1 then e2 else e3) s res.
Proof.
  intros.
  assert (Match peg (&e1) s (Some s));
  destruct res;
  eauto using Match.
Qed.

Ltac contradict_match e :=
  match goal with
  [ Hf: forall r, ~ Match _ e _ r,
    Hx: Match _ e _ _ |- _ ] =>
      apply Hf in Hx; contradiction
  end.

(* If the condition is true, but
   the 'then' expression is undecided, then
   the whole 'if-then-else' is undecided *)
Theorem if_condition_succeeds_then_undec :
  forall peg e1 e2 e3 s s',
  Match peg e1 s (Some s') ->
  (forall res, ~ Match peg e2 s res) ->
  (forall res, ~ Match peg (if& e1 then e2 else e3) s res).
Proof.
  intros peg e1 e2 e3 s s' H1 H2 r H3.
  match_exp (if& e1 then e2 else e3);
  match_exp (&e1;e2);
  match_exp (&e1);
  match_exp (!e1);
  try contradict_match e2;
  try discriminate_results.
Qed.

(* If the condition is false, then
   the whole 'if-then-else' is equivalent to the 'else' *)
Theorem if_condition_fails :
  forall peg e1 e2 e3 s res,
  Match peg e1 s None ->
  Match peg e3 s res ->
  Match peg (if& e1 then e2 else e3) s res.
Proof.
  intros.
  assert (Match peg (&e1) s None);
  destruct res;
  eauto using Match.
Qed.

(* If the condition is false, but
   the 'else' expression is undecided, then
   the whole 'if-then-else' is undecided *)
Theorem if_condition_fails_else_undec :
  forall peg e1 e2 e3 s,
  Match peg e1 s None ->
  (forall res, ~ Match peg e3 s res) ->
  (forall res, ~ Match peg (if& e1 then e2 else e3) s res).
Proof.
  intros peg e1 e2 e3 s H1 H2 r H3.
  match_exp (if& e1 then e2 else e3);
  match_exp (&e1;e2);
  match_exp (&e1);
  match_exp (!e1);
  try discriminate_results;
  match_exp (!e1;e3);
  match_exp (!e1);
  try discriminate_results;
  try contradict_match e3.
Qed.

(* If the condition is undecided, then
   the whole 'if-then-else' is undecided *)
Theorem if_condition_undec :
  forall peg e1 e2 e3 s,
  (forall res1, ~ Match peg e1 s res1) ->
  (forall res2, ~ Match peg (if& e1 then e2 else e3) s res2).
Proof.
  intros peg e1 e2 e3 s H1 r H2.
  match_exp (if& e1 then e2 else e3);
  match_exp (&e1;e2);
  match_exp (&e1);
  match_exp (!e1);
  contradict_match e1.
Qed.

(* We define a set of ASCII characters as a function of ascii to boolean values *)
Definition charset : Type := ascii -> bool.

(* An empty set is that where, for every character, the return is false *)
Definition emptyset : charset := (fun _ => false).

(* A full set is that where, for every character, the return is true *)
Definition fullset : charset := (fun _ => true).

(* A singleton only contains one character
   We could define this function as (fun a a' => Ascii.eqb a a'),
   but we can use currying and define it simply as Ascii.eqb *)
Definition singleton : ascii -> charset := Ascii.eqb.

(* A set union contains the elements of two sets.
   By how we've defined charsets, this corresponds to the boolean 'or' *)
Definition union (cs1 cs2 : charset) : charset := (fun a => cs1 a || cs2 a).

(* The set complement operator uses the boolean 'not' *)
Definition complement (cs : charset) : charset := (fun a => negb (cs a)).

Reserved Notation "cs1 '<==[' e '@' peg ']==' cs2" (at level 50).

(*
   "First-and-follow"

   `First peg e cs1 cs2` or `cs1 <==[ e @ peg ]== cs2`

   peg - the PEG used to contextualize the expression `e`
   e   - the expression itself being parsed
   cs1 - "first": the set of characters that will not fail the expression `e`
         and whatever comes after
   cs2 - "follow": the set of characters allowed after expression `e`,
         as if there expression `e` were in a sequence expression and this
         was the first of the following expression
*)
Inductive First : PEG -> Exp -> charset -> charset -> Prop :=
  | FETrue :
      forall peg cs,
      cs <==[ ETrue @ peg ]== cs
  | FEFalse :
      forall peg cs,
      emptyset <==[ EFalse @ peg ]== cs
  | FEAny :
      forall peg cs,
      fullset <==[ EAny @ peg ]== cs
  | FETerminal :
      forall peg cs a,
      singleton a <==[ ETerminal a @ peg ]== cs
  | FENonTerminal :
      forall peg i e cs cs',
      nth_error peg i = Some e ->
      cs <==[ e @ peg ]== cs' ->
      cs <==[ ENonTerminal i @ peg ]== cs'
  | FESequence :
      forall peg cs cs' cs'' e1 e2,
      cs <==[ e1 @ peg ]== cs' ->
      cs' <==[ e2 @ peg ]== cs'' ->
      cs <==[ e1; e2 @ peg ]== cs''
  | FEOrderedChoice :
      forall peg cs1 cs2 cs' e1 e2,
      cs1 <==[ e1 @ peg ]== cs' ->
      cs2 <==[ e2 @ peg ]== cs' ->
      union cs1 cs2 <==[ e1 // e2 @ peg ]== cs'
  | FENotPredicate :
      forall peg cs cs' e,
      cs <==[ e @ peg ]== cs' ->
      union (complement cs) cs' <==[ !e @ peg ]== cs'
  | FEKleeneStar :
      forall peg cs cs' e,
      cs <==[ e @ peg ]== cs' ->
      union cs cs' <==[ e~ @ peg ]== cs'

where "cs1 '<==[' e '@' peg ']==' cs2" := (First peg e cs1 cs2).

Theorem first_deterministic :
  forall peg e cs1 cs2 cs',
  cs1 <==[ e @ peg ]== cs' ->
  cs2 <==[ e @ peg ]== cs' ->
  cs1 = cs2.
Proof.
  intros peg e cs1 cs2 cs' H1 H2.
  generalize dependent cs2.
  induction H1; intros cs2' H2;
  inversion H2; subst;
  try trivial_congruence;
  try repeat match goal with
  [ IH: forall csx, csx <==[ ?e @ ?peg ]== ?cs' -> _ = csx,
    H: _ <==[ ?e @ ?peg ]== ?cs' |- _ ] =>
        apply IH in H; subst
  end;
  auto.
Qed.
