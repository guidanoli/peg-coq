(* @author Guilherme Dantas *)

From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Peg Require Import Nth.
Open Scope string.

(* Parsing Expression
   Each expression can mention non-terminals i < n *)
Inductive Exp {n : nat} : Type :=
  | ETrue : Exp (* Always matches *)
  | EFalse : Exp (* Never matches *)
  | EAny : Exp (* Matches any ASCII character *)
  | ETerminal : ascii -> Exp (* Matches an ASCII character *)
  | ENonTerminal : forall i, i < n -> Exp (* Matches a non-terminal *)
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
   Each grammar is composed of n parsing rules *)
Inductive Grammar (n : nat) : Type :=
  | PEG : forall (l : list (@Exp n)), n = length l -> Grammar n.

(* Get the i-th rule of a grammar of n rules, where i < n *)
Definition rule {n : nat} (g : Grammar n) (i : nat) (Hi : i < n) : Exp :=
  match g with
  | PEG _ l Hlen => nth l i (PeanoNat.Nat.lt_stepr _ _ _ Hi Hlen)
  end.

Theorem rule_deterministic :
  forall n (g : Grammar n) i H1 H2,
  rule g i H1 = rule g i H2.
Proof.
  intros.
  remember (rule g i H1) as e1.
  remember (rule g i H2) as e2.
  destruct g.
  repeat match goal with
  | Hx: _ = rule _ _ _ |- _ =>
      unfold rule in Hx;
      symmetry in Hx;
      apply nth_equal in Hx
  end.
  match goal with
  | Hx: ?a = Some _, Hy: ?a = Some _ |- _ =>
      rewrite Hx in Hy;
      injection Hy
  end.
  trivial.
Qed.

(* Match an expression
   Given a grammar, a parsing expression, and an input string,
   can either result in success (with `Some` leftover string)
   or failure (with `None` left) *)
Inductive Match (n : nat) : Grammar n -> Exp -> string -> option string -> Prop :=
  | METrue :
      forall g s,
      Match n g ETrue s (Some s)
  | MEFalse :
      forall g s,
      Match n g EFalse s None
  | MEAny1 :
      forall g a s,
      Match n g EAny (String a s) (Some s)
  | MEAny2 :
      forall g,
      Match n g EAny EmptyString None
  | METerminal1 :
      forall g a s,
      Match n g (ETerminal a) (String a s) (Some s)
  | METerminal2 :
      forall g a a' s,
      a <> a' ->
      Match n g (ETerminal a) (String a' s) None
  | METerminal3 :
      forall g a,
      Match n g (ETerminal a) EmptyString None
  | MENonTerminal :
      forall g i s H res,
      Match n g (rule g i H) s res ->
      Match n g (ENonTerminal i H) s res
  | MESequence1 :
      forall g e1 e2 s s' res,
      Match n g e1 s (Some s') ->
      Match n g e2 s' res ->
      Match n g (e1; e2) s res
  | MESequence2 :
      forall g e1 e2 s,
      Match n g e1 s None ->
      Match n g (e1; e2) s None
  | MEOrderedChoice1 :
      forall g e1 e2 s s',
      Match n g e1 s (Some s') ->
      Match n g (e1 // e2) s (Some s')
  | MEOrderedChoice2 :
      forall g e1 e2 s res,
      Match n g e1 s None ->
      Match n g e2 s res ->
      Match n g (e1 // e2) s res
  | MENotPredicate1 :
      forall g e s,
      Match n g e s None ->
      Match n g (!e) s (Some s)
  | MENotPredicate2 :
      forall g e s s',
      Match n g e s (Some s') ->
      Match n g (!e) s None
  | MEKleeneStar1 :
      forall g e s s' res,
      Match n g e s (Some s') ->
      Match n g (e~) s' res ->
      Match n g (e~) s res
  | MEKleeneStar2 :
      forall g e s,
      Match n g e s None ->
      Match n g (e~) s (Some s)
  .

(* Invert Match proposition with Exp e *)
Ltac match_exp e :=
  match goal with
  | H: Match _ _ e _ _ |- _ =>
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
   in the context of a grammar always outputs the same result *)
Theorem match_deterministic :
  forall n g e s r1 r2,
  Match n g e s r1 ->
  Match n g e s r2 ->
  r1 = r2.
Proof.
  intros n g e s r1 r2 H1 H2.
  generalize dependent r2.
  induction H1; intros r2 H';
  inversion H'; subst;
  try congruence;
  try trivial_congruence;
  try match goal with
  [ IH: forall r, Match ?n ?g (?e; ?e') ?s r -> Some _ = r,
    H: Match ?n ?g ?e ?s None |- _ ] =>
        assert (Match n g (e; e') s None);
        eauto using Match
  end;
  try match goal with
  [ IH: forall r, Match ?n ?g ?e ?s r -> None = r,
    H: Match ?n g (?e; ?e') ?s (Some _) |- _ ] =>
        inversion H; subst
  end;
  try match goal with
  [ IH: forall r, Match ?n ?g ?e ?s r -> _ = r,
    H: Match ?n ?g ?e ?s _ |- _ ] =>
        apply IH in H
  end;
  try match goal with
  [ IH: forall rx, Match ?n ?g (rule ?g ?i ?H1) ?s rx -> ?r = rx,
    H: Match ?n ?g (rule ?g ?i ?H2) ?s ?r' |- ?r = ?r' ] =>
        erewrite rule_deterministic in H
  end;
  try discriminate;
  try match goal with
  [ H: ?c ?e1 = ?c ?e2 |- _ ] =>
        assert (e1 = e2);
        try (congruence; trivial);
        clear H;
        subst
  end;
  eauto.
Qed.

(* Use match_deterministic to discriminate
   different result types *)
Ltac discriminate_results :=
  match goal with
  [ H1: Match ?n ?g ?e ?s (Some ?s'),
    H2: Match ?n ?g ?e ?s None |- _ ] =>
        assert (Some s' = None);
        eauto using match_deterministic;
        discriminate
  end.

(* Use match_deterministic to unify
   two successful (Some) results *)
Ltac unify_results :=
   match goal with
   [ H1: Match ?n ?g ?e ?s (Some ?s1),
     H2: Match ?n ?g ?e ?s (Some ?s2) |- _ ] =>
         assert (Some s1 = Some s2) as Haux;
         eauto using match_deterministic;
         assert (s1 = s2);
         try congruence;
         clear Haux;
         subst
   end.

(* Two parsing expressions are said equivalent in the
   context of some grammar iff for every input string,
   they output the same result *)
Definition equivalent (n : nat) (g : Grammar n) (e1 e2 : Exp) : Prop :=
  forall s res,
  Match n g e1 s res <-> Match n g e2 s res.

(* Proving that the sequence expression is associative *)
Theorem sequence_assoc :
  forall n g e1 e2 e3,
  equivalent n g (e1; (e2; e3))
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
  forall n g e1 e2 e3,
  equivalent n g (e1 // (e2 // e3))
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
  forall n g e,
  equivalent n g e (EFalse // e).
Proof.
  intros.
  constructor;
  intros H.
  - (* -> *)
    eauto using Match.
  - (* <- *)
    inversion H; subst;
    eauto using Match;
    match_exp (@EFalse n).
Qed.

(* Show that a true first choice is enough *)
Theorem first_choice_true :
  forall n g e,
  equivalent n g ETrue (ETrue // e).
Proof.
  intros.
  constructor;
  intros H.
  - (* -> *)
    match_exp (@ETrue n).
  - (* <- *)
    match_exp (ETrue // e).
    match_exp (@ETrue n).
Qed.

(* Show that a false second choice is useless *)
Theorem second_choice_false :
  forall n g e,
  equivalent n g e (e // EFalse).
Proof.
  intros.
  constructor;
  intros H.
  - (* -> *)
    destruct res; econstructor; eauto using Match.
  - (* <- *)
    inversion H; subst; auto.
    destruct res; auto.
    match_exp (@EFalse n).
Qed.

(* Show that a true first sequence part is useless *)
Theorem first_part_true :
  forall n g e,
  equivalent n g e (ETrue; e).
Proof.
  intros.
  constructor;
  intros H;
  inversion H; subst;
  eauto using Match;
  match_exp (@ETrue n).
Qed.

(* Show that a false first sequence part is enough *)
Theorem first_part_false :
  forall n g e,
  equivalent n g EFalse (EFalse; e).
Proof.
  intros.
  constructor;
  intros H;
  inversion H; subst;
  eauto using Match;
  match_exp (@EFalse n).
Qed.

Theorem choice_sequence_distributive_left :
  forall n g e1 e2 e3,
  equivalent n g (e1; (e2 // e3))
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
  forall n g e s res s2,
  Match n g e s res ->
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
Definition EAndPredicate {n : nat} (e : @Exp n) : Exp := !!e.

Notation "'&' A" := (EAndPredicate A) (at level 60, right associativity).

(* If-then-else expression *)
Definition EIf {n : nat} (e1 e2 e3 : @Exp n) : Exp :=
  &e1; e2 // !e1; e3.

Notation "'if&' A 'then' B 'else' C" := (EIf A B C) (at level 60, right associativity).

(* If the condition is true, then
   the whole 'if-then-else' is equivalent to the 'then' *)
Theorem if_condition_succeeds :
  forall n g e1 e2 e3 s s' res,
  Match n g e1 s (Some s') ->
  Match n g e2 s res ->
  Match n g (if& e1 then e2 else e3) s res.
Proof.
  intros.
  assert (Match n g (&e1) s (Some s));
  destruct res;
  eauto using Match.
Qed.

Ltac contradict_match e :=
  match goal with
  [ Hf: forall r, ~ Match _ _ e _ r,
    Hx: Match _ _ e _ _ |- _ ] =>
      apply Hf in Hx; contradiction
  end.

(* If the condition is true, but
   the 'then' expression is undecided, then
   the whole 'if-then-else' is undecided *)
Theorem if_condition_succeeds_then_undec :
  forall n g e1 e2 e3 s s',
  Match n g e1 s (Some s') ->
  (forall res, ~ Match n g e2 s res) ->
  (forall res, ~ Match n g (if& e1 then e2 else e3) s res).
Proof.
  intros n g e1 e2 e3 s s' H1 H2 r H3.
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
  forall n g e1 e2 e3 s res,
  Match n g e1 s None ->
  Match n g e3 s res ->
  Match n g (if& e1 then e2 else e3) s res.
Proof.
  intros.
  assert (Match n g (&e1) s None);
  destruct res;
  eauto using Match.
Qed.

(* If the condition is false, but
   the 'else' expression is undecided, then
   the whole 'if-then-else' is undecided *)
Theorem if_condition_fails_else_undec :
  forall n g e1 e2 e3 s,
  Match n g e1 s None ->
  (forall res, ~ Match n g e3 s res) ->
  (forall res, ~ Match n g (if& e1 then e2 else e3) s res).
Proof.
  intros n g e1 e2 e3 s H1 H2 r H3.
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
  forall n g e1 e2 e3 s,
  (forall res1, ~ Match n g e1 s res1) ->
  (forall res2, ~ Match n g (if& e1 then e2 else e3) s res2).
Proof.
  intros n g e1 e2 e3 s H1 r H2.
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

Reserved Notation "cs1 '<==[' e '@' g ']==' cs2" (at level 50).

(*
   "First-and-follow"

   `First g e cs1 cs2` or `cs1 <==[ e @ g ]== cs2`

   g - the grammar used to contextualize the expression `e`
   e   - the expression itself being parsed
   cs1 - "first": the set of characters that will not fail the expression `e`
         and whatever comes after
   cs2 - "follow": the set of characters allowed after expression `e`,
         as if there expression `e` were in a sequence expression and this
         was the first of the following expression
*)
Inductive First (n : nat) : Grammar n -> @Exp n -> charset -> charset -> Prop :=
  | FETrue :
      forall g cs,
      cs <==[ ETrue @ g ]== cs
  | FEFalse :
      forall g cs,
      emptyset <==[ EFalse @ g ]== cs
  | FEAny :
      forall g cs,
      fullset <==[ EAny @ g ]== cs
  | FETerminal :
      forall g cs a,
      singleton a <==[ ETerminal a @ g ]== cs
  | FENonTerminal :
      forall g i H cs cs',
      cs <==[ rule g i H @ g ]== cs' ->
      cs <==[ ENonTerminal i H @ g ]== cs'
  | FESequence :
      forall g cs cs' cs'' e1 e2,
      cs <==[ e1 @ g ]== cs' ->
      cs' <==[ e2 @ g ]== cs'' ->
      cs <==[ e1; e2 @ g ]== cs''
  | FEOrderedChoice :
      forall g cs1 cs2 cs' e1 e2,
      cs1 <==[ e1 @ g ]== cs' ->
      cs2 <==[ e2 @ g ]== cs' ->
      union cs1 cs2 <==[ e1 // e2 @ g ]== cs'
  | FENotPredicate :
      forall g cs cs' e,
      cs <==[ e @ g ]== cs' ->
      union (complement cs) cs' <==[ !e @ g ]== cs'
  | FEKleeneStar :
      forall g cs cs' e,
      cs <==[ e @ g ]== cs' ->
      union cs cs' <==[ e~ @ g ]== cs'

where "cs1 '<==[' e '@' g ']==' cs2" := (First _ g e cs1 cs2).

Theorem first_deterministic :
  forall n (g : Grammar n) e cs1 cs2 cs',
  cs1 <==[ e @ g ]== cs' ->
  cs2 <==[ e @ g ]== cs' ->
  cs1 = cs2.
Proof.
  intros n g e cs1 cs2 cs' H1 H2.
  generalize dependent cs2.
  induction H1; intros cs2' H2;
  inversion H2; subst;
  try trivial_congruence;
  try match goal with
  [ IH: forall csx, csx <==[ rule ?g ?i ?H1 @ ?g ]== ?cs' -> _ = csx,
    H: _ <==[ rule ?g ?i ?H2 @ ?g ]== ?cs' |- _ ] =>
        erewrite rule_deterministic in H
  end;
  try repeat match goal with
  [ IH: forall csx, csx <==[ ?e @ ?g ]== ?cs' -> _ = csx,
    H: _ <==[ ?e @ ?g ]== ?cs' |- _ ] =>
        apply IH in H; subst
  end;
  eauto.
Qed.
