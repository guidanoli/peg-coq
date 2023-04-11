From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.

(* Parsing Expression *)
Inductive Exp : Type :=
  | ETrue : Exp (* Always matches *)
  | EFalse : Exp (* Never matches *)
  | ETerminal : ascii -> Exp (* Matches an ASCII character *)
  | ENonTerminal : nat -> Exp (* Matches a non-terminal *)
  | ESequence : Exp -> Exp -> Exp (* Matches two subexpressions in sequence *)
  | EOrderedChoice : Exp -> Exp -> Exp (* Matches one of two subexpressions *)
  | ENotPredicate : Exp -> Exp (* Matches if subexpression doesn't *)
  .

Notation "A ';' B" := (ESequence A B) (at level 70, right associativity).
Notation "A '//' B" := (EOrderedChoice A B) (at level 90, right associativity).
Notation "'!' A" := (ENotPredicate A) (at level 60, right associativity).

(* Parsing Expression Grammar
   Each PEG is composed of a finite set of parsing rule *)
Definition PEG : Type := list Exp.

(* Match an expression
   Given a PEG, a parsing expression, and an input string,
   can either result in success (with `Some` leftover string)
   or failure (with `None` left) *)
Inductive Match : PEG -> Exp -> string -> option string -> Prop :=
  | PETrue :
      forall peg s,
      Match peg ETrue s (Some s)
  | PEFalse :
      forall peg s,
      Match peg EFalse s None
  | PETerminal1 :
      forall peg a s,
      Match peg (ETerminal a) (String a s) (Some s)
  | PETerminal2 :
      forall peg a a' s,
      a <> a' ->
      Match peg (ETerminal a) (String a' s) None
  | PETerminal3 :
      forall peg a,
      Match peg (ETerminal a) EmptyString None
  | PENonTerminal :
      forall peg i s e res,
      nth_error peg i = Some e ->
      Match peg e s res ->
      Match peg (ENonTerminal i) s res
  | PESequence1 :
      forall peg e1 e2 s s' res,
      Match peg e1 s (Some s') ->
      Match peg e2 s' res ->
      Match peg (e1; e2) s res
  | PESequence2 :
      forall peg e1 e2 s,
      Match peg e1 s None ->
      Match peg (e1; e2) s None
  | PEOrderedChoice1 :
      forall peg e1 e2 s s',
      Match peg e1 s (Some s') ->
      Match peg (e1 // e2) s (Some s')
  | PEOrderedChoice2 :
      forall peg e1 e2 s res,
      Match peg e1 s None ->
      Match peg e2 s res ->
      Match peg (e1 // e2) s res
  | PENotPredicate1 :
      forall peg e s,
      Match peg e s None ->
      Match peg (!e) s (Some s)
  | PENotPredicate2 :
      forall peg e s s',
      Match peg e s (Some s') ->
      Match peg (!e) s None
  .

(* Invert Match proposition with Exp e *)
Ltac match_exp e :=
  match goal with
  | H: Match _ e _ _ |- _ =>
      inversion H; subst; auto
  end.

(* Parsing a string against a parsing expression
   in the context of a PEG always outputs the same result *)
Theorem deterministic_result :
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
  try match goal with
  [ H1: ?x = ?c ?e1,
    H2: ?x = ?c ?e2 |- _ ] =>
        rewrite -> H1 in H2;
        assert (e1 = e2);
        try (congruence; trivial);
        clear H2;
        subst
  end;
  try match goal with
    [ IH: forall _, Match _ ?e _ _ -> _,
      H: Match _ ?e _ _ |- _ ] =>
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

(* Use deterministic_result to discriminate
   different result types *)
Ltac discriminate_results :=
  match goal with
  [ H1: Match ?peg ?e ?s (Some ?s'),
    H2: Match ?peg ?e ?s None |- _ ] =>
        assert (Some s' = None);
        eauto using deterministic_result;
        discriminate
  end.

(* Use deterministic_result to unify
   two successful (Some) results *)
Ltac unify_results :=
   match goal with
   [ H1: Match ?peg ?e ?s (Some ?s1),
     H2: Match ?peg ?e ?s (Some ?s2) |- _ ] =>
         assert (Some s1 = Some s2) as Haux;
         eauto using deterministic_result;
         assert (s1 = s2);
         try congruence;
         clear Haux;
         subst
   end.

(* Two parsing expressions are said equivalent
   if, and only if, for every PEG and input string,
   they output the same result *)
Inductive equivalent : Exp -> Exp -> Prop :=
  | Equivalent :
      forall e1 e2,
      (forall peg s res, Match peg e1 s res <-> Match peg e2 s res) ->
      equivalent e1 e2.

(* Proving that the sequence expression is associative *)
Theorem sequence_assoc :
  forall e1 e2 e3,
  equivalent (e1; (e2; e3))
             ((e1; e2); e3).
Proof.
  intros.
  constructor.
  intros.
  split; intros H;
  inversion H; subst;
  try match_exp (e1; e2);
  try match_exp (e2; e3);
  eauto using Match.
Qed.

(* Proving that the ordered choice expression is associative *)
Theorem ordered_choice_assoc :
  forall e1 e2 e3,
  equivalent (e1 // (e2 // e3))
             ((e1 // e2) // e3).
Proof.
  intros.
  constructor.
  intros.
  split; intros H;
  inversion H; subst;
  try match_exp (e1 // e2);
  try match_exp (e2 // e3);
  eauto using Match.
Qed.

(* Show that a false first choice is useless *)
Theorem first_choice_false :
  forall e,
  equivalent e (EFalse // e).
Proof.
  intros.
  constructor.
  intros.
  split; intros H.
  - (* -> *)
    eauto using Match.
  - (* <- *)
    inversion H; subst;
    eauto using Match;
    match_exp EFalse.
Qed.

(* Show that a false second choice is useless *)
Theorem second_choice_false :
  forall e,
  equivalent e (e // EFalse).
Proof.
  intros.
  constructor.
  intros.
  split; intros H.
  - (* -> *)
    destruct res; econstructor; eauto using Match.
  - (* <- *)
    inversion H; subst; auto.
    destruct res; auto.
    match_exp EFalse.
Qed.

(* Show that a false first sequence part is enough *)
Theorem first_part_false :
  forall e,
  equivalent EFalse (EFalse; e).
Proof.
  intros.
  constructor.
  intros.
  split; intros H;
  inversion H; subst;
  eauto using Match;
  match_exp EFalse.
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
Theorem if_condition_suceeds :
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
Theorem if_then_undec :
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
Theorem if_else_undec :
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
