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

(* Parsing Result
   The result of parsing a string against a PEG *)
Inductive Result : Type :=
  | Success : string -> Result (* Match suffix *)
  | Failure : Result
  .

(* Parse string according to PEG and parsing expression *)
Inductive parse : PEG -> Exp -> string -> Result -> Prop :=
  | PETrue :
      forall peg s,
      parse peg ETrue s (Success s)
  | PEFalse :
      forall peg s,
      parse peg EFalse s Failure
  | PETerminalSuccess :
      forall peg a s,
      parse peg (ETerminal a) (String a s) (Success s)
  | PETerminalFailureString :
      forall peg a a' s,
      a <> a' ->
      parse peg (ETerminal a) (String a' s) Failure
  | PETerminalFailureEmptyString :
      forall peg a,
      parse peg (ETerminal a) EmptyString Failure
  | PENonTerminal :
      forall peg i s e res,
      nth_error peg i = Some e ->
      parse peg e s res ->
      parse peg (ENonTerminal i) s res
  | PESequenceSuccess :
      forall peg e1 e2 s s' res,
      parse peg e1 s (Success s') ->
      parse peg e2 s' res ->
      parse peg (e1; e2) s res
  | PESequenceFailure :
      forall peg e1 e2 s,
      parse peg e1 s Failure ->
      parse peg (e1; e2) s Failure
  | PEOrderedChoiceSuccess :
      forall peg e1 e2 s s',
      parse peg e1 s (Success s') ->
      parse peg (e1 // e2) s (Success s')
  | PEOrderedChoiceFailure :
      forall peg e1 e2 s res,
      parse peg e1 s Failure ->
      parse peg e2 s res ->
      parse peg (e1 // e2) s res
  | PENotPredicateSuccess :
      forall peg e s,
      parse peg e s Failure ->
      parse peg (!e) s (Success s)
  | PENotPredicateFailure :
      forall peg e s s',
      parse peg e s (Success s') ->
      parse peg (!e) s Failure
  .

(* Invert parse proposition with Exp e *)
Ltac parse_exp e :=
  match goal with
  | H: parse _ e _ _ |- _ => inversion H; subst; auto
  end.

(* Parsing a string against a parsing expression
   in the context of a PEG always outputs the same result *)
Theorem deterministic_result :
  forall peg e s r1,
  parse peg e s r1 ->
  (forall r2, parse peg e s r2 -> r1 = r2).
Proof.
  intros peg e s r1 H1.
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
    [ IH: forall _, parse _ ?e _ _ -> _,
      H: parse _ ?e _ _ |- _ ] =>
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
  [ H1: parse ?peg ?e ?s (Success ?s'),
    H2: parse ?peg ?e ?s Failure |- _ ] =>
        assert (Success s' = Failure);
        eauto using deterministic_result;
        discriminate
  end.

(* Use deterministic_result to unify
   two Success results *)
Ltac unify_results :=
   match goal with
   [ H1: parse ?peg ?e ?s (Success ?s1),
     H2: parse ?peg ?e ?s (Success ?s2) |- _ ] =>
         assert (Success s1 = Success s2) as Haux;
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
      (forall peg s res, parse peg e1 s res <-> parse peg e2 s res) ->
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
  try parse_exp (e1; e2);
  try parse_exp (e2; e3);
  eauto using parse.
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
  try parse_exp (e1 // e2);
  try parse_exp (e2 // e3);
  eauto using parse.
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
    eauto using parse.
  - (* <- *)
    inversion H; subst;
    eauto using parse;
    parse_exp EFalse.
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
    destruct res; econstructor; eauto using parse.
  - (* <- *)
    inversion H; subst; auto.
    destruct res; auto.
    parse_exp EFalse.
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
  eauto using parse;
  parse_exp EFalse.
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
Theorem if_true :
  forall peg e1 e2 e3 s s' res,
  parse peg e1 s (Success s') ->
  (parse peg (if& e1 then e2 else e3) s res <-> parse peg e2 s res).
Proof.
  intros.
  split; intros H'.
  - (* -> *)
    inversion H'; subst;
    parse_exp (&e1;e2).
    + (* &e1 and e2 succeed *)
      parse_exp (&e1).
    + (* &e1 succeeds, but e2 fails *)
      parse_exp (!e1;e3);
      parse_exp (&e1);
      discriminate_results.
    + (* &e1 fails *)
      parse_exp (&e1).
      parse_exp (!e1).
      discriminate_results.
  - (* <- *)
    assert (parse peg (&e1) s (Success s)).
    { eauto using parse. }
    destruct res;
    eauto using parse.
Qed.

(* If the condition is false, then
   the whole 'if-then-else' is equivalent to the 'else' *)
Theorem if_false :
  forall peg e1 e2 e3 s res,
  parse peg e1 s Failure ->
  (parse peg (if& e1 then e2 else e3) s res <-> parse peg e3 s res).
Proof.
  intros.
  split; intros H'.
  - (* -> *)
    inversion H'; subst;
    parse_exp (&e1;e2);
    try (parse_exp (&e1); parse_exp(!e1); discriminate_results);
    parse_exp (!e1;e3);
    parse_exp (!e1);
    discriminate_results.
  - (* <- *)
    assert (parse peg (&e1) s Failure).
    { eauto using parse. }
    destruct res;
    eauto using parse.
Qed.

(* If the condition is undecided, then
   the whole 'if-then-else' is undecided *)
Theorem if_undecided :
  forall peg e1 e2 e3 s,
  (forall res1, ~ parse peg e1 s res1) ->
  (forall res2, ~ parse peg (if& e1 then e2 else e3) s res2).
Proof.
  intros peg e1 e2 e3 s H1 r H2.
  parse_exp (if& e1 then e2 else e3);
  parse_exp (&e1;e2);
  parse_exp (&e1);
  parse_exp (!e1);
  match goal with
  [ Hf: forall r, ~ parse _ e1 _ r,
    Hx: parse _ e1 _ _ |- _ ] =>
      apply Hf in Hx; contradiction
  end.
Qed.
