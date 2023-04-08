From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
Open Scope char_scope.
Open Scope string_scope.

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
      parse peg (ESequence e1 e2) s res
  | PESequenceFailure :
      forall peg e1 e2 s,
      parse peg e1 s Failure ->
      parse peg (ESequence e1 e2) s Failure
  | PEOrderedChoiceSuccess :
      forall peg e1 e2 s s',
      parse peg e1 s (Success s') ->
      parse peg (EOrderedChoice e1 e2) s (Success s')
  | PEOrderedChoiceFailure :
      forall peg e1 e2 s res,
      parse peg e1 s Failure ->
      parse peg e2 s res ->
      parse peg (EOrderedChoice e1 e2) s res
  | PENotPredicateSuccess :
      forall peg e s,
      parse peg e s Failure ->
      parse peg (ENotPredicate e) s (Success s)
  | PENotPredicateFailure :
      forall peg e s s',
      parse peg e s (Success s') ->
      parse peg (ENotPredicate e) s Failure
  .

Definition peg_example1 : PEG :=
  [EOrderedChoice (ESequence (ETerminal "a") (ENonTerminal 0)) ETrue].

Theorem parse_example1 :
  parse peg_example1 (ENonTerminal 0) "aa" (Success "").
Proof.
  unfold peg_example1.
  do 10 (econstructor; simpl; eauto).
Qed.

Theorem parse_example2 :
  parse peg_example1 (ENonTerminal 0) "aab" (Success "b").
Proof.
  unfold peg_example1.
  do 10 (econstructor; simpl; eauto).
  eapply Ascii.eqb_neq; simpl; trivial.
Qed.

(* Equivalent parsing expressions under the same PEG *)
Inductive equivalent : PEG -> Exp -> Exp -> Prop :=
  | Equivalent :
      forall peg e1 e2,
      (forall s res, parse peg e1 s res <-> parse peg e2 s res) ->
      equivalent peg e1 e2.

(* Proving that the sequence expression is associative *)
Theorem sequence_assoc :
  forall peg e1 e2 e3,
  equivalent peg
  (ESequence e1 (ESequence e2 e3))
  (ESequence (ESequence e1 e2) e3).
Proof.
  intros.
  constructor.
  intros.
  split; intros H;
  inversion H; subst;
  try match goal with 
  | H12 : parse _ (ESequence e1 e2) _ _ |- _ => inversion H12; subst
  | H23 : parse _ (ESequence e2 e3) _ _ |- _ => inversion H23; subst
  end;
  eauto using parse.
Qed.

(* Proving that the ordered choice expression is associative *)
Theorem ordered_choice_assoc :
  forall peg e1 e2 e3,
  equivalent peg
  (EOrderedChoice e1 (EOrderedChoice e2 e3))
  (EOrderedChoice (EOrderedChoice e1 e2) e3).
Proof.
  intros.
  constructor.
  intros.
  split; intros H;
  inversion H; subst;
  try match goal with 
  | H12 : parse _ (EOrderedChoice e1 e2) _ _ |- _ => inversion H12; subst
  | H23 : parse _ (EOrderedChoice e2 e3) _ _ |- _ => inversion H23; subst
  end;
  eauto using parse.
Qed.

(* Tactic for inverting parsing of false expression as success *)
Ltac invert_false_success :=
    match goal with
    | H: parse _ EFalse _ (Success _) |- _ => inversion H
    end.

(* Show that a false first choice is useless *)
Theorem first_choice_false :
  forall peg e,
  equivalent peg e (EOrderedChoice EFalse e).
Proof.
  intros.
  constructor.
  intros.
  split; intros H.
  - (* -> *)
    eauto using parse.
  - (* <- *)
    inversion H; subst; eauto using parse;
    invert_false_success.
Qed.

(* Show that a false second choice is useless *)
Theorem second_choice_false :
  forall peg e,
  equivalent peg e (EOrderedChoice e EFalse).
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
    invert_false_success.
Qed.

(* Show that a false first sequence part is enough *)
Theorem first_part_false :
  forall peg e,
  equivalent peg EFalse (ESequence EFalse e).
Proof.
  intros.
  constructor.
  intros.
  split; intros H;
  inversion H; subst;
  eauto using parse;
  try invert_false_success.
Qed.

(* Kleene star operator *)
Definition EStar (e : Exp) (i : nat) : Exp :=
  EOrderedChoice (ESequence e (ENonTerminal i)) ETrue.

(* Plus operator *)
Definition EPlus (e : Exp) (i : nat) : Exp :=
  ESequence e (EStar e i).

(* Optional expression *)
Definition EOptional (e : Exp) : Exp :=
  EOrderedChoice e ETrue.

(* And predicate *)
Definition EAndPredicate (e : Exp) : Exp :=
  ENotPredicate (ENotPredicate e).
