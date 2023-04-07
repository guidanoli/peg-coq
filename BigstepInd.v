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
  .

(* Parsing Expression Grammar
   Each PEG is composed of a finite set of parsing rule *)
Definition PEG : Type := list Exp.

(* Parsing Result
   The result of parsing a string against a PEG *)
Inductive Result : Type :=
  | Success : string -> Result (* String suffix *)
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
  | PETerminal :
      forall peg a s,
      parse peg (ETerminal a) (String a s) (Success s)
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
      parse peg (EOrderedChoice e1 e2) s res.
