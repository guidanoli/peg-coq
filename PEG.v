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
  | EWrapper : Exp -> Exp (* Wraps subexpression for backtracking *)
  .

(* Parsing Expression Grammar
   Each PEG is composed of a finite set of parsing rule *)
Definition PEG : Type := list Exp.

(* Starting Expression
   The first parsing expression in the list of parsing rules *)
Definition startExp (peg : PEG) : Exp := ENonTerminal 0.

(* Stack Entry
   Each stack entry is composed of:
   - an expression (to recover)
   - a string (to recover) *)
Definition StackEntry : Type := Exp * string.

(* Stack
   A list of stack entries *)
Definition Stack : Type := list StackEntry.

(* Parsing State
   Each parsing state is composed of:
   - the current parsing expression
   - a list of fallbacks (for ordered choices)
   - the current string being parsed *)
Definition PState : Type := Exp * Stack * string.

Reserved Notation " ps1 '==[' peg ']==>' ps2 " (at level 50, left associativity).

Inductive step : PEG -> PState -> PState -> Prop :=
  | STerminal1 :
      forall peg st a s,
      (ETerminal a, st, String a s) ==[ peg ]==> (ETrue, st, s)
  | STerminal2 :
      forall peg st a,
      (ETerminal a, st, EmptyString) ==[ peg ]==> (EFalse, st, EmptyString)
  | SNonTerminal1 :
      forall peg st i e s,
      nth_error peg i = Some e ->
      (ENonTerminal i, st, s) ==[ peg ]==> (e, st, s)
  | SNonTerminal2 :
      forall peg st i s,
      nth_error peg i = None ->
      (ENonTerminal i, st, s) ==[ peg ]==> (EFalse, st, s)
  | SSequence1 :
      forall peg st st' e1 e1' s s' e2,
      (e1, st, s) ==[ peg ]==> (e1', st', s') ->
      (ESequence e1 e2, st, s) ==[ peg ]==> (ESequence e1' e2, st', s')
  | SSequence2 :
      forall peg st e2 s,
      (ESequence ETrue e2, st, s) ==[ peg ]==> (e2, st, s)
  | SSequence3 :
      forall peg st e2 s,
      (ESequence EFalse e2, st, s) ==[ peg ]==> (EFalse, st, s)
  | SOrderedChoice :
      forall peg st e1 e2 s,
      (EOrderedChoice e1 e2, st, s) ==[ peg ]==> (EWrapper e1, (e2, s) :: st, s)
  | SWrapper1 :
      forall peg st st' e e' s s',
      (e, st, s) ==[ peg ]==> (e', st', s') ->
      (EWrapper e, st, s) ==[ peg ]==> (EWrapper e', st', s')
  | SWrapper2 :
      forall peg st s h,
      (EWrapper ETrue, h :: st, s) ==[ peg ]==> (ETrue, st, s)
  | SWrapper3 :
      forall peg st s e s',
      (EWrapper EFalse, (e, s') :: st, s) ==[ peg ]==> (e, st, s')

where " ps1 '==[' peg ']==>' ps2 " := (step peg ps1 ps2).
