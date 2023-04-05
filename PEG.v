From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Open Scope char_scope.

(* Parsing Expression *)
Inductive PExp : Type :=
  | PETrue : PExp (* Always matches *)
  | PEFalse : PExp (* Never matches *)
  | PETerminal : ascii -> PExp (* Matches a ASCII character *)
  | PENonTerminal : nat -> PExp (* Matches a non-terminal *)
  | PESequence : PExp -> PExp -> PExp (* Matches two subexpressions in sequence *)
  | PEOrderedChoice : PExp -> PExp -> PExp (* Matches one of two subexpressions *)
  | PEWrapper : PExp -> PExp (* Wraps subexpression for backtracking *)
  .

(* Parsing Expression Grammar
   Each PEG is composed of a finite set of parsing rule *)
Definition PEG : Type := list PExp.

(* Starting Expression
   The first parsing expression in the list of parsing rules *)
Definition startExp (peg : PEG) : PExp := PENonTerminal 0.

(* Stack Entry
   Each stack entry is composed of:
   - an expression (to recover)
   - a string (to recover) *)
Definition StackEntry : Type := PExp * string.

(* Stack
   A list of stack entries *)
Definition Stack : Type := list StackEntry.

(* Parsing State
   Each parsing state is composed of:
   - the current parsing expression
   - a list of fallbacks (for ordered choices)
   - the current string being parsed *)
Definition PState : Type := PExp * Stack * string.

Reserved Notation " ps1 '==[' peg ']==>' ps2 " (at level 50, left associativity).

Inductive step : PEG -> PState -> PState -> Prop :=
  | STerminal1 :
      forall peg st a s,
      (PETerminal a, st, String a s) ==[ peg ]==> (PETrue, st, s)
  | STerminal2 :
      forall peg st a,
      (PETerminal a, st, EmptyString) ==[ peg ]==> (PEFalse, st, EmptyString)
  | SNonTerminal1 :
      forall peg st i e s,
      nth_error peg i = Some e ->
      (PENonTerminal i, st, s) ==[ peg ]==> (e, st, s)
  | SNonTerminal2 :
      forall peg st i s,
      nth_error peg i = None ->
      (PENonTerminal i, st, s) ==[ peg ]==> (PEFalse, st, s)
  | SSequence1 :
      forall peg st st' e1 e1' s s' e2,
      (e1, st, s) ==[ peg ]==> (e1', st', s') ->
      (PESequence e1 e2, st, s) ==[ peg ]==> (PESequence e1' e2, st', s')
  | SSequence2 :
      forall peg st e2 s,
      (PESequence PETrue e2, st, s) ==[ peg ]==> (e2, st, s)
  | SSequence3 :
      forall peg st e2 s,
      (PESequence PEFalse e2, st, s) ==[ peg ]==> (PEFalse, st, s)
  | SOrderedChoice :
      forall peg st e1 e2 s,
      (PEOrderedChoice e1 e2, st, s) ==[ peg ]==> (PEWrapper e1, (e2, s) :: st, s)
  | SWrapper1 :
      forall peg st st' e e' s s',
      (e, st, s) ==[ peg ]==> (e', st', s') ->
      (PEWrapper e, st, s) ==[ peg ]==> (PEWrapper e', st', s')
  | SWrapper2 :
      forall peg st s h,
      (PEWrapper PETrue, h :: st, s) ==[ peg ]==> (PETrue, st, s)
  | SWrapper3 :
      forall peg st s e s',
      (PEWrapper PEFalse, (e, s') :: st, s) ==[ peg ]==> (e, st, s')

where " ps1 '==[' peg ']==>' ps2 " := (step peg ps1 ps2).
