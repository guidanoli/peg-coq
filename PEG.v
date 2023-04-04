From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Open Scope char_scope.

(* Parsing Expression *)
Inductive PExp : Type :=
  | PETrue : PExp
  | PEFalse : PExp
  | PETerminal : ascii -> PExp
  | PENonTerminal : nat -> PExp
  | PESequence : PExp -> PExp -> PExp
  | PEOrderedChoice : PExp -> PExp -> PExp
  | PEAndPredicate : PExp -> PExp
  | PENotPredicate : PExp -> PExp.

(* Parsing Expression Grammar
   Each PEG is composed of a starting rule (the first on the list)
   and a finite set of parsing rules (indexed by natural numbers) *)
Definition PEG : Type := list PExp.

(* Stack Entry
   The stack contains entries that allow backtracking *)
Inductive StackEntry : Type :=
  | SEIfFalse : PExp -> string -> StackEntry
  | SEIfTrue : PExp -> string -> StackEntry.

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
  | STrue1 :
      forall peg st s e s',
      (PETrue, (SEIfTrue e s') :: st, s) ==[ peg ]==> (e, st, s')
  | STrue2 :
      forall peg st s e s',
      (PETrue, (SEIfFalse e s') :: st, s) ==[ peg ]==> (PETrue, st, s)
  | SFalse1 :
      forall peg st s e s',
      (PEFalse, (SEIfFalse e s') :: st, s) ==[ peg ]==> (e, st, s')
  | SFalse2 :
      forall peg st s e s',
      (PEFalse, (SEIfTrue e s') :: st, s) ==[ peg ]==> (PEFalse, st, s)
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
      forall peg st st' e2 e2' s s',
      (e2, st, s) ==[ peg ]==> (e2', st', s') ->
      (PESequence PETrue e2, st, s) ==[ peg ]==> (PESequence PETrue e2', st', s')
  | SSequence3 :
      forall peg st e2 s,
      (PESequence PEFalse e2, st, s) ==[ peg ]==> (PEFalse, st, s)
  | SSequence4 :
      forall peg st s,
      (PESequence PETrue PETrue, st, s) ==[ peg ]==> (PETrue, st, s)
  | SSequence5 :
      forall peg st s,
      (PESequence PETrue PEFalse, st, s) ==[ peg ]==> (PEFalse, st, s)
  | SOrderedChoice :
      forall peg st e1 e2 s,
      (PEOrderedChoice e1 e2, st, s) ==[ peg ]==> (e1, (SEIfFalse e2 s) :: st, s)
  | SAndPredicate :
      forall peg st e s,
      (PEAndPredicate e, st, s) ==[ peg ]==> (e, (SEIfTrue PETrue EmptyString) :: st, s)
  | SNotPredicate :
      forall peg st e s,
      (PENotPredicate e, st, s) ==[ peg ]==> (e, (SEIfFalse PETrue EmptyString) :: st, s)

where " ps1 '==[' peg ']==>' ps2 " := (step peg ps1 ps2).

