From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.

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
  | Success : string -> nat -> Result (* String suffix and remaining gas *)
  | Failure : string -> nat -> Result (* String suffix and remaining gas *)
  | OutOfGas : string -> Result (* String suffix *)
  | NoTerminal : nat -> Result (* Terminal ID *)
  .

(* Parse string according to PEG and parsing expression
   Number of steps is limited by gas *)
Fixpoint eparse (peg : PEG) (e : Exp) (s : string) (gas : nat) : Result :=
  match gas with
  | O => OutOfGas s
  | S gas' => match e with
              | ETrue => Success s gas'
              | EFalse => Failure s gas'
              | ETerminal a => match s with
                               | EmptyString => Failure s gas'
                               | String a' s' => if Ascii.eqb a a'
                                                 then Success s' gas'
                                                 else Failure s gas'
                               end
              | ENonTerminal i => match nth_error peg i with
                                  | Some e' => eparse peg e' s gas'
                                  | None => NoTerminal i
                                  end
              | ESequence e1 e2 => match eparse peg e1 s gas' with
                                   | Success s' gas'' => eparse peg e2 s' gas'
                                   | res => res
                                   end
              | EOrderedChoice e1 e2 => match eparse peg e1 s gas' as res with
                                        | Failure _ _ => eparse peg e2 s gas'
                                        | res => res
                                        end
              end
  end.

(* Parse string according to PEG and first parsing rule
   Number of steps is limited by gas *)
Definition parse (peg : PEG) (s : string) (gas : nat) : Result :=
  eparse peg (ENonTerminal 0) s gas.
