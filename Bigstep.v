(* @author Guilherme Dantas *)

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
  | Success : string -> Result (* String suffix *)
  | Failure : string -> Result (* String suffix *)
  | OutOfGas : string -> Result (* String suffix *)
  | MissingRule : nat -> Result (* Terminal ID *)
  .

(* Parse string according to PEG and parsing expression
   Number of steps is limited by gas *)
Fixpoint eparse (peg : PEG) (e : Exp) (s : string) (gas : nat) : Result :=
  match gas with
  | O => OutOfGas s
  | S gas' => match e with
              | ETrue => Success s
              | EFalse => Failure s
              | ETerminal a => match s with
                               | EmptyString => Failure s
                               | String a' s' => if Ascii.eqb a a'
                                                 then Success s'
                                                 else Failure s
                               end
              | ENonTerminal i => match nth_error peg i with
                                  | Some e' => eparse peg e' s gas'
                                  | None => MissingRule i
                                  end
              | ESequence e1 e2 => match eparse peg e1 s gas' with
                                   | Success s' => eparse peg e2 s' gas'
                                   | res => res
                                   end
              | EOrderedChoice e1 e2 => match eparse peg e1 s gas' as res with
                                        | Failure _ => eparse peg e2 s gas'
                                        | res => res
                                        end
              end
  end.

(* Parse string according to PEG and first parsing rule
   Number of steps is limited by gas *)
Definition parse (peg : PEG) (s : string) (gas : nat) : Result :=
  eparse peg (ENonTerminal 0) s gas.
