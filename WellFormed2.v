(* @author Guilherme Dantas *)

From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.

(* Expression (stripped down) *)
Inductive Exp : Type :=
  | ETrue : Exp (* Always matches *)
  | EAny : Exp (* Matches any ASCII character *)
  | ENonTerminal : string -> Exp (* Matches a rule (labeled expression) *)
  | ESequence : Exp -> Exp -> Exp (* Matches two subexpressions in sequence *)
  .

(* Cost of matching an expression *)
Fixpoint cost (e : Exp) : nat :=
  match e with
  | ETrue => 0
  | EAny => 0
  | ENonTerminal _ => 1
  | ESequence e1 e2 => cost e1 + cost e2 + 1
  end.

(* Map of string keys and values of type A *)
Definition Map (A : Type) : Type := list (string * option A).

(* Grammar, a finite set of rules *)
Definition Grammar : Type := Map Exp.

(* A character index counter for each rule *)
Definition Counter : Type := Map nat.

(* Retrieve a value from a map *)
Fixpoint get {A : Type} (m : Map A) (l : string) : option A :=
  match m with
  | nil => None
  | cons (l', a) m' => if eqb l l'
                       then a
                       else get m' l
  end.

(* Overwrite the value associated with a label in a map *)
Definition set {A : Type} (m : Map A) (l : string) (a : A) : Map A :=
  cons (l, Some a) m.

(* Remove the value associated with a label in a map *)
Definition unset {A : Type} (m : Map A) (l : string) : Map A :=
  cons (l, None) m.

Inductive Result : Type :=
  | Wellformed : nat -> Result
  | Malformed : Result
  .

Fixpoint wf (e : Exp) (g : Grammar) (c : Counter) (n : nat) (gas : nat) : option Result :=
  match gas with
  | O => None
  | S gas' => match e with
              | ETrue => Some (Wellformed n)
              | EAny => Some (Wellformed (S n))
              | ENonTerminal l => match get g l with
                                  (* Rule is not in grammar *)
                                  | None => Some Malformed
                                  (* Rule is in grammar *)
                                  | Some e' => match get c l with
                                               (* Rule was not visited *)
                                               | None => wf e' g (set c l n) n gas'
                                               (* Rule was visited *)
                                               | Some n' => if Nat.eqb n n'
                                                            then Some Malformed
                                                            else Some (Wellformed n)
                                               end
                                  end
              | ESequence e1 e2 => match wf e1 g c n gas' with
                                   | Some (Wellformed n') => wf e2 g c n' gas'
                                   | res => res
                                   end
              end
  end.
