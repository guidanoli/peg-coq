(* @author Guilherme Dantas *)

From Coq Require Import Lia.
From Coq Require Import Lists.List.

(* Expression (stripped down) *)
Inductive Exp : Type :=
  | ETrue : Exp (* Always matches *)
  | EAny : Exp (* Matches any ASCII character *)
  | ENonTerminal : nat -> Exp (* Matches a rule (indexed expression) *)
  | ESequence : Exp -> Exp -> Exp (* Matches two subexpressions in sequence *)
  .

(* Cost of matching an expression *)
Fixpoint cost (e : Exp) : nat :=
  match e with
  | ETrue => 1
  | EAny => 1
  | ENonTerminal _ => 1
  | ESequence e1 e2 => S (cost e1 + cost e2)
  end.

(* A map is a list of index-value pairs *)
Definition Map (A : Type) : Type := list (nat * A).

(* Check if entry `e` has index `i` *)
Definition hasIndex {A : Type} (i : nat) (e : nat * A) : bool :=
  Nat.eqb i (fst e).

(* Get the value of the first entry with index `i` *)
Definition get {A : Type} (map : Map A) (i : nat) : option A :=
  match filter (hasIndex i) map with
  | nil => None
  | cons (_, a) _ => Some a
  end.

(* Delete every entry with index `i` *)
Definition del {A : Type} (map : Map A) (i : nat) : Map A :=
  filter (fun e => negb (hasIndex i e)) map.

Lemma get_after_del :
  forall A (map : Map A) i,
  get (del map i) i = None.
Proof.
  intros.
  induction map as [|e map'].
  - (* nil *)
    trivial.
  - (* cons e map' *)
    simpl.
    destruct (hasIndex i e) eqn:E.
    + auto.
    + simpl.
      unfold get.
      simpl.
      rewrite E.
      auto.
Qed.

(* Grammar, a finite set of indexed expressions *)
Definition Grammar : Type := Map Exp.

Inductive Result : Type :=
  | WellFormed : bool -> Result (* Well-formed + "always consumes some input?" *)
  | IllFormed : Result (* Ill-formed *)
  .

Fixpoint wf (e : Exp) (g : Grammar) (gas : nat) : option Result :=
  match gas with
  | O => None
  | S gas' => match e with
              | ETrue => Some (WellFormed false)
              | EAny => Some (WellFormed true)
              | ENonTerminal i => match get g i with
                                  | None => Some IllFormed
                                  | Some e => wf e (del g i) gas'
                                  end
              | ESequence e1 e2 => match wf e1 g gas' with
                                   | Some (WellFormed false) => wf e2 g gas'
                                   | res => res
                                   end
              end
  end.
