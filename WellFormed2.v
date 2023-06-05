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

(* Cost of checking if an expression is well-formed *)
Fixpoint cost_exp (e : Exp) : nat :=
  match e with
  | ETrue => 1
  | EAny => 1
  | ENonTerminal _ => 1
  | ESequence e1 e2 => S (cost_exp e1 + cost_exp e2)
  end.

(* A map is a list of index-value pairs *)
Definition Map (A : Type) : Type := list (nat * A).

(* Check if pair `p` has index `i` *)
Definition hasIndex {A : Type} (i : nat) (p : nat * A) : bool :=
  Nat.eqb i (fst p).

(* Get the value of the first pair with index `i` *)
Definition get {A : Type} (map : Map A) (i : nat) : option A :=
  match filter (hasIndex i) map with
  | nil => None
  | cons (_, a) _ => Some a
  end.

(* Delete every pair with index `i` *)
Definition del {A : Type} (map : Map A) (i : nat) : Map A :=
  filter (fun p => negb (hasIndex i p)) map.

Lemma get_after_del :
  forall A (map : Map A) i,
  get (del map i) i = None.
Proof.
  intros.
  induction map as [|p map'].
  - (* nil *)
    trivial.
  - (* cons p map' *)
    simpl.
    destruct (hasIndex i p) eqn:E.
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
  | WellFormed : bool -> Result (* Well-formed + "matches the empty string?" *)
  | IllFormed : Result (* Ill-formed *)
  .

Fixpoint wf_exp (e : Exp) (g : Grammar) (gas : nat) : option Result :=
  match gas with
  | O => None
  | S gas' => match e with
              | ETrue => Some (WellFormed true)
              | EAny => Some (WellFormed false)
              | ENonTerminal i => match get g i with
                                  | None => Some IllFormed
                                  | Some e => wf_exp e (del g i) gas'
                                  end
              | ESequence e1 e2 => match wf_exp e1 g gas' with
                                   | Some (WellFormed true) => wf_exp e2 g gas'
                                   | res => res
                                   end
              end
  end.

Fixpoint wf_grammar_aux (g gconst : Grammar) (gas : nat) : option bool :=
  match g with
  | nil => Some true
  | cons (_, e) g' => match wf_exp e gconst gas with
                      | Some (WellFormed _) => wf_grammar_aux g' gconst gas
                      | Some IllFormed => Some false
                      | None => None
                      end
  end.

Definition wf_grammar (g : Grammar) (gas : nat) : option bool :=
  wf_grammar_aux g g gas.
