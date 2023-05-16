(* @author Guilherme Dantas *)

From Coq Require Import Lia.

(* Parsing Expression (stripped down) *)
Inductive Exp : Type :=
  | ETrue : Exp (* Always matches *)
  | EAny : Exp (* Matches any ASCII character *)
  | ESequence : Exp -> Exp -> Exp (* Matches two subexpressions in sequence *)
  .

(* Cost of matching expression *)
Fixpoint cost (e : Exp) : nat :=
  match e with
  | ETrue => 0
  | EAny => 0
  | ESequence e1 e2 => cost e1 + cost e2 + 1
  end.

(* Well formed expression
   Returns None if ran out of gas *)
Fixpoint wf (e : Exp) (gas : nat) {struct gas} : option bool :=
  match gas with
  | O => None
  | S gas' => match e with
              | ETrue => Some true
              | EAny => Some true
              | ESequence e1 e2 => match wf e1 gas' with
                                   | Some true => wf e2 gas'
                                   | res => res
                                   end
              end
  end.

(* Given any expression, the algorithm `wf` consumes a finite
   amount of gas. That is, it terminates eventually. *)
Proposition wf_finite_gas :
  forall e gas,
  gas > cost e ->
  exists b, wf e gas = Some b.
Proof.
  intros e gas H.
  generalize dependent gas.
  induction e;
  intros gas H;
  simpl in H;
  try (
    exists true;
    destruct gas;
    auto;
    lia
  ).
  destruct gas; try lia.
  specialize (IHe1 gas).
  assert (gas > cost e1) as Hc1 by lia.
  assert (gas > cost e2) as Hc2 by lia.
  apply IHe1 in Hc1.
  apply IHe2 in Hc2.
  destruct Hc1 as [b1 Hwf1].
  destruct Hc2 as [b2 Hwf2].
  destruct b1;
  eexists; simpl; rewrite Hwf1; eauto.
Qed.

