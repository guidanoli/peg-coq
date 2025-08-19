From Peg Require Import Syntax.
From Coq Require Import Lists.List.
From Coq Require Import Lia.
Import ListNotations.


(*
  Update the 'idx'-th position of list 'l' to the value 'newval'.
  no-op if index out of range.
*)
Fixpoint update {T} (l : list T) (idx : nat) (newval : T) : list T :=
  match idx,  l with
  | _, nil => nil
  | 0,  (h :: t) => newval :: t
  | S idx', (h :: t) => h :: update t idx' newval
  end.


(*
  status of each Non-terminal rule during traversal
*)
Inductive RuleStatus : Type :=
| NotVisited
| Visiting
| Visited : bool -> RuleStatus.  (* true means rule is nullable *)


(*
  Result of a traversal:
  - None means left-recursion detected.
  - Some: bool true means pattern is nullable; list is status updated.
*)
Definition RResult := option (bool * list RuleStatus).


Fixpoint verifyrule (gas : nat)
    (g : grammar) (p : pat) (lr : list RuleStatus) (nb : bool) :
      option RResult :=
  match gas with
  | 0 => None
  | S gas' =>
    match p with
    | PEmpty => Some (Some (true, lr))
    | PSet _ => Some (Some (nb, lr))
    | PSequence p1 p2 =>
      match verifyrule gas' g p1 lr false with
      | None => None  (* out of gas *)
      | Some None => Some None  (* ill formed *)
      | Some (Some (false, lr')) => Some (Some (nb, lr'))
      | Some (Some (true, lr')) => verifyrule gas' g p2 lr' nb
      end
    | PChoice p1 p2 =>
      match verifyrule gas' g p1 lr nb with
      | None => None  (* out of gas *)
      | Some None => Some None  (* ill formed *)
      | Some (Some (nb', lr')) => verifyrule gas' g p2 lr' nb'
      end
    | PRepetition p' => verifyrule gas' g p' lr true
    | PNot p' => verifyrule gas' g p' lr true
    | PAnd p' => verifyrule gas' g p' lr true
    | PNT i =>
      match nth i lr Visiting with
      | Visiting => Some None  (* left recursion *)
      | Visited nb' => Some (Some (orb nb nb', lr))
      | NotVisited =>
        match verifyrule gas' g (nth i g PEmpty)
                              (update lr i Visiting) false with
        | None => None  (* out of gas *)
        | Some None => Some None  (* ill formed *)
        | Some (Some (nb', lr')) =>
            Some (Some (orb nb nb', update lr' i (Visited nb')))
        end
      end
    end
  end.


(* Cost (gas) to traverse a pattern: It is equal to the size of the pattern *)
Fixpoint costP p : nat :=
  match p with
  | PEmpty => 1
  | PSet _ => 1
  | PSequence p1 p2 => S (costP p1 + costP p2)
  | PChoice p1 p2 => S (costP p1 + costP p2)
  | PRepetition p => S (costP p)
  | PNot p => S (costP p)
  | PAnd p => S (costP p)
  | PNT _ => 1
  end.


(* Cost (gas) to traverse a grammar: It is the summation of the sizes of the
   non-visited rules plus 1 for each non-visited rule. It also adds 2 for
   each non-visited rule not present in the grammar, which does not happen
   but we don't need to prove that. *)
Fixpoint costG g lr : nat :=
  match lr with
  | nil => 0
  | NotVisited :: lr' =>
      match g with
      | nil => S (1 + costG nil lr')   (* should not happen *)
      | (p :: g') => S (costP p + costG g' lr')
      end
  | _ :: lr' =>    (* visited rules add no cost *)
      match g with
      | nil => costG nil lr'
      | (_ :: g') => costG g' lr'
      end
  end.


Definition Result := option (list RuleStatus).

(*
  Traverse all rules of a grammar up to 'n' (exclusive), passing forward
  the list of status.
 *)
Fixpoint verifygrammar n
    (g : grammar) (lr : list RuleStatus) : Result :=
  match n with
  | 0 => Some lr
  | S n' => match verifygrammar n' g lr with
            | None => None
            | Some lr' =>
                match verifyrule (costG g lr' + 1)
                                      g (PNT n') lr' false with
                | None => Some lr'   (* cannot happen *)
                | Some None => None
                | Some (Some (nb, lr'')) => Some lr''
                end
            end
  end.


(*
  Traverse all rules of a grammar, returning the final list of status.
  (Start with all rules NotVisited.)
 *)
Definition VG (g : grammar) : Result :=
  verifygrammar (length g) g (repeat NotVisited (length g)).


(* Check whether a pattern is nullable, using 'lr' to solve rules *)
Fixpoint nullable lr p : bool :=
  match p with
  | PEmpty => true
  | PSet _ => false
  | PSequence p1 p2 =>
      (nullable lr p1 && nullable lr p2)%bool
  | PChoice p1 p2 =>
      (nullable lr p1 || nullable lr p2)%bool
  | PRepetition _ => true
  | PNot _ => true
  | PAnd _ => true
  | PNT i => match nth i lr Visiting with
             | Visited false => false
             | _ => true
             end
  end.


(*
  Check whether pattern doesn't have a loop with a nullable body.
*)
Fixpoint noloops lr p : bool :=
  match p with
  | PEmpty => true
  | PSet _ => true
  | PSequence p1 p2 =>
      (noloops lr p1 && noloops lr p2)%bool
  | PChoice p1 p2 =>
      (noloops lr p1 && noloops lr p2)%bool
  | PRepetition p' =>
      if nullable lr p' then false
      else noloops lr p'
  | PNot p' => noloops lr p'
  | PAnd p' => noloops lr p'
  | PNT _ => true   (* each rule will be checked by itself *)
end.


(*
  Check whether pattern doesn't have a loop with a nullable body
  and whether it is nullable.
*)
Fixpoint noloops2 lr p : (bool * bool) :=
  match p with
  | PEmpty => (true, true)
  | PSet _ => (true, false)
  | PSequence p1 p2 =>
      let (lp1, nl1) := noloops2 lr p1 in
      let (lp2, nl2) := noloops2 lr p2 in
        ((lp1 && lp2)%bool, (nl1 && nl2)%bool)
  | PChoice p1 p2 =>
      let (lp1, nl1) := noloops2 lr p1 in
      let (lp2, nl2) := noloops2 lr p2 in
        ((lp1 && lp2)%bool, (nl1 || nl2)%bool)
  | PRepetition p' =>
      let (lp, nl) := noloops2 lr p' in
        ((negb nl && lp)%bool, true)
  | PNot p' =>
      let (lp, _) := noloops2 lr p' in (lp,  true)
  | PAnd p' =>
      let (lp, _) := noloops2 lr p' in (lp,  true)
  | PNT i => match nth i lr Visiting with
             | Visited false => (true, false)
             | _ => (true, true)
             end
end.




Lemma noloops2_null: forall lr p,
  snd (noloops2 lr p) = nullable lr p.
Proof.
  induction p; simpl; trivial.
  - destruct (noloops lr p1).
    destruct (noloops lr p2).
    simpl in *; subst. trivial.
Abort.


(*
  Check whether grammar doesn't have a loop with a nullable body,
  up to rule 'n' (exclusive).
*)
Fixpoint Gnoloops (n : nat) (lr : list RuleStatus) (g : grammar) : bool :=
  match n with
  | 0 => true
  | S n' => match Gnoloops n' lr g with
            | false => false
            | true => noloops lr (nth n' g PEmpty)
            end
  end.


(*
  Final check: Checks whether grammar has neither left recursion nor
  loops with nullable body.
*)
Definition well_formed (g : grammar) : Result :=
  match VG g with
  | Some lr => 
      if Gnoloops (length g) lr g then Some lr
      else None
  | None => None
end.


Module Examples.
(* R0 -> R0 *)
Goal well_formed [PNT 0] = None. reflexivity. Qed.

Definition dot : pat := PSet (fun c => true).

(* R0 -> R1 R1; R1 -> ε / . *)
Goal well_formed [PSequence (PNT 1) (PNT 1); PChoice PEmpty dot] =
     Some [Visited true; Visited true]. reflexivity. Qed.

(* R0 -> . R0 / . *)
Goal well_formed [PChoice (PSequence dot (PNT 0)) dot] =
       Some [Visited false]. reflexivity. Qed.

(* R0 -> !. / &. . R0 *)
Goal well_formed [PChoice (PNot dot)
                          (PSequence (PAnd dot)
                          (PSequence dot (PNT 0)))] = Some [Visited true].
reflexivity. Qed.


(* R0 -> ( .* )*  *)
Goal well_formed [PRepetition (PRepetition dot)] = None.
reflexivity. Qed.


(* R0 -> ( .* . )*  *)
Goal well_formed [PRepetition (PSequence (PRepetition dot) dot)] =
      Some [Visited true]. reflexivity. Qed.

End Examples.


Module Cost.

(* number of steps to perform nullable lr p *)
Fixpoint nullable_cost p : nat :=
  match p with
  | PEmpty => 1
  | PSet _ => 1
  | PSequence p1 p2 =>
      1 + nullable_cost p1 + nullable_cost p2
  | PChoice p1 p2 =>
      1 + nullable_cost p1 + nullable_cost p2
  | PRepetition _ => 1
  | PNot _ => 1
  | PAnd _ => 1
  | PNT i => 1
end.


(* number of steps to perform noloops lr p *)
Fixpoint noloops_cost p : nat :=
  match p with
  | PEmpty => 1
  | PSet _ => 1
  | PSequence p1 p2 =>
      1 + noloops_cost p1 + noloops_cost p2
  | PChoice p1 p2 =>
      1 + noloops_cost p1 + noloops_cost p2
  | PRepetition p' =>
      1 + nullable_cost p' + noloops_cost p'
  | PNot p' => noloops_cost p'
  | PAnd p' => noloops_cost p'
  | PNT _ => 1
end.


(* Proof that noloop has a time complexity linear with the size of the
   pattern *)
Lemma noloop_cost: forall p,
  noloops_cost p + nullable_cost p <= 2 * costP p.
Proof.
  induction p; simpl; try lia.
Qed.

End Cost.

