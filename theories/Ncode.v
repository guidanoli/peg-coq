From Peg Require Import Syntax.
From Coq Require Import Lists.List.
Import ListNotations.


Fixpoint update {T} (l : list T) (idx : nat) (newval : T) : list T :=
  match idx,  l with
  | _, nil => nil
  | 0,  (h :: t) => newval :: t
  | S idx', (h :: t) => h :: update t idx' newval
  end.


Inductive RuleStatus : Type :=
| NotVisited
| Visiting
| Visited : bool -> RuleStatus.


Definition Result := option (bool * list RuleStatus).


Fixpoint verifyrule_comp gas
    (g : grammar) (p : pat) (lr : list RuleStatus) (nb : bool) :
      option Result :=
  match gas with
  | 0 => None
  | S gas' =>
    match p with
    | PEmpty => Some (Some (true, lr))
    | PSet _ => Some (Some (nb, lr))
    | PSequence p1 p2 =>
      match verifyrule_comp gas' g p1 lr false with
      | None => None  (* out of gas *)
      | Some None => Some None  (* ill formed *)
      | Some (Some (false, lr')) => Some (Some (nb, lr'))
      | Some (Some (true, lr')) => verifyrule_comp gas' g p2 lr' nb
      end
    | PChoice p1 p2 =>
      match verifyrule_comp gas' g p1 lr nb with
      | None => None  (* out of gas *)
      | Some None => Some None  (* ill formed *)
      | Some (Some (nb', lr')) => verifyrule_comp gas' g p2 lr' nb'
      end
    | PRepetition p' => verifyrule_comp gas' g p' lr true
    | PNot p' => verifyrule_comp gas' g p' lr true
    | PAnd p' => verifyrule_comp gas' g p' lr true
    | PNT i =>
      match nth i lr Visiting with
      | Visiting => Some (None)  (* ill formed *)
      | Visited nb' => Some (Some (orb nb nb', lr))
      | NotVisited =>
        match verifyrule_comp gas' g (nth i g PEmpty)
                              (update lr i Visiting) false with
        | None => None  (* out of gas *)
        | Some None => Some None  (* ill formed *)
        | Some (Some (nb', lr')) =>
            Some (Some (orb nb nb', update lr' i (Visited nb')))
        end
      end
    end
  end.


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


Fixpoint costG g lr : nat :=
  match lr with
  | nil => 0
  | NotVisited :: lr' =>
      match g with
      | nil => S (1 + costG nil lr')
      | (p :: g') => S (costP p + costG g' lr')
      end
  | _ :: lr' =>
      match g with
      | nil => costG nil lr'
      | (_ :: g') => costG g' lr'
      end
  end.


Fixpoint verifygrammar_comp n
    (g : grammar) (lr : list RuleStatus) : option (list RuleStatus) :=
  match n with
  | 0 => Some lr
  | S n' => match verifygrammar_comp n' g lr with
            | None => None
            | Some lr' =>
                match verifyrule_comp (costG g lr' + costP (PNT n'))
                                      g (PNT n') lr' false with
                | None => Some lr'   (* cannot happen *)
                | Some None => None
                | Some (Some (nb, lr'')) => Some lr''
                end
            end
  end.


Definition VG (g : grammar) : option (list RuleStatus) :=
  verifygrammar_comp (length g) g (repeat NotVisited (length g)).


Fixpoint nullable_comp lr p :=
  match p with
  | PEmpty => true
  | PSet _ => false
  | PSequence p1 p2 =>
      if nullable_comp lr p1 then
        nullable_comp lr p2
      else false
  | PChoice p1 p2 =>
      if nullable_comp lr p1 then
        true
      else
        nullable_comp lr p2
  | PRepetition _ => true
  | PNot _ => true
  | PAnd _ => true
  | PNT i => match nth i lr Visiting with
             | Visited false => false
             | _ => true
             end
  end.


(** CheckLoops function **)

Fixpoint noloops_comp lr p :=
  match p with
  | PEmpty => true
  | PSet _ => true
  | PSequence p1 p2 =>
      (noloops_comp lr p1 && noloops_comp lr p2)%bool
  | PChoice p1 p2 =>
      (noloops_comp lr p1 && noloops_comp lr p2)%bool
  | PRepetition p' =>
      if nullable_comp lr p' then false
      else noloops_comp lr p'
  | PNot p' => noloops_comp lr p'
  | PAnd p' => noloops_comp lr p'
  | PNT _ => true
end.


Fixpoint Gnoloops_comp n lr g : bool :=
  match n with
  | 0 => true
  | S n' => match Gnoloops_comp n' lr g with
            | false => false
            | true => noloops_comp lr (nth n' g PEmpty)
            end
  end.


Definition well_formed (g : grammar) : option (list RuleStatus) :=
  match VG g with
  | Some lr => 
      if Gnoloops_comp (length g) lr g then Some lr
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


