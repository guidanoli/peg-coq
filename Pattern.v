From Coq Require Import Strings.Ascii.

Inductive pat : Type :=
  | PEmpty : pat                          (* ε            *)
  | PChar : ascii -> pat                  (* 'a'          *)
  | PSequence : pat -> pat -> pat         (* p1 p2        *)
  | PChoice : pat -> pat -> pat           (* p1 / p2      *)
  | PRepetition : pat -> pat              (* p*           *)
  | PNot : pat -> pat                     (* !p           *)
  | PNT : nat -> pat                      (* G[i]         *)
  .

Fixpoint pat_size p :=
  match p with
  | PEmpty => 1
  | PChar _ => 1
  | PSequence p1 p2 => 1 + pat_size p1 + pat_size p2
  | PChoice p1 p2 => 1 + pat_size p1 + pat_size p2
  | PRepetition p => 1 + pat_size p
  | PNot p => 1 + pat_size p
  | PNT _ => 1
  end.
