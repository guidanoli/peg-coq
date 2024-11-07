From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List.
From Coq Require Import Lia.

(** Pattern (a.k.a. expression) **)

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

(** Grammar **)

Definition grammar : Type := list pat.

Fixpoint grammar_size g :=
  match g with
  | cons p g' => pat_size p + grammar_size g'
  | nil => 0
  end.

Lemma pat_size_le_grammar_size :
  forall p g,
  In p g ->
  pat_size p <= grammar_size g.
Proof.
  intros * HIn.
  generalize dependent p.
  induction g as [|p' g' IHg]; intros.
  + (* nil *)
    inversion HIn.
  + (* cons p' g' *)
    inversion HIn as [|HIn']; subst.
    - (* p = p' *)
      simpl.
      lia.
    - (* In p (p' :: g') *)
      simpl.
      specialize (IHg _ HIn').
      lia.
Qed.
