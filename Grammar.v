From Coq Require Import Lists.List.
From Coq Require Import Lia.

From Peg Require Import Pattern.

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
