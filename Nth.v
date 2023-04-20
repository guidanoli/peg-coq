Require Extraction.
From Coq Require Import Lists.List.
Import List.ListNotations.



Definition nth {A : Type} (l : list A) (n : nat)
               (H : n < length l) : A.
refine (
  (fix nth (l0 : list A) (n0 : nat) : (n0 < length l0) -> A := 
     match n0 with
     | O => match l0 with
            | nil => (fun H => _)
            | cons x xs => (fun _ => x)
            end
     | S n' => match l0 with
            | nil => (fun H => _)
            | cons x xs => (fun _ => nth xs n' _)
            end
     end
  ) l n H).
  - apply PeanoNat.Nat.nlt_0_r in H. destruct H.
  - apply PeanoNat.Nat.nlt_0_r in H. destruct H.
  - apply PeanoNat.Nat.succ_lt_mono. trivial.
Defined.

Extraction nth.

Check proj1 (PeanoNat.Nat.succ_lt_mono 10 20).

Lemma nth_previous : forall {A} a (l : list A) n (H : n < length l)
                     (H' : S n < length (cons a l)),
  nth l n H = nth (cons a l) (S n) H'.
Proof.
  intros.
  generalize dependent l.
  induction n; intros.
  - destruct l.
    + exfalso. eapply PeanoNat.Nat.nlt_0_r. apply H.
    + trivial.
  - destruct l.
    + exfalso. eapply PeanoNat.Nat.nlt_0_r. apply H.
    + apply IHn.
Qed.


Lemma nth_equal : forall {A} a (l : list A) n (H : n < length l),
  nth l n H = a ->
  nth_error l n = Some a.
Proof.
  intros.
  generalize dependent l.
  induction n; intros; destruct l.
  + exfalso. eapply PeanoNat.Nat.nlt_0_r. apply H.
  + simpl in H0. subst. trivial.
  + exfalso. eapply PeanoNat.Nat.nlt_0_r. apply H.
  + eapply IHn. simpl in H. subst.
    apply nth_previous.
  Unshelve. eapply PeanoNat.Nat.succ_lt_mono. auto.
Qed.




