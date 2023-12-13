From Coq Require Import Strings.String.

Inductive suffix : string -> string -> Prop :=
  | SuffixRefl :
      forall s,
      suffix s s
  | SuffixChar :
      forall s1 s2 a,
      suffix s1 s2 ->
      suffix s1 (String a s2).

Lemma suffix_correct :
  forall s1 s2,
  suffix s1 (append s2 s1).
Proof.
  intros.
  induction s2.
  - constructor.
  - simpl.
    constructor.
    trivial.
Qed.

Lemma suffix_trans :
  forall s1 s2 s3,
  suffix s1 s2 ->
  suffix s2 s3 ->
  suffix s1 s3.
Proof.
  intros.
  generalize dependent s2.
  generalize dependent s1.
  induction s3 as [|a s3 IH]; intros s1 s2 H12 H23;
  inversion H23; subst; auto.
  constructor.
  eauto using IH.
Qed.

Lemma suffix_length_le :
  forall s1 s2,
  suffix s1 s2 ->
  length s1 <= length s2.
Proof.
  intros * H.
  induction H; simpl; auto.
Qed.

Lemma suffix_length_eq :
  forall s1 s2,
  suffix s1 s2 ->
  length s1 = length s2 ->
  s1 = s2.
Proof.
  intros * H1 H2.
  induction H1; auto.
  specialize (suffix_length_le _ _ H1) as Hle.
  rewrite H2 in Hle.
  simpl in Hle.
  exfalso.
  apply (PeanoNat.Nat.nle_succ_diag_l _ Hle).
Qed.

Lemma suffix_antisymmetric :
  forall s1 s2,
  suffix s1 s2 ->
  suffix s2 s1 ->
  s1 = s2.
Proof.
  intros * H12 H21.
  specialize (suffix_length_le _ _ H12) as Hlen12.
  specialize (suffix_length_le _ _ H21) as Hlen21.
  specialize (PeanoNat.Nat.le_antisymm _ _ Hlen12 Hlen21) as Hlen.
  eauto using suffix_length_eq.
Qed.
