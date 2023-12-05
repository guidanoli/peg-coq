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
