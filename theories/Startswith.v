From Coq Require Import Bool.
From Coq Require Import Strings.String.
From Peg Require Import Charset.

Inductive startswith : string -> charset -> Prop :=
  | SWEmpty :
      forall cs,
      startswith EmptyString cs
  | SWChar :
      forall a s cs,
      cs a = true ->
      startswith (String a s) cs
  .

Lemma startswith_fullcharset :
  forall s,
  startswith s fullcharset.
Proof.
  intros.
  unfold fullcharset.
  destruct s;
  eauto using startswith.
Qed.

Lemma startswith_unioncharset :
  forall s cs1 cs2,
  startswith s cs1 \/ startswith s cs2 ->
  startswith s (cs1 U cs2).
Proof.
  intros * H.
  destruct s.
  - (* EmptyString *)
    auto using startswith.
  - (* String a s *)
    destruct H;
    inversion H; subst;
    eauto using orb_true_intro, unioncharset, startswith.
Qed.

Lemma startswith_complementcharset :
  forall cs a s,
  ~ in_charset a cs ->
  startswith (String a s) (complementcharset cs).
Proof.
  intros * H.
  destruct (cs a) eqn:Heqcsa.
  + (* cs a = true *)
    assert (in_charset a cs)
    by eauto using in_charset.
    contradiction.
  + (* cs a = false *)
    unfold complementcharset.
    econstructor.
    rewrite Heqcsa.
    auto.
Qed.

Lemma startswith_charseteq :
  forall s cs1 cs2,
  startswith s cs1 ->
  charseteq cs1 cs2 ->
  startswith s cs2.
Proof.
  intros * Hsw Hcseq.
  inversion Hcseq; subst;
  inversion Hsw; subst;
  eauto using startswith.
Qed.
