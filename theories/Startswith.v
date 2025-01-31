From Coq Require Import Bool.
From Coq Require Import Strings.String.
From Peg Require Import Charset.
From Peg Require Import Tactics.

Inductive startswith : string -> charset -> Prop :=
  | SWEmpty :
      forall cs,
      startswith EmptyString cs
  | SWChar :
      forall a s cs,
      cs a = true ->
      startswith (String a s) cs
  .

Lemma startswith_dec :
  forall s cs, {startswith s cs} + {~ startswith s cs}.
Proof.
  intros.
  destruct s as [|a s].
  - (* EmptyString *)
    auto using startswith.
  - (* String a s *)
    destruct (cs a) eqn:?.
    + (* cs a = true *)
      auto using startswith.
    + (* cs a = false *)
      right.
      intro Hcontra.
      inversion Hcontra; subst.
      destruct1sep.
Qed.

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
  cs a = false ->
  startswith (String a s) (complementcharset cs).
Proof.
  intros * Heqcsa.
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
