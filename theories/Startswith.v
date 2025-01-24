From Coq Require Import Bool.
From Coq Require Import Strings.String.
From Peg Require Import Charset.

Inductive startswith : string -> charset -> Prop :=
  | SWEmpty :
      forall cs,
      startswith EmptyString cs
  | SWChar :
      forall a s cs,
      in_charset a cs = true ->
      startswith (String a s) cs
  .

Lemma startswith_fullcharset :
  forall s,
  startswith s fullcharset.
Proof.
  intros.
  destruct s;
  eauto using startswith, in_charset.
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
    econstructor;
    simpl;
    rewrite orb_true_iff;
    auto.
Qed.

Lemma startswith_complementcharset :
  forall cs a s,
  in_charset a cs = false ->
  startswith (String a s) (complementcharset cs).
Proof.
  intros * H.
  econstructor.
  simpl.
  rewrite H.
  auto.
Qed.

Lemma startswith_charseteq :
  forall s cs1 cs2,
  startswith s cs1 ->
  charseteq cs1 cs2 ->
  startswith s cs2.
Proof.
  unfold charseteq.
  intros * Hsw Hcseq.
  inversion Hsw; subst;
  eauto using startswith.
Qed.
