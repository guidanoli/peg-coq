From Coq Require Import Bool.
From Coq Require Import Strings.String.
From Peg Require Import Charset.
From Peg Require Import Tactics.

Definition startswith (s : string) (cs : charset) : Prop :=
  match s with
  | EmptyString => False
  | String a _ => (cs a = true)
  end.

Lemma startswith_dec :
  forall s cs, {startswith s cs} + {~ startswith s cs}.
Proof.
  intros.
  unfold startswith.
  destruct s as [|a ?].
  - (* EmptyString *)
    auto.
  - (* String a _ *)
    destruct (cs a) eqn:?;
    auto.
Qed.

Lemma empty_or_startswith_fullcharset :
  forall s,
  s = EmptyString \/ startswith s fullcharset.
Proof.
  intros.
  unfold startswith.
  unfold fullcharset.
  destruct s;
  auto.
Qed.

Lemma startswith_unioncharset :
  forall s cs1 cs2,
  startswith s cs1 \/ startswith s cs2 ->
  startswith s (cs1 ∪ cs2).
Proof.
  unfold startswith.
  intros * H.
  destruct s.
  - (* EmptyString *)
    destruct H;
    auto.
  - (* String _ _ *)
    destruct H;
    eauto using orb_true_intro.
Qed.

Lemma startswith_intersectioncharset :
  forall s cs1 cs2,
  startswith s cs1 ->
  startswith s cs2 ->
  startswith s (cs1 ∩ cs2).
Proof.
  unfold startswith.
  intros * H1 H2.
  destruct s.
  - (* EmptyString *)
    auto.
  - (* String _ _ *)
    eauto using andb_true_intro.
Qed.

Lemma startswith_complementcharset :
  forall cs a s,
  cs a = false ->
  startswith (String a s) (complementcharset cs).
Proof.
  intros * Heqcsa.
  unfold startswith.
  unfold complementcharset.
  rewrite Heqcsa.
  auto.
Qed.
