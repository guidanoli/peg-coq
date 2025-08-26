From Coq Require Import Arith.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.
From Coq Require Import Classes.EquivDec.

From Peg Require Import Syntax.
From Peg Require Import Ncode.
From Peg Require Import NMatch.
From Peg Require Import NVerifyrule.

Set Implicit Arguments.


Inductive noleftrec : grammar -> pat -> bool -> Prop :=
  | NLREmpty :
      forall g,
      noleftrec g PEmpty true
  | NLRSet :
      forall g cs,
      noleftrec g (PSet cs) false
  | NLRSequenceSomeTrue :
      forall g p1 p2 nb,
      noleftrec g p1 true ->
      noleftrec g p2 nb ->
      noleftrec g (PSequence p1 p2) nb
  | NLRSequenceSomeFalse :
      forall g p1 p2,
      noleftrec g p1 false ->
      noleftrec g (PSequence p1 p2) false
  | NLRChoice :
      forall g p1 p2 nb nb',
      noleftrec g p1 nb ->
      noleftrec g p2 nb' ->
      noleftrec g (PChoice p1 p2) (orb nb nb')
  | NLRRepetition :
      forall g p nb,
      noleftrec g p nb ->
      noleftrec g (PRepetition p) true
  | NLRNot :
      forall g p nb,
      noleftrec g p nb ->
      noleftrec g (PNot p) true
  | NLRNT :
      forall g i p nb,
      nth i g PEmpty = p ->
      noleftrec g p nb ->
      noleftrec g (PNT i) nb
.


Lemma uniqueNLRnb: forall g p nb nb',
    noleftrec g p nb ->
    noleftrec g p nb' ->
    nb = nb'.
Proof.
  intros * H1.
  generalize dependent nb'.
  induction H1; intros * H2; inversion H2;
  subst; intuition auto with *; try congruence.
  repeat f_equal; auto.
Qed.


Lemma update_coher : forall g p lr i,
  nth i lr Visiting = NotVisited ->
  (forall (n : nat) (nb' : bool),
     nth n lr Visiting = Visited nb' -> noleftrec g p nb') ->
  (forall (n : nat) (nb' : bool),
     nth n (update lr i Visiting) Visiting = Visited nb' -> noleftrec g p nb').
Proof.
  intros * H1 * H2 * H3.
  destruct (Nat.eq_dec n i); subst.
  - exfalso. erewrite update_eq in H3; try discriminate.
    eapply nth_overflow'; eauto. congruence.
  - erewrite update_neq in H3; eauto.
Qed.


Ltac simplOrb :=
    repeat rewrite Bool.orb_false_r;
    try rewrite Bool.orb_false_r in *;
    repeat rewrite Bool.orb_true_r;
    try rewrite Bool.orb_true_r in *;
    repeat rewrite Bool.orb_true_l;
    try rewrite Bool.orb_true_l in *;
    repeat rewrite Bool.orb_false_l;
    try rewrite Bool.orb_false_l in *.


Definition LRCoher (g : grammar) lr :=
  forall n nb, nth n lr Visiting = Visited nb -> noleftrec g (PNT n) nb.


Lemma LRCoherUpdateVisiting: forall g lr n,
    LRCoher g lr ->
    LRCoher g (update lr n Visiting).
Proof.
  intros * HC.
  unfold LRCoher; intros * HV.
  destruct (Nat.eq_dec n n0); subst.
  - rewrite update_eq in HV; try discriminate.
    replace (length lr) with (length (update lr n0 Visiting))
        by auto using update_len.
    eapply nth_overflow'; eauto. congruence.
  - rewrite update_neq in HV; auto.
Qed.


Lemma LRCoherUpdateVisited: forall g lr n nb,
    LRCoher g lr ->
    noleftrec g (nth n g PEmpty) nb ->
    LRCoher g (update lr n (Visited nb)).
Proof.
  intros * HC HNL.
  unfold LRCoher; intros * HV.
  destruct (Nat.eq_dec n n0); subst.
  - rewrite update_eq in HV.
    + injection HV; intros; subst.
      eauto using noleftrec.
    + replace (length lr) with (length (update lr n0 (Visited nb)))
        by auto using update_len.
      eapply nth_overflow'; eauto. congruence.
  - rewrite update_neq in HV; auto.
 Qed.


Lemma not_null_nt: forall g p n,
    not_nullable g p ->
    nth n g PEmpty = p ->
    not_nullable g (PNT n).
Proof.
  unfold not_nullable.
  intros * HNN Heq.
  inversion 1; subst.
  eapply HNN. eauto.
Qed.


Lemma nlr_nullable : forall g p,
   noleftrec g p false -> not_nullable g p.
Proof.
  intros * HNLR.
  remember false as nbF eqn:Heq.
  induction HNLR; try discriminate;
  intros *;
    eauto using not_null_set, not_null_seq2, not_null_seq1,
                not_null_choice, not_null_nt.
  apply Bool.orb_false_elim in Heq; destruct Heq; subst.
  eauto using not_null_choice.
Qed.




(*-------------------------------------------------------------------------*)

Definition orres (res : option RResult) (nb : bool) : option RResult :=
  match res with
  | None => None
  | Some None => Some None
  | Some (Some (nb', lr)) => Some (Some (orb nb nb', lr))
  end.


Lemma orresfalse : forall res, orres res false = res.
Proof.
  destruct res; simpl; trivial.
  destruct r; simpl; trivial.
  destruct p. trivial.
Qed.


Lemma orres2 : forall res nb nb',
    orres (orres res nb) nb' = orres res (orb nb' nb).
Proof.
  intros *.
  destruct res as [[[? ?] | ] | ]; simpl; trivial.
  rewrite Bool.orb_assoc. trivial.
Qed.


Fixpoint verifyrule' (gas : nat)
    (g : grammar) (p : pat) (lr : list RuleStatus) :
      option RResult :=
  match gas with
  | 0 => None
  | S gas' =>
    match p with
    | PEmpty => Some (Some (true, lr))
    | PSet _ => Some (Some (false, lr))
    | PSequence p1 p2 =>
      match verifyrule' gas' g p1 lr with
      | None => None  (* out of gas *)
      | Some None => Some None  (* ill formed *)
      | Some (Some (false, lr')) => Some (Some (false, lr'))
      | Some (Some (true, lr')) => verifyrule' gas' g p2 lr'
      end
    | PChoice p1 p2 =>
      match verifyrule' gas' g p1 lr with
      | None => None  (* out of gas *)
      | Some None => Some None  (* ill formed *)
      | Some (Some (nb, lr')) => orres (verifyrule' gas' g p2 lr') nb
      end
    | PRepetition p' => orres (verifyrule' gas' g p' lr) true
    | PNot p' => orres (verifyrule' gas' g p' lr) true
    | PNT i =>
      match nth i lr Visiting with
      | Visiting => Some None  (* left recursion *)
      | Visited nb => Some (Some (nb, lr))
      | NotVisited =>
        match verifyrule' gas' g (nth i g PEmpty)
                              (update lr i Visiting) with
        | None => None  (* out of gas *)
        | Some None => Some None  (* ill formed *)
        | Some (Some (nb, lr')) =>
            Some (Some (nb, update lr' i (Visited nb)))
        end
      end
    end
  end.


Lemma VRcompequiv : forall gas g p lr nb,
  verifyrule gas g p lr nb = orres (verifyrule' gas g p lr) nb.
Proof.
  induction gas; trivial.
  destruct p; intros *; simpl; simpl; simplOrb; trivial;
  rewrite IHgas;
  try
   (destruct (verifyrule' gas g p lr) as [[[? ?] | ] | ]; trivial;
    rewrite orres2; simplOrb; trivial; fail).
  - rewrite orresfalse.
    destruct (verifyrule' gas g p1 lr) as [[[? ?] | ] | ]; trivial.
    destruct b; eauto.
    simpl. simplOrb. trivial.
  - destruct (verifyrule' gas g p1 lr) as [[[? ?] | ] | ]; trivial.
    simpl.
    rewrite IHgas.
    destruct (verifyrule' gas g p2 lr) as [[[? ?] | ] | ]; trivial;
    rewrite orres2; trivial.
  - destruct (nth n lr Visiting); trivial.
    destruct (verifyrule' gas g (nth n g PEmpty) (update lr n Visiting))
      as [[[? ?] | ] | ]; trivial.
Qed.


Corollary VRcompequivfalse : forall gas g p lr,
  verifyrule gas g p lr false = verifyrule' gas g p lr.
Proof.
  intros *. rewrite VRcompequiv. apply orresfalse.
Qed.


Ltac dstrm :=
  match goal with
    [H: match ?e with _ => _ end = _ |- _] =>
      destruct e as [[[? ?] | ] | ] eqn:?; try congruence end.


Lemma sameLen' : forall gas g p lr lr' nb,
    verifyrule' gas g p lr = Some (Some (nb, lr')) ->
    length lr = length lr'.
Proof.
  induction gas; try discriminate.
  intros * Heq.
  destruct p; simpl in Heq; try congruence; try dstrm.
  - destruct b.
    + apply IHgas in Heq.
      apply IHgas in Heqo.
      congruence.
    + apply IHgas in Heqo.
      congruence.
  - destruct (verifyrule' gas g p2 l) as [[[? ?] | ] | ] eqn:?;
      try discriminate.
    simpl in Heq. injection Heq; intros; subst.
    apply IHgas in Heqo0.
    apply IHgas in Heqo.
    congruence.
  - destruct (verifyrule' gas g p lr) as [[[? ?] | ] | ] eqn:?;
      try discriminate.
    simpl in Heq. injection Heq; intros; subst.
    eauto.
  - destruct (verifyrule' gas g p lr) as [[[? ?] | ] | ] eqn:?;
      try discriminate.
    simpl in Heq. injection Heq; intros; subst.
    eauto.
  - destruct (nth n lr Visiting); try discriminate.
    + dstrm.
      simpl in Heq. injection Heq; intros; subst.
      apply IHgas in Heqo.
      rewrite update_len in *. trivial.
    + congruence.
Qed.


Theorem NLRpreservation' : forall gas g p lr nb lr',
    verifyrule' gas g p lr = Some (Some (nb, lr')) ->
    LRCoher g lr ->
    noleftrec g p nb /\ LRCoher g lr'.
Proof.
  induction gas; try discriminate.
  destruct p; intros * Heq HC.
  - simpl in Heq.
    injection Heq; intros; subst; intuition eauto using noleftrec.
  - simpl in Heq.
    injection Heq; intros; subst; intuition eauto using noleftrec.
  - simpl in Heq.
    destruct (verifyrule' gas g p1 lr) as [[[? ?] | ] | ] eqn:?;
        try discriminate.
    destruct b.
    + apply IHgas in Heqo; trivial.
      destruct Heqo.
      apply IHgas in Heq; trivial.
      destruct Heq.
      intuition eauto using noleftrec.
    + injection Heq; intros; subst.
      apply IHgas in Heqo; trivial.
      destruct Heqo.
      intuition eauto using noleftrec.
  - simpl in Heq.
    destruct (verifyrule' gas g p1 lr) as [[[? ?] | ] | ] eqn:?;
       try discriminate.
    apply IHgas in Heqo; trivial.
    destruct Heqo.
    destruct (verifyrule' gas g p2 l) as [[[? ?] | ] | ] eqn:?;
       try discriminate.
    apply IHgas in Heqo; trivial.
    destruct Heqo.
    simpl in Heq.
    injection Heq; intros; subst.
    intuition eauto using noleftrec.
  - simpl in Heq.
    destruct (verifyrule' gas g p lr) as [[[? ?] | ] | ] eqn:?;
       try discriminate.
    apply IHgas in Heqo; trivial.
    simpl in Heq. injection Heq; intros; subst.
    intuition eauto using noleftrec.
  - simpl in Heq.
    destruct (verifyrule' gas g p lr) as [[[? ?] | ] | ] eqn:?;
       try discriminate.
    apply IHgas in Heqo; trivial.
    simpl in Heq. injection Heq; intros; subst.
    intuition eauto using noleftrec.
  - simpl in Heq.
    destruct (nth n lr Visiting) eqn:?; try discriminate.
    + destruct
       (verifyrule' gas g (nth n g PEmpty) (update lr n Visiting))
          as [[[? ?] | ] | ] eqn:?; try discriminate.
      injection Heq; intros; subst. clear Heq.
      apply IHgas in Heqo.
      * destruct Heqo.
        split; eauto using noleftrec.
        auto using LRCoherUpdateVisited.
      * auto using LRCoherUpdateVisiting.
    + injection Heq; intros; subst.
      apply HC in Heqr. intuition.
Qed.


Lemma vrinc': forall gas g p nb lr lr' n stat,
  verifyrule' gas g p lr = Some (Some (nb, lr')) ->
  nth n lr Visiting = stat ->
  stat <> NotVisited ->
  nth n lr' Visiting = stat.
Proof.
  induction gas; try discriminate.
  intros * Heq Heq' HNeq.
  destruct p; simpl in Heq.
  - injection Heq; intros; subst. trivial.
  - injection Heq; intros; subst. trivial.
  - destruct (verifyrule' gas g p1 lr) as [[[? ?] | ] | ] eqn:?;
      try discriminate.
    destruct b.
    + apply IHgas with (stat := stat) (n := n) in Heqo; eauto.
    + apply IHgas with (stat := stat) (n := n) in Heqo; eauto.
      injection Heq; intros; subst. trivial.
  - destruct (verifyrule' gas g p1 lr) as [[[? ?] | ] | ] eqn:?;
      try discriminate.
    apply IHgas with (stat := stat) (n := n) in Heqo; eauto.
    destruct (verifyrule' gas g p2 l) as [[[? ?] | ] | ] eqn:?;
          try discriminate.
    injection Heq; intros; subst.
    eauto.
  - destruct (verifyrule' gas g p lr) as [[[? ?] | ] | ] eqn:?;
          try discriminate.
    injection Heq; intros; subst.
    eauto.
  - destruct (verifyrule' gas g p lr) as [[[? ?] | ] | ] eqn:?;
          try discriminate.
    injection Heq; intros; subst.
    eauto.
  - destruct (nth n0 lr Visiting) eqn:?; try discriminate.
    + destruct
        (verifyrule' gas g (nth n0 g PEmpty) (update lr n0 Visiting))
          as [[[? ?] | ] | ] eqn:?; try discriminate.
      injection Heq; intros; subst. clear Heq.
      apply IHgas with (n := n) (stat := (nth n lr Visiting)) in Heqo; auto.
      * destruct (Nat.eq_dec n n0); subst; try congruence.
        rewrite update_neq; trivial.
      * destruct (Nat.eq_dec n n0); subst; try congruence.
        rewrite update_neq; trivial.
    + injection Heq; intros; subst. trivial.
Qed.


Lemma VRAdd1'': forall gas g r nb lr lr',
  verifyrule' gas g (PNT r) lr = Some (Some (nb, lr')) ->
  nth r lr Visiting = NotVisited ->
  nth r lr' Visiting = Visited nb.
Proof.
  destruct gas; try discriminate.
  intros * Heq Hneq.
  simpl in Heq.
  destruct (nth r lr Visiting) eqn:?; try discriminate.
  destruct (verifyrule' gas g (nth r g PEmpty) (update lr r Visiting))
          as [[[? ?] | ] | ] eqn:?; try discriminate.
  inversion Heq; intros; subst.
  rewrite update_eq; trivial.
  eapply nth_overflow' in Heqr0; try congruence.
  apply sameLen' in Heqo.
  rewrite update_len in *. lia.
 Qed. 


Lemma VRAdd1N: forall gas g r nb lr lr',
  verifyrule' gas g (PNT r) lr = Some (Some (nb, lr')) ->
   nth r lr' Visiting = Visited nb.
Proof.
  intros * HV.
  destruct gas; try discriminate.
  destruct (nth r lr Visiting) eqn:?.
  - eauto using VRAdd1''.
  - simpl in HV.
    rewrite Heqr0 in HV. discriminate.
  - simpl in HV.
    rewrite Heqr0 in HV. congruence.
Qed.

