From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.
From Peg Require Import Tactics.
From Peg Require Import Syntax.

(** Coherent predicate **)
(** A pattern in a grammar is coherent
    if non-terminals always reference existing rules **)

Inductive coherent : grammar -> pat -> bool -> Prop :=
  | CEmpty :
      forall g,
      coherent g PEmpty true
  | CSet :
      forall g cs,
      coherent g (PSet cs) true
  | CSequenceFalse :
      forall g p1 p2,
      coherent g p1 false ->
      coherent g (PSequence p1 p2) false
  | CSequenceTrue :
      forall g p1 p2 b,
      coherent g p1 true ->
      coherent g p2 b ->
      coherent g (PSequence p1 p2) b
  | CChoiceFalse :
      forall g p1 p2,
      coherent g p1 false ->
      coherent g (PChoice p1 p2) false
  | CChoiceTrue :
      forall g p1 p2 b,
      coherent g p1 true ->
      coherent g p2 b ->
      coherent g (PChoice p1 p2) b
  | CRepetition :
      forall g p b,
      coherent g p b ->
      coherent g (PRepetition p) b
  | CNot :
      forall g p b,
      coherent g p b ->
      coherent g (PNot p) b
  | CNTNone :
      forall g i,
      nth_error g i = None ->
      coherent g (PNT i) false
  | CNTSome :
      forall g i p,
      nth_error g i = Some p ->
      coherent g (PNT i) true
  .

Lemma coherent_determinism :
  forall g p b1 b2,
  coherent g p b1 ->
  coherent g p b2 ->
  b1 = b2.
Proof.
  intros * H1 H2.
  generalize dependent b2.
  induction H1;
  intros;
  inversion H2;
  subst;
  eauto using coherent;
  try destruct2sep;
  try match goal with
    [ IHx: forall b, coherent ?g ?p b -> ?b1 = b,
      Hx: coherent ?g ?p ?b2 |- _ ] =>
        assert (b1 = b2) by auto;
        discriminate;
        fail
  end.
Qed.

Ltac pose_coherent_determinism :=
  match goal with
    [ Hx1: coherent ?g ?r ?b1,
      Hx2: coherent ?g ?r ?b2 |- _ ] =>
          assert (b1 = b2)
          by eauto using coherent_determinism
  end.

(** Coherent function **)

Fixpoint coherent_func (g : grammar) p {struct p} :=
  match p with
  | PEmpty => true
  | PSet _ => true
  | PSequence p1 p2 => coherent_func g p1 && coherent_func g p2
  | PChoice p1 p2 => coherent_func g p1 && coherent_func g p2
  | PRepetition p => coherent_func g p
  | PNot p => coherent_func g p
  | PNT i => match nth_error g i with
             | Some _ => true
             | None => false
             end
  end.

Lemma coherent_func_soundness :
  forall g p b,
  coherent_func g p = b ->
  coherent g p b.
Proof.
  intros * H.
  generalize dependent b.
  generalize dependent g.
  induction p;
  intros;
  simpl in H;
  subst;
  try match goal with
    [ |- coherent ?g (_ ?p1 ?p2) _ ] =>
      destruct (coherent_func g p1) as [|] eqn:?;
      destruct (coherent_func g p2) as [|] eqn:?
  end;
  try match goal with
    [ |- coherent ?g (PNT ?i) _ ] =>
      destruct (nth_error g i) as [|] eqn:?
  end;
  eauto using coherent.
Qed.

(** Coherent for lists of patterns

    lcoherent g rs true === all rules in rs are coherent
    lcoherent g rs false === some rule in rs is not coherent

**)

Inductive lcoherent : grammar -> list pat -> bool -> Prop :=
  | LCNil :
      forall g,
      lcoherent g nil true
  | LCConsFalse :
      forall g r rs,
      coherent g r false ->
      lcoherent g (cons r rs) false
  | LCConsTrue :
      forall g r rs b,
      coherent g r true ->
      lcoherent g rs b ->
      lcoherent g (cons r rs) b.

Lemma lcoherent_determinism :
  forall g rs b1 b2,
  lcoherent g rs b1 ->
  lcoherent g rs b2 ->
  b1 = b2.
Proof.
  intros * H1 H2.
  generalize dependent b2.
  induction H1; intros;
  inversion H2; subst;
  try (pose_coherent_determinism; discriminate);
  eauto using coherent_determinism.
Qed.

Lemma lcoherent_true_In :
  forall g rs r,
  lcoherent g rs true ->
  In r rs ->
  coherent g r true.
Proof.
  intros * Hc HIn.
  generalize dependent r.
  generalize dependent g.
  induction rs; intros.
  - (* nil *)
    exfalso.
    auto using in_nil.
  - (* cons r rs *)
    inversion Hc; subst.
    simpl in HIn.
    destruct HIn;
    subst;
    eauto.
Qed.

Fixpoint lcoherent_func g rs :=
  match rs with
  | nil => true
  | cons r rs' => coherent_func g r && lcoherent_func g rs'
  end.

Lemma lcoherent_func_soundness :
  forall g rs b,
  lcoherent_func g rs = b ->
  lcoherent g rs b.
Proof.
  intros * H.
  generalize dependent b.
  generalize dependent g.
  induction rs as [|r rs];
  intros.
  - (* nil *)
    simpl in H.
    subst.
    eauto using lcoherent.
  - (* cons r rs *)
    simpl in H.
    destruct (coherent_func g r) as [|] eqn:?;
    simpl in H;
    subst;
    eauto using lcoherent, coherent_func_soundness.
Qed.
