From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.

(** Syntax **)
(************)

Inductive pat : Type :=
  | PTrue : pat
  | PFalse : pat
  | PAnyChar : pat
  | PChar : ascii -> pat
  | PSequence : pat -> pat -> pat
  | PChoice : pat -> pat -> pat
  | PRepetition : pat -> pat
  | PNot : pat -> pat
  .

Definition expandRepetition p :=
  PChoice (PSequence p (PRepetition p)) PTrue.

Inductive entry : Type :=
  | IfTrue : pat -> string -> entry
  | IfFalse : pat -> string -> entry
  | Continue : pat -> entry
  .

Definition stack : Type := list entry.

Definition state : Type := pat * string * stack.

Inductive final : state -> Prop :=
  | FTrue :
      forall s,
      final (PTrue, s, nil)
  | FFalse :
      forall s,
      final (PFalse, s, nil)
  .

(** Semantics **)
(***************)

Reserved Notation " t1 '-->' t2 " (at level 50, left associativity).

Inductive step : state -> state -> Prop :=
  | STrue1 :
      forall p s s' k,
      (PTrue, s, cons (IfFalse p s') k) --> (PTrue, s, k)
  | STrue2 :
      forall p s s' k,
      (PTrue, s, cons (IfTrue p s') k) --> (p, s', k)
  | STrue3 :
      forall p s k,
      (PTrue, s, cons (Continue p) k) --> (p, s, k)
  | SFalse1 :
      forall p s s' k,
      (PFalse, s, cons (IfFalse p s') k) --> (p, s', k)
  | SFalse2 :
      forall p s s' k,
      (PFalse, s, cons (IfTrue p s') k) --> (PFalse, s, k)
  | SFalse3 :
      forall p s k,
      (PFalse, s, cons (Continue p) k) --> (PFalse, s, k)
  | SAnyChar1 :
      forall a s k,
      (PAnyChar, String a s, k) --> (PTrue, s, k)
  | SAnyChar2 :
      forall k,
      (PAnyChar, EmptyString, k) --> (PFalse, EmptyString, k)
  | SChar1 :
      forall a s k,
      (PChar a, String a s, k) --> (PTrue, s, k)
  | SChar2 :
      forall a a' s k,
      a <> a' ->
      (PChar a, String a' s, k) --> (PFalse, String a' s, k)
  | SChar3 :
      forall a k,
      (PChar a, EmptyString, k) --> (PFalse, EmptyString, k)
  | SSequence :
      forall p1 p2 s k,
      (PSequence p1 p2, s, k) --> (p1, s, cons (Continue p2) k)
  | SChoice :
      forall p1 p2 s k,
      (PChoice p1 p2, s, k) --> (p1, s, cons (IfFalse p2 s) k)
  | SRepetition :
      forall p s k,
      (PRepetition p, s, k) --> (expandRepetition p, s, k)
  | SNot :
      forall p s k,
      (PNot p, s, k) --> (p, s, cons (IfTrue PFalse s) k)

where " t1 '-->' t2 " := (step t1 t2).

Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Ltac invert_step p :=
  match goal with
    [ Hx: (p, _, _) --> _ |- _ ] =>
        inversion Hx
  end.

Theorem step_deterministic :
  deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
  inversion Hy2; subst;
  auto;
  try contradiction;
  try invert_step PTrue;
  try invert_step PFalse;
  try match goal with
    [ IHx: forall y2, ?y1 --> y2 -> ?y3 = y2,
    Hx: ?y1 --> ?y4 |- _ ] =>
        apply IHx in Hx;
        inversion H4; subst;
        auto
  end.
Qed.

Theorem strong_progress :
  forall t, final t \/ (exists t', t --> t').
Proof.
  intros [[p s] k].
  induction p;
  try (left; auto using final; fail);
  try (destruct k as [|[]]; eauto using final, step; fail);
  try (destruct s; eauto using step; fail).
  - (* PChar *) right. destruct s.
    + eauto using step.
    + destruct (ascii_dec a a0); try subst; eauto using step.
Qed.

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Lemma final_is_nf :
  forall f,
  final f -> normal_form step f.
Proof.
  intros f H.
  unfold normal_form.
  destruct H;
  intro contra;
  destruct contra as [t' contra];
  inversion contra.
Qed.

Lemma nf_is_final :
  forall t,
  normal_form step t -> final t.
Proof.
  unfold normal_form.
  intros t H1.
  specialize (strong_progress t) as H2.
  destruct H2.
  - trivial.
  - contradiction.
Qed.

Corollary nf_same_as_final :
  forall t,
  normal_form step t <-> final t.
Proof.
  intros.
  split.
  - apply nf_is_final.
  - apply final_is_nf.
Qed.

Inductive Result :=
  | Success : string -> Result
  | Failure : Result
  .

Fixpoint eval p s gas {struct gas} :=
  match gas with
  | O => None
  | S gas' => match p with
              | PTrue => Some (Success s)
              | PFalse => Some Failure
              | PAnyChar => match s with
                            | EmptyString => Some Failure
                            | String a s' => Some (Success s')
                            end
              | PChar a' => match s with
                            | EmptyString => Some Failure
                            | String a s' => match ascii_dec a a' with
                                             | left _ => Some (Success s')
                                             | right _ => Some Failure
                                             end
                            end
              | PSequence p1 p2 => match eval p1 s gas' with
                                   | Some (Success s') => eval p2 s' gas'
                                   | optres => optres
                                   end
              | PChoice p1 p2 => match eval p1 s gas' with
                                 | Some Failure => eval p2 s gas'
                                 | optres => optres
                                 end
              | PRepetition p => eval (expandRepetition p) s gas'
              | PNot p => match eval p s gas' with
                          | Some (Success _) => Some Failure
                          | Some Failure => Some (Success s)
                          | None => None
                          end
              end
  end.
