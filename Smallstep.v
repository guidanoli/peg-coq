From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import List.
Import ListNotations.

(** Syntax **)
(************)

Inductive pat : Type :=
  | PConst : bool -> pat
  | PAnyChar : pat
  | PChar : ascii -> pat
  | PSequence : pat -> pat -> pat
  | PChoice : pat -> pat -> pat
  | PRepetition : pat -> pat
  | PNot : pat -> pat
  .

(** Semantics **)
(***************)

Definition expandRepetition p :=
  PChoice (PSequence p (PRepetition p)) (PConst true).

Inductive entry : Type :=
  | RevertIf : bool -> pat -> string -> entry
  | Continue : pat -> entry
  .

Definition stack : Type := list entry.

Definition state : Type := pat * string * stack.

Inductive final : state -> Prop :=
  | FConst :
      forall s b,
      final (PConst b, s, nil)
  .

Reserved Notation " t1 '-->' t2 " (at level 50, left associativity).

Inductive step : state -> state -> Prop :=
  | SConst :
      forall b p s s' k,
      (PConst b, s, (RevertIf b p s' :: k)) --> (p, s', k)
  | STrue1 :
      forall p s s' k,
      (PConst true, s, (RevertIf false p s' :: k)) --> (PConst true, s, k)
  | STrue2 :
      forall p s k,
      (PConst true, s, (Continue p :: k)) --> (p, s, k)
  | SFalse1 :
      forall p s s' k,
      (PConst false, s, (RevertIf true p s' :: k)) --> (PConst true, s, k)
  | SFalse2 :
      forall p s k,
      (PConst false, s, (Continue p :: k)) --> (PConst false, s, k)
  | SAnyChar1 :
      forall a s k,
      (PAnyChar, String a s, k) --> (PConst true, s, k)
  | SAnyChar2 :
      forall k,
      (PAnyChar, EmptyString, k) --> (PConst false, EmptyString, k)
  | SChar1 :
      forall a s k,
      (PChar a, String a s, k) --> (PConst true, s, k)
  | SChar2 :
      forall a a' s k,
      a <> a' ->
      (PChar a, String a' s, k) --> (PConst false, String a' s, k)
  | SChar3 :
      forall a k,
      (PChar a, EmptyString, k) --> (PConst false, EmptyString, k)
  | SSequence :
      forall p1 p2 s k,
      (PSequence p1 p2, s, k) --> (p1, s, (Continue p2 :: k))
  | SChoice :
      forall p1 p2 s k,
      (PChoice p1 p2, s, k) --> (p1, s, (RevertIf false p2 s :: k))
  | SRepetition :
      forall p s k,
      (PRepetition p, s, k) --> (expandRepetition p, s, k)
  | SNot :
      forall p s k,
      (PNot p, s, k) --> (p, s, (RevertIf true (PConst false) s) :: k)

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
  try discriminate;
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
  try (destruct b; destruct k as [|[[] p' s'|p']k']; eauto using final, step; fail);
  try (destruct s; eauto using step; fail).
  - (* PChar *) right. destruct s.
    + eauto using step.
    + destruct (ascii_dec a a0); try subst; eauto using step.
Qed.

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ~ exists t', R t t'.

Definition step_normal_form := normal_form step.

Lemma final_is_nf :
  forall f,
  final f -> step_normal_form f.
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
  step_normal_form t -> final t.
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
  step_normal_form t <-> final t.
Proof.
  intros.
  split.
  - apply nf_is_final.
  - apply final_is_nf.
Qed.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Theorem multi_R : forall (X : Type) (R : relation X) (x y : X),
  R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with y.
  - apply H.
  - apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X) (x y z : X),
  multi R x y ->
  multi R y z ->
  multi R x z.
Proof.
  intros X R x y z G H.
  induction G.
    - (* multi_refl *) assumption.
    - (* multi_step *)
      apply multi_step with y.
      + assumption.
      + apply IHG. assumption.
Qed.

Notation " t1 '-->*' t2 " := (multi step t1 t2) (at level 40).

Ltac eapply_multi :=
  eapply multi_refl +
  eapply multi_step;
    try match goal with
      [ |- ?t --> ?t' ] =>
          eauto using step;
          match t with
          | (PChar _, String _ _, _) =>
              apply SChar2; intro; discriminate
          end
    end.

Lemma pat_a_with_a :
  (PChar "a", "a"%string, nil) -->*
  (PConst true, ""%string, nil).
Proof.
  repeat eapply_multi.
Qed.

Lemma pat_a_with_ab :
  (PChar "a", "ab"%string, nil) -->*
  (PConst true, "b"%string, nil).
Proof.
  repeat eapply_multi.
Qed.

Lemma pat_a_with_b :
  (PChar "a", "b"%string, nil) -->*
  (PConst false, "b"%string, nil).
Proof.
  repeat eapply_multi.
Qed.

Example pat_a_rep := PRepetition (PChar "a").

Lemma pat_a_rep_with_empty :
  (pat_a_rep, ""%string, nil) -->*
  (PConst true, ""%string, nil).
Proof.
  repeat eapply_multi.
Qed.

Lemma pat_a_rep_with_a :
  (pat_a_rep, "a"%string, nil) -->*
  (PConst true, ""%string, nil).
Proof.
  repeat eapply_multi.
Qed.

Lemma pat_a_rep_with_aaa :
  (pat_a_rep, "aaa"%string, nil) -->*
  (PConst true, ""%string, nil).
Proof.
  repeat eapply_multi.
Qed.

Lemma pat_a_rep_with_xyz :
  (pat_a_rep, "xyz"%string, nil) -->*
  (PConst true, "xyz"%string, nil).
Proof.
  repeat eapply_multi.
Qed.

Lemma pat_a_rep_with_aaron :
  (pat_a_rep, "aaron"%string, nil) -->*
  (PConst true, "ron"%string, nil).
Proof.
  repeat eapply_multi.
Qed.

Lemma pat_anychar_with_empty :
  (PAnyChar, ""%string, nil) -->*
  (PConst false, ""%string, nil).
Proof.
  repeat eapply_multi.
Qed.

Lemma pat_anychar_with_a :
  (PAnyChar, "a"%string, nil) -->*
  (PConst true, ""%string, nil).
Proof.
  repeat eapply_multi.
Qed.

Definition pat_anychar_but_a := PSequence (PNot (PChar "a")) PAnyChar.

Lemma pat_anychar_but_a_with_empty :
  (pat_anychar_but_a, ""%string, nil) -->*
  (PConst false, ""%string, nil).
Proof.
  repeat eapply_multi.
Qed.

Lemma pat_anychar_but_a_with_a :
  (pat_anychar_but_a, "a"%string, nil) -->*
  (PConst false, "a"%string, nil).
Proof.
  repeat eapply_multi.
Qed.

Lemma pat_anychar_but_a_with_b :
  (pat_anychar_but_a, "b"%string, nil) -->*
  (PConst true, ""%string, nil).
Proof.
  repeat eapply_multi.
Qed.

Definition normal_form_of t t' :=
  (t -->* t' /\ step_normal_form t').

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  unfold deterministic. unfold normal_form_of.
  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12].
  destruct P2 as [P21 P22].
  generalize dependent y2.
  induction P11; intros.
  - (* multi_refl *)
    destruct P21.
    + trivial.
    + exfalso.
      apply P12.
      eauto.
  - (* multi_step *)
    specialize (IHP11 P12).
    destruct P21.
    + exfalso.
      destruct P22.
      eauto.
    + apply IHP11;
      try match goal with
        [ Hx: ?y1 -->* ?z |- ?y2 -->* ?z ] =>
            assert (y1 = y2) by (eauto using step_deterministic);
            subst
      end;
      auto.
Qed.

Inductive Result :=
  | Success : string -> Result
  | Failure : Result
  .

Fixpoint eval p s gas {struct gas} :=
  match gas with
  | O => None
  | S gas' => match p with
              | PConst true => Some (Success s)
              | PConst false => Some Failure
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
