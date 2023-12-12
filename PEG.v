From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Peg Require Import Strong.
From Peg Require Import Suffix.

(** Syntax **)
(************)

Inductive pat : Type :=
  | PEmpty : pat                   (* ε        *)
  | PChar : ascii -> pat           (* a        *)
  | PAnyChar : pat                 (* .        *)
  | PSequence : pat -> pat -> pat  (* p1 p2    *)
  | PChoice : pat -> pat -> pat    (* p1 / p2  *)
  | PRepetition : pat -> pat       (* p*       *)
  | PNot : pat -> pat              (* p!       *)
  .

(** Semantics **)
(***************)

(** Match predicate (big step) **)

Inductive MatchResult : Type :=
  | Failure : MatchResult            (* Pattern failed to match.            *)
  | Success : string -> MatchResult  (* Pattern matched and left string s.  *)
  .

Inductive matches : pat -> string -> MatchResult -> Prop :=
  | MEmptySuccess :
      forall s,
      matches PEmpty s (Success s)
  | MCharSuccess :
      forall a s,
      matches (PChar a) (String a s) (Success s)
  | MCharFailureEmptyString :
      forall a,
      matches (PChar a) EmptyString Failure
  | MCharFailureString :
      forall a1 a2 s,
      a1 <> a2 ->
      matches (PChar a1) (String a2 s) Failure
  | MAnyCharSuccess :
      forall a s,
      matches PAnyChar (String a s) (Success s)
  | MAnyCharFailure :
      matches PAnyChar EmptyString Failure
  | MSequenceSuccess :
      forall p1 p2 s s' res,
      matches p1 s (Success s') ->
      matches p2 s' res ->
      matches (PSequence p1 p2) s res
  | MSequenceFailure :
      forall p1 p2 s,
      matches p1 s Failure ->
      matches (PSequence p1 p2) s Failure
  | MChoiceSuccess :
      forall p1 p2 s s',
      matches p1 s (Success s') ->
      matches (PChoice p1 p2) s (Success s')
  | MChoiceFailure :
      forall p1 p2 s res,
      matches p1 s Failure ->
      matches p2 s res ->
      matches (PChoice p1 p2) s res
  | MRepetitionSuccess :
      forall p s s' res,
      matches p s (Success s') ->
      matches (PRepetition p) s' res ->
      matches (PRepetition p) s res
  | MRepetitionFailure :
      forall p s,
      matches p s Failure ->
      matches (PRepetition p) s (Success s)
  | MNotSuccess :
      forall p s s',
      matches p s (Success s') ->
      matches (PNot p) s Failure
  | MNotFailure :
      forall p s,
      matches p s Failure ->
      matches (PNot p) s (Success s)
  .

Ltac destruct1 :=
  match goal with
  [ H: ?C _ = ?C _ |- _ ] =>
      inversion H; clear H; subst
  end.

Ltac apply_matches_IH :=
  match goal with [
    IHx: forall r, matches ?p ?s r -> _ = r,
    Hx: matches ?p ?s _ |- _
  ] =>
    apply IHx in Hx
  end.

(** Match predicate determinism **)

Theorem matches_det :
  forall p s res1 res2,
  matches p s res1 ->
  matches p s res2 ->
  res1 = res2.
Proof.
  intros p s res1 res2 H1 H2.
  generalize dependent res2.
  induction H1;
  intros res2 H2;
  inversion H2; subst;
  try apply_matches_IH;
  try contradiction;
  try discriminate;
  try destruct1;
  try apply_matches_IH;
  auto.
Qed.

Ltac pose_matches_det :=
  match goal with
  [ H1: matches ?p ?s ?r1,
    H2: matches ?p ?s ?r2 |- _ ] =>
        pose (matches_det p s r1 r2 H1 H2)
  end.

Example infinite_loop :
  forall p s,
  matches p s (Success s) ->
  ~ (exists res, matches (PRepetition p) s res).
Proof.
  intros p s H1 [res H2].
  remember (PRepetition p).
  induction H2;
  try destruct1;
  try pose_matches_det;
  try discriminate;
  try destruct1;
  auto.
Qed.

(** Match suffix theorem **)

Theorem matches_suffix :
  forall p s s',
  matches p s (Success s') ->
  suffix s' s.
Proof.
  intros.
  remember (Success s') as res.
  generalize dependent s'.
  induction H; intros;
  try discriminate;
  try destruct1;
  eauto using suffix, suffix_trans.
Qed.

(** Match function with gas **)

Fixpoint matches_comp p s gas {struct gas} :=
  match gas with
  | O => None
  | S gas' => match p with
              | PEmpty => Some (Success s)
              | PChar a => match s with
                           | EmptyString => Some Failure
                           | String a' s' => if ascii_dec a a'
                                             then Some (Success s')
                                             else Some Failure
                           end
              | PAnyChar => match s with
                            | EmptyString => Some Failure
                            | String _ s' => Some (Success s')
                            end
              | PSequence p1 p2 => match matches_comp p1 s gas' with
                                   | Some (Success s') => matches_comp p2 s' gas'
                                   | res => res
                                   end
              | PChoice p1 p2 => match matches_comp p1 s gas' with
                                 | Some Failure => matches_comp p2 s gas'
                                 | res => res
                                 end
              | PRepetition p' => match matches_comp p' s gas' with
                                 | Some Failure => Some (Success s)
                                 | Some (Success s') => matches_comp p s' gas'
                                 | None => None
                                 end
              | PNot p' => match matches_comp p' s gas' with
                           | Some Failure => Some (Success s)
                           | Some (Success _) => Some Failure
                           | None => None
                           end
              end
  end.

Theorem matches_comp_correct :
  forall p s gas res,
  matches_comp p s gas = Some res ->
  matches p s res.
Proof.
  intros p s gas.
  generalize dependent s.
  generalize dependent p.
  induction gas; intros; try discriminate.
  destruct p; simpl in H; try destruct1; eauto using matches.
  5: {
    destruct (matches_comp p s gas) as [res'|] eqn:Hores.
    + apply IHgas in Hores.
      destruct res' as [|s']; try destruct1.
      -- eauto using matches.
      -- eapply MRepetitionSuccess.
         ++ eauto.
         ++ eapply IHgas.
            eauto.
  }
Admitted.
