From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lists.List.
From Coq Require Import Lia.
From Peg Require Import Strong.
From Peg Require Import Suffix.
From Peg Require Import Pigeonhole.

Import ListNotations.

(** Syntax **)
(************)

Inductive pat : Type :=
  | PEmpty : pat                          (* ε            *)
  | PChar : ascii -> pat                  (* 'a'          *)
  | PAnyChar : pat                        (* .            *)
  | PSequence : pat -> pat -> pat         (* p1 p2        *)
  | PChoice : pat -> pat -> pat           (* p1 / p2      *)
  | PRepetition : pat -> pat              (* p*           *)
  | PNot : pat -> pat                     (* !p           *)
  | PNT : nat -> pat                      (* G[i]         *)
  .

Definition grammar : Type := list pat.

(** Semantics **)
(***************)

(** Match predicate (big step) **)

Inductive MatchResult : Type :=
  | Failure : MatchResult            (* Pattern failed to match.            *)
  | Success : string -> MatchResult  (* Pattern matched and left string s.  *)
  .

Inductive matches : grammar -> pat -> string -> MatchResult -> Prop :=
  | MEmptySuccess :
      forall g s,
      matches g PEmpty s (Success s)
  | MCharSuccess :
      forall g a s,
      matches g (PChar a) (String a s) (Success s)
  | MCharFailureEmptyString :
      forall g a,
      matches g (PChar a) EmptyString Failure
  | MCharFailureString :
      forall g a1 a2 s,
      a1 <> a2 ->
      matches g (PChar a1) (String a2 s) Failure
  | MAnyCharSuccess :
      forall g a s,
      matches g PAnyChar (String a s) (Success s)
  | MAnyCharFailure :
      forall g,
      matches g PAnyChar EmptyString Failure
  | MSequenceSuccess :
      forall g p1 p2 s s' res,
      matches g p1 s (Success s') ->
      matches g p2 s' res ->
      matches g (PSequence p1 p2) s res
  | MSequenceFailure :
      forall g p1 p2 s,
      matches g p1 s Failure ->
      matches g (PSequence p1 p2) s Failure
  | MChoiceSuccess :
      forall g p1 p2 s s',
      matches g p1 s (Success s') ->
      matches g (PChoice p1 p2) s (Success s')
  | MChoiceFailure :
      forall g p1 p2 s res,
      matches g p1 s Failure ->
      matches g p2 s res ->
      matches g (PChoice p1 p2) s res
  | MRepetitionSuccess :
      forall g p s s' res,
      matches g p s (Success s') ->
      matches g (PRepetition p) s' res ->
      matches g (PRepetition p) s res
  | MRepetitionFailure :
      forall g p s,
      matches g p s Failure ->
      matches g (PRepetition p) s (Success s)
  | MNotSuccess :
      forall g p s s',
      matches g p s (Success s') ->
      matches g (PNot p) s Failure
  | MNotFailure :
      forall g p s,
      matches g p s Failure ->
      matches g (PNot p) s (Success s)
  | MNonTerminalSome :
      forall g i p s res,
      nth_error g i = Some p ->
      matches g p s res ->
      matches g (PNT i) s res
  .

Ltac destruct1 :=
  match goal with
  [ H: ?C _ = ?C _ |- _ ] =>
      injection H as H; subst
  end.

Ltac destruct2 :=
  match goal with
  [ H: ?C _ _ = ?C _ _ |- _ ] =>
      injection H as H; subst
  end.

Ltac apply_matches_IH :=
  match goal with [
    IHx: forall r, matches ?g ?p ?s r -> _ = r,
    Hx: matches ?g ?p ?s _ |- _
  ] =>
    apply IHx in Hx
  end.

Ltac eq_nth_error :=
  match goal with [
    Hx1: nth_error ?g ?i = _,
    Hx2: nth_error ?g ?i = _ |- _ ] =>
        rewrite Hx1 in Hx2;
        try (injection Hx2 as Hx2; subst);
        try discriminate
  end.

(** Match predicate determinism **)

Theorem matches_determinism :
  forall g p s res1 res2,
  matches g p s res1 ->
  matches g p s res2 ->
  res1 = res2.
Proof.
  intros * H1 H2.
  generalize dependent res2.
  induction H1;
  intros res2 H2;
  inversion H2; subst;
  try apply_matches_IH;
  try contradiction;
  try discriminate;
  try destruct1;
  try apply_matches_IH;
  try eq_nth_error;
  auto.
Qed.

Ltac pose_matches_determinism :=
  match goal with
  [ H1: matches ?g ?p ?s ?r1,
    H2: matches ?g ?p ?s ?r2 |- _ ] =>
        pose (matches_determinism g p s r1 r2 H1 H2)
  end.

Example infinite_loop :
  forall g p s,
  matches g p s (Success s) ->
  ~ (exists res, matches g (PRepetition p) s res).
Proof.
  intros * H1 [res H2].
  remember (PRepetition p).
  induction H2;
  try destruct1;
  try pose_matches_determinism;
  try discriminate;
  try destruct1;
  auto.
Qed.

(** Match suffix theorem **)

Theorem matches_suffix :
  forall g p s s',
  matches g p s (Success s') ->
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

Fixpoint matches_comp g p s gas {struct gas} :=
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
              | PSequence p1 p2 => match matches_comp g p1 s gas' with
                                   | Some (Success s') => matches_comp g p2 s' gas'
                                   | res => res
                                   end
              | PChoice p1 p2 => match matches_comp g p1 s gas' with
                                 | Some Failure => matches_comp g p2 s gas'
                                 | res => res
                                 end
              | PRepetition p' => match matches_comp g p' s gas' with
                                 | Some Failure => Some (Success s)
                                 | Some (Success s') => matches_comp g p s' gas'
                                 | None => None
                                 end
              | PNot p' => match matches_comp g p' s gas' with
                           | Some Failure => Some (Success s)
                           | Some (Success _) => Some Failure
                           | None => None
                           end
              | PNT i => match nth_error g i with
                         | Some p' => matches_comp g p' s gas'
                         | None => None
                         end
              end
  end.

Theorem matches_comp_soundness :
  forall g p s gas res,
  matches_comp g p s gas = Some res ->
  matches g p s res.
Proof with eauto using matches.
  intros *.
  generalize dependent res.
  generalize dependent s.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros; try discriminate.
  destruct p; simpl in H; eauto using matches.
  - (* PEmpty *)
    destruct1...
  - (* PChar a *)
    destruct s as [|a' s'];
    try destruct (ascii_dec a a');
    destruct1;
    eauto using matches.
  - (* PAnyChar *)
    destruct s as [|a' s'];
    destruct1;
    eauto using matches.
  - (* PSequence p1 p2 *)
    destruct (matches_comp g p1 s gas) as [res1|] eqn:H1; try discriminate.
    apply IHgas in H1.
    destruct res1 as [|s1].
    -- (* Failure *)
       destruct1...
    -- (* Success s1 *)
       apply IHgas in H...
  - (* PChoice p1 p2 *)
    destruct (matches_comp g p1 s gas) as [res1|] eqn:H1; try discriminate.
    apply IHgas in H1.
    destruct res1 as [|s1].
    -- (* Failure *)
       apply IHgas in H...
    -- (* Success s1 *)
       destruct1...
  - (* PRepetition p *)
    destruct (matches_comp g p s gas) as [res1|] eqn:H1; try discriminate.
    apply IHgas in H1.
    destruct res1 as [|s1].
    -- (* Failure *)
       destruct1...
    -- (* Success s1 *)
       apply IHgas in H...
  - (* PNot p *)
    destruct (matches_comp g p s gas) as [res1|] eqn:H1; try discriminate.
    apply IHgas in H1.
    destruct res1 as [|s1];
    destruct1;
    eauto using matches.
  - (* PNT n *)
    destruct (nth_error g n) as [p|] eqn:H1.
    + (* Some p *)
      eauto using matches.
    + (* None *)
      discriminate.
Qed.

Corollary matches_comp_determinism :
  forall g p s gas1 gas2 res1 res2,
  matches_comp g p s gas1 = Some res1 ->
  matches_comp g p s gas2 = Some res2 ->
  res1 = res2.
Proof.
  eauto using matches_comp_soundness, matches_determinism.
Qed.

Lemma matches_comp_S_gas_some :
  forall g p s gas res,
  matches_comp g p s gas = Some res ->
  matches_comp g p s (S gas) = Some res.
Proof.
  intros *.
  generalize dependent res.
  generalize dependent s.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros; try discriminate.
  destruct p; simpl in H;
  try match goal with
    [ Hx: match nth_error ?g ?n with _ => _ end = _ |- _ ] =>
      destruct (nth_error g n) as [|] eqn:H1;
      remember (S gas);
      simpl;
      rewrite H1;
      try apply IHgas in H;
      auto
  end;
  try match goal with
    [ Hx: match matches_comp ?g ?px ?sx ?gasx with _ => _ end = _ |- _ ] =>
      destruct (matches_comp g px sx gasx) as [[]|] eqn:H1;
      try discriminate;
      apply IHgas in H1;
      remember (S gasx);
      simpl;
      rewrite H1;
      auto
  end;
  try (
    remember (S gas);
    simpl;
    auto;
    fail
  ).
Qed.

Lemma matches_comp_S_gas_none :
  forall g p s gas,
  matches_comp g p s (S gas) = None ->
  matches_comp g p s gas = None.
Proof.
  intros.
  destruct (matches_comp g p s gas) eqn:H'; trivial.
  apply matches_comp_S_gas_some in H'.
  rewrite H' in H.
  discriminate.
Qed.

Lemma matches_comp_gas_some_le :
  forall g p s gas gas' res,
  matches_comp g p s gas = Some res ->
  gas <= gas' ->
  matches_comp g p s gas' = Some res.
Proof.
  intros * H1 Hle.
  induction Hle; auto.
  eauto using matches_comp_S_gas_some.
Qed.

Lemma matches_comp_gas_none_le :
  forall g p s gas gas',
  matches_comp g p s gas' = None ->
  gas <= gas' ->
  matches_comp g p s gas = None.
Proof.
  intros * H1 Hle.
  induction Hle; auto.
  eauto using matches_comp_S_gas_none.
Qed.

Ltac rewrite_match_subject_in_goal :=
  match goal with
    [ Hx: ?lhs = _ |- match ?lhs with _ => _ end = _ ] =>
      rewrite Hx
  end.

Theorem matches_comp_termination :
  forall g p s res,
  matches g p s res ->
  (exists gas, matches_comp g p s gas = Some res).
Proof.
  intros * H.
  induction H;
  (* Cases with no recursive calls *)
  try (exists 1; auto; fail);
  (* Cases with one recursive call *)
  try (
    destruct IHmatches as [gas1 H1];
    exists (1 + gas1);
    simpl;
    try rewrite_match_subject_in_goal;
    trivial
  );
  (* Cases with two recursive calls *)
  try (
    destruct IHmatches1 as [gas1 H1];
    destruct IHmatches2 as [gas2 H2];
    exists (1 + gas1 + gas2);
    simpl;
    specialize (Nat.le_add_r gas1 gas2) as Hle1;
    rewrite (matches_comp_gas_some_le _ _ _ _ _ _ H1 Hle1);
    specialize (Plus.le_plus_r gas1 gas2) as Hle2;
    eauto using matches_comp_gas_some_le
  ).
  - (* MCharSuccess *)
    exists 1. simpl. destruct (ascii_dec a a); auto; contradiction.
  - (* MCharFailureString *)
    exists 1. simpl. destruct (ascii_dec a1 a2); auto; contradiction.
Qed.

(** Coherent predicate **)
(** A pattern in a grammar is coherent
    if non-terminals always reference existing rules **)

Inductive coherent : grammar -> pat -> bool -> Prop :=
  | CEmpty :
      forall g,
      coherent g PEmpty true
  | CChar :
      forall g a,
      coherent g (PChar a) true
  | CAnyChar :
      forall g,
      coherent g PAnyChar true
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
  try eq_nth_error;
  try match goal with
    [ IHx: forall b, coherent ?g ?p b -> ?b1 = b,
      Hx: coherent ?g ?p ?b2 |- _ ] =>
        assert (b1 = b2) by auto;
        discriminate;
        fail
  end.
Qed.

(** Coherent function **)

Fixpoint coherent_comp (g : grammar) p gas {struct gas} :=
  match gas with
  | O => None
  | S gas' => match p with
              | PEmpty => Some true
              | PChar _ => Some true
              | PAnyChar => Some true
              | PSequence p1 p2 => match coherent_comp g p1 gas' with
                                   | Some true => coherent_comp g p2 gas'
                                   | res => res
                                   end
              | PChoice p1 p2 => match coherent_comp g p1 gas' with
                                 | Some true => coherent_comp g p2 gas'
                                 | res => res
                                 end
              | PRepetition p => coherent_comp g p gas'
              | PNot p => coherent_comp g p gas'
              | PNT i => match nth_error g i with
                         | Some _ => Some true
                         | None => Some false
                         end
              end
  end.

Lemma coherent_comp_soundness :
  forall g p gas b,
  coherent_comp g p gas = Some b ->
  coherent g p b.
Proof.
  intros * H.
  generalize dependent b.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros; try discriminate.
  destruct p;
  simpl in H;
  repeat match goal with
    [ Hx: match ?x with | _ => _ end = _ |- _ ] =>
        destruct x eqn:?
  end;
  try discriminate;
  try destruct1;
  eauto using coherent.
Qed.

Lemma coherent_comp_S_gas :
  forall g p gas b,
  coherent_comp g p gas = Some b ->
  coherent_comp g p (S gas) = Some b.
Proof.
  intros * H.
  generalize dependent b.
  generalize dependent p.
  generalize dependent g.
  induction gas;
  intros;
  try discriminate.
  simpl in H.
  destruct p;
  try destruct1;
  remember (S gas);
  simpl;
  repeat match goal with
    [ Hx: match ?x with | _ => _ end = _ |- _ ] =>
        destruct x eqn:?
  end;
  try discriminate;
  subst;
  try match goal with
    [ Hx: coherent_comp ?g ?p ?gas = Some ?b
      |- match coherent_comp ?g ?p (S ?gas) with | _ => _ end = _ ] =>
      apply IHgas in Hx;
      rewrite Hx
  end;
  auto.
Qed.

Lemma coherent_comp_le_gas :
  forall g p gas1 gas2 b,
  coherent_comp g p gas1 = Some b ->
  gas1 <= gas2 ->
  coherent_comp g p gas2 = Some b.
Proof.
  intros * H Hle.
  induction Hle;
  auto using coherent_comp_S_gas.
Qed.

Lemma coherent_comp_termination :
  forall g p,
  exists gas b,
  coherent_comp g p gas = Some b.
Proof.
  intros.
  generalize dependent g.
  induction p; intros;
  (* Zero recursive calls *)
  try (
    exists 1;
    simpl;
    try match goal with
      [ |- exists _, match ?x with | _ => _ end = _ ] =>
        destruct x eqn:?
    end;
    eauto;
    fail
  );
  (* One recursive call *)
  try (
    destruct (IHp g) as [gas [b H]];
    exists (1 + gas);
    eauto;
    fail
  );
  (* Two recursive calls *)
  try (
    destruct (IHp1 g) as [gas1 [b1 H1]];
    destruct (IHp2 g) as [gas2 [b2 H2]];
    assert (gas1 <= gas1 + gas2) as Hle1 by lia;
    assert (gas2 <= gas1 + gas2) as Hle2 by lia;
    assert (coherent_comp g p1 (gas1 + gas2) = Some b1) as H1'
    by eauto using coherent_comp_le_gas;
    assert (coherent_comp g p2 (gas1 + gas2) = Some b2) as H2'
    by eauto using coherent_comp_le_gas;
    exists (1 + gas1 + gas2);
    simpl;
    rewrite H1';
    destruct b1;
    eauto;
    fail
  ).
Qed.

(** VerifyRule predicate **)
(** Checks whether a pattern is nullable (or not), or contains left recursion **)
(** The nb parameter is used for tail calls in choices (stands for (N)ulla(B)le) **)
(** The v parameter is the list of (V)isited rules without consuming input **)
(** res = None -> has LR **)
(** res = Some true -> no LR, nullable **)
(** res = Some false -> no LR, not nullable **)

Inductive verifyrule :
  grammar -> pat -> nat -> bool -> option bool -> list nat -> Prop :=

  | VREmpty :
      forall g nleft nb,
      verifyrule g PEmpty nleft nb (Some true) nil
  | VRChar :
      forall g a nleft nb,
      verifyrule g (PChar a) nleft nb (Some nb) nil
  | VRAnyChar :
      forall g nleft nb,
      verifyrule g PAnyChar nleft nb (Some nb) nil
  | VRSequenceNone :
      forall g p1 p2 nleft nb v,
      verifyrule g p1 nleft false None v ->
      verifyrule g (PSequence p1 p2) nleft nb None v
  | VRSequenceSomeTrue :
      forall g p1 p2 nleft nb res v1 v2,
      verifyrule g p1 nleft false (Some true) v1 ->
      verifyrule g p2 nleft nb res v2 ->
      verifyrule g (PSequence p1 p2) nleft nb res v2
  | VRSequenceSomeFalse :
      forall g p1 p2 nleft nb v,
      verifyrule g p1 nleft false (Some false) v ->
      verifyrule g (PSequence p1 p2) nleft nb (Some nb) v
  | VRChoiceNone :
      forall g p1 p2 nleft nb v,
      verifyrule g p1 nleft nb None v ->
      verifyrule g (PChoice p1 p2) nleft nb None v
  | VRChoiceSome :
      forall g p1 p2 nleft nb nb' res v1 v2,
      verifyrule g p1 nleft nb (Some nb') v1 ->
      verifyrule g p2 nleft nb' res v2 ->
      verifyrule g (PChoice p1 p2) nleft nb res v2
  | VRRepetition :
      forall g p nleft nb res v,
      verifyrule g p nleft true res v ->
      verifyrule g (PRepetition p) nleft nb res v
  | VRNot :
      forall g p nleft nb res v,
      verifyrule g p nleft true res v ->
      verifyrule g (PNot p) nleft nb res v
  | VRNTZero :
      forall g i nb,
      verifyrule g (PNT i) O nb None nil
  | VRNTSucc :
      forall g i p nleft nb res v,
      nth_error g i = Some p ->
      verifyrule g p nleft nb res v ->
      verifyrule g (PNT i) (S nleft) nb res (i :: v)
  .

Goal
  forall g nb nleft,
  verifyrule g PEmpty nleft nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g a nb nleft,
  verifyrule g (PChar a) nleft nb (Some nb) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb nleft,
  verifyrule g PAnyChar nleft nb (Some nb) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb nleft,
  verifyrule g (PSequence PEmpty PEmpty) nleft nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb nleft,
  verifyrule g (PSequence PAnyChar PEmpty) nleft nb (Some nb) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb nleft,
  verifyrule g (PSequence PEmpty PAnyChar) nleft nb (Some nb) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PSequence (PNT 0) PEmpty) 0 nb None nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PSequence PEmpty (PNT 0)) 0 nb None nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule [PNT 1; PEmpty; g] (PSequence (PNT 0) PEmpty) 1 nb None [0].
Proof.
  intros.
  eapply VRSequenceNone; eauto using verifyrule.
  eapply VRNTSucc; eauto using verifyrule.
  simpl.
  eauto.
Qed.

Goal
  forall g nb,
  verifyrule [PNT 1; g] (PSequence PEmpty (PNT 0)) 1 nb None [0].
Proof.
  intros.
  eapply VRSequenceSomeTrue; eauto using verifyrule.
  eapply VRNTSucc; eauto using verifyrule.
  simpl.
  eauto.
Qed.

Goal
  forall g nb nleft,
  verifyrule g (PChoice PEmpty PEmpty) nleft nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb nleft,
  verifyrule g (PChoice PAnyChar PEmpty) nleft nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb nleft,
  verifyrule g (PChoice PEmpty PAnyChar) nleft nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb nleft,
  verifyrule g (PChoice PAnyChar PAnyChar) nleft nb (Some nb) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PChoice (PNT 0) PEmpty) 0 nb None nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PChoice PEmpty (PNT 0)) 0 nb None nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule (PNT 1 :: g) (PChoice (PNT 0) PEmpty) 1 nb None [0].
Proof.
  intros.
  eapply VRChoiceNone; eauto using verifyrule.
  eapply VRNTSucc; eauto using verifyrule.
  simpl.
  eauto.
Qed.

Goal
  forall nb,
  verifyrule
  [PAnyChar; PAnyChar]
  (PChoice (PNT 0) (PNT 1)) 1 nb (Some nb) [1].
Proof.
  intros.
  eapply VRChoiceSome;
  eapply VRNTSucc; simpl; eauto using verifyrule.
Qed.

Goal
  forall nb,
  verifyrule
  [PNT 7; PAnyChar]
  (PChoice (PNT 0) (PNT 1)) 1 nb None [0].
Proof.
  intros.
  eapply VRChoiceNone;
  eapply VRNTSucc; simpl; eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PRepetition PEmpty) 0 nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PRepetition PAnyChar) 0 nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PRepetition (PNT 0)) 0 nb None nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule (PNT 1 :: g) (PRepetition (PNT 0)) 1 nb None [0].
Proof.
  intros.
  eapply VRRepetition.
  eapply VRNTSucc; simpl; eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PNot PEmpty) 0 nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PNot PAnyChar) 0 nb (Some true) nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule g (PNot (PNT 0)) 0 nb None nil.
Proof.
  eauto using verifyrule.
Qed.

Goal
  forall g nb,
  verifyrule (PNT 1 :: g) (PNot (PNT 0)) 1 nb None [0].
Proof.
  intros.
  eapply VRNot.
  eapply VRNTSucc; simpl; eauto using verifyrule.
Qed.

Goal
  forall nleft,
  verifyrule [PNT 0] (PNT 0) nleft false None (repeat 0 nleft).
Proof.
  intros.
  induction nleft.
  - (* O *)
    eauto using verifyrule.
  - (* S nleft *)
    simpl.
    eapply VRNTSucc; simpl; auto.
Qed.

Lemma verifyrule_determinism :
  forall g p nleft nb res1 res2 v1 v2,
  verifyrule g p nleft nb res1 v1 ->
  verifyrule g p nleft nb res2 v2 ->
  res1 = res2 /\ v1 = v2.
Proof.
  intros * H1 H2.
  generalize dependent v2.
  generalize dependent res2.
  induction H1; intros;
  inversion H2; subst;
  try eq_nth_error;
  try lia;
  auto;
  try match goal with
  [ IHx: forall res v, verifyrule ?g ?p ?nleft ?nb res v -> _ = res /\ _ = v,
    Hx: verifyrule ?g ?p ?nleft ?nb _ _ |- _ ] =>
      apply IHx in Hx;
      destruct Hx;
      try discriminate;
      try destruct1;
      subst;
      auto
  end.
Qed.

Ltac pose_verifyrule_determinism :=
  repeat match goal with
    [ Hx1: verifyrule ?g ?p ?nleft ?nb ?res1 ?v1,
      Hx2: verifyrule ?g ?p ?nleft ?nb ?res2 ?v2 |- _ ] =>
          assert (res1 = res2 /\ v1 = v2)
          as [? ?]
          by eauto using verifyrule_determinism;
          clear Hx2
  end.

Lemma verifyrule_S_nleft :
  forall g p nleft nb nb' v,
  verifyrule g p nleft nb (Some nb') v ->
  verifyrule g p (S nleft) nb (Some nb') v.
Proof.
  intros * H.
  remember (Some nb').
  generalize dependent nb'.
  induction H; intros;
  try discriminate;
  eauto using verifyrule.
Qed.

Lemma verifyrule_nleft_le_some_determinism :
  forall g p nleft nleft' nb nb' v,
  verifyrule g p nleft nb (Some nb') v ->
  nleft <= nleft' ->
  verifyrule g p nleft' nb (Some nb') v.
Proof.
  intros * H Hle.
  induction Hle;
  eauto using verifyrule_S_nleft.
Qed.

Lemma verifyrule_nleft_some_determinism :
  forall g p nleft nleft' nb b b' v v',
  verifyrule g p nleft nb (Some b) v ->
  verifyrule g p nleft' nb (Some b') v' ->
  b = b' /\ v = v'.
Proof.
  intros * H H'.
  destruct (Compare_dec.le_ge_dec nleft nleft') as [Hle|Hge];
  try unfold ge in *;
  match goal with
    [ Hx: ?nleft <= ?nleft',
      Hy: verifyrule ?g ?p ?nleft ?nb (Some ?b) ?v,
      Hz: verifyrule ?g ?p ?nleft' ?nb (Some ?b') ?v' |- _ ] =>
          assert (verifyrule g p nleft' nb (Some b) v)
          by eauto using verifyrule_nleft_le_some_determinism
  end;
  pose_verifyrule_determinism;
  subst;
  destruct1;
  auto.
Qed.

Ltac pose_verifyrule_some_determinism :=
  repeat match goal with
    [ Hx1: verifyrule ?g ?p ?nleft1 ?nb (Some ?b1) ?v1,
      Hx2: verifyrule ?g ?p ?nleft2 ?nb (Some ?b2) ?v2 |- _ ] =>
          assert (b1 = b2 /\ v1 = v2)
          as [? ?]
          by eauto using verifyrule_nleft_some_determinism;
          clear Hx2
  end.

Lemma verifyrule_length_v_le_nleft :
  forall g p nleft nb res v,
  verifyrule g p nleft nb res v ->
  length v <= nleft.
Proof.
  intros * H.
  induction H; simpl; lia.
Qed.

Lemma verifyrule_length_v_eq_nleft :
  forall g p nleft nb v,
  verifyrule g p nleft nb None v ->
  length v = nleft.
Proof.
  intros * H.
  remember None.
  induction H;
  try discriminate;
  simpl;
  auto.
Qed.

Lemma verifyrule_i_in_v_lt_length_g :
  forall g p nleft nb res v i,
  verifyrule g p nleft nb res v ->
  In i v ->
  i < length g.
Proof.
  intros * H Hin.
  generalize dependent i.
  induction H; intros;
  try contradiction;
  eauto;
  try match goal with
    [ Hx: In _ (_ :: _) |- _ ] =>
        destruct Hin;
        try subst;
        auto;
        apply nth_error_Some;
        intro;
        eq_nth_error
  end.
Qed.

Inductive coherent_return_type_after_nleft_increase : option bool -> option bool -> Prop :=
  | FromNone :
      forall res,
      coherent_return_type_after_nleft_increase None res
  | FromSome :
      forall b,
      coherent_return_type_after_nleft_increase (Some b) (Some b)
  .

Lemma coherent_return_type_after_nleft_increase_transitive :
  forall res1 res2 res3,
  coherent_return_type_after_nleft_increase res1 res2 ->
  coherent_return_type_after_nleft_increase res2 res3 ->
  coherent_return_type_after_nleft_increase res1 res3.
Proof.
  intros * H12 H23.
  inversion H12; subst;
  eauto using coherent_return_type_after_nleft_increase.
Qed.

Ltac specialize_forall_eq :=
  match goal with
    [ Hx: forall y, ?C ?x = ?C y -> _ |- _ ] =>
        specialize (Hx x)
  end.

Ltac specialize_eq_refl :=
  match goal with
    [ Hx: ?x = ?x -> _ |- _ ] =>
        specialize (Hx (eq_refl x))
  end.

Ltac destruct_exists_hyp :=
  match goal with
    [ Hx: exists _, _ |- _ ] =>
        destruct Hx
  end.

Ltac destruct_and_hyp :=
  match goal with
    [ Hx: _ /\ _ |- _ ] =>
        destruct Hx
  end.

Lemma verifyrule_nleft_decrease :
  forall g p nleft nb res v,
  verifyrule g p (S nleft) nb res v ->
  exists res' v',
  coherent_return_type_after_nleft_increase res' res /\
  verifyrule g p nleft nb res' v'.
Proof.
  intros * H.
  remember (S nleft) as nleft'.
  generalize dependent nleft.
  induction H;
  intros;
  subst;
  try discriminate;
  try destruct1;
  try match goal with
    [ IHx: forall nleftx, ?nleft' = S nleftx -> _
      |- exists _ _, _ /\ verifyrule _ _ ?nleft' _ _ _ ] =>
          destruct nleft'
  end;
  repeat specialize_forall_eq;
  repeat specialize_eq_refl;
  repeat destruct_exists_hyp;
  repeat destruct_and_hyp;
  try match goal with
    [ Hx: coherent_return_type_after_nleft_increase _ _ |- _ ] =>
        inversion Hx; subst
  end;
  eauto using verifyrule, coherent_return_type_after_nleft_increase.
Qed.

Lemma verifyrule_nleft_le_coherent_result_type :
  forall g p nleft nleft' nb res v,
  verifyrule g p nleft' nb res v ->
  nleft <= nleft' ->
  exists res' v',
  coherent_return_type_after_nleft_increase res' res /\
  verifyrule g p nleft nb res' v'.
Proof.
  intros * Hv Hle.
  generalize dependent v.
  generalize dependent res.
  generalize dependent nb.
  generalize dependent p.
  generalize dependent g.
  induction Hle as [|nleft' Hle IH];
  intros.
  - (* nleft = nleft', prove for nleft' *)
    destruct res;
    eauto using coherent_return_type_after_nleft_increase.
  - (* nleft <= nleft', prove for (S nleft') *)
    assert (exists res' v',
            coherent_return_type_after_nleft_increase res' res /\
            verifyrule g p nleft' nb res' v')
    as [res' [v' [? ?]]]
    by eauto using verifyrule_nleft_decrease.
    assert (exists res'' v'',
            coherent_return_type_after_nleft_increase res'' res' /\
            verifyrule g p nleft nb res'' v'')
    as [res'' [v'' [? ?]]]
    by eauto.
    eauto using coherent_return_type_after_nleft_increase_transitive.
Qed.

Lemma verifyrule_res_none_or_some_true :
  forall g p nleft res v,
  verifyrule g p nleft true res v ->
  res = None \/ res = Some true.
Proof.
  intros * H.
  remember true.
  induction H; subst; eauto using verifyrule.
  match goal with
    [ Hx: true = true -> Some _ = None \/ Some _ = Some true |- _ ] =>
      specialize (Hx (eq_refl true)) as [? | ?];
      try discriminate;
      try destruct1;
      auto
  end.
Qed.

Inductive same_result_type : bool -> option bool -> bool -> option bool -> Prop :=
  | SRTLeftRecursive :
      forall nb nb',
      same_result_type nb None nb' None
  | SRTNotNullable :
      forall nb nb',
      same_result_type nb (Some nb) nb' (Some nb')
  | SRTNullable :
      forall b b',
      same_result_type b (Some true) b' (Some true)
  .

Lemma verifyrule_nb_change :
  forall g p nleft nb nb' res v,
  verifyrule g p nleft nb res v ->
  exists res', same_result_type nb res nb' res' /\ verifyrule g p nleft nb' res' v.
Proof.
  intros * H.
  generalize dependent nb'.
  induction H;
  intros;
  try discriminate;
  eauto using verifyrule, same_result_type;
  try match goal with
    [ IHx: forall _, exists _, _ /\ _
      |- exists _, _ /\ verifyrule _ _ _ ?nbx _ _ ] =>
          specialize (IHx nbx) as [? [Hsrt ?]];
          inversion Hsrt;
          subst;
          eauto using verifyrule, same_result_type;
          fail
  end.
  try match goal with
    [ IHx1: forall _, exists _, _ /\ verifyrule _ ?p1 _ _ _ _,
      IHx2: forall _, exists _, _ /\ verifyrule _ ?p2 _ _ _ _
      |- exists res, _ /\ verifyrule ?g (PChoice ?p1 ?p2) ?nleft ?nbx res ?v ] =>
          specialize (IHx1 nbx) as [res' [Hsrt1 ?]];
          inversion Hsrt1;
          subst;
          match goal with
            [ _: verifyrule ?g ?p1 ?nleft ?nbx (Some ?b) _ |- _ ] =>
                specialize (IHx2 b) as [res'' [Hsrt2 ?]];
                inversion Hsrt2;
                subst;
                eauto using verifyrule, same_result_type
          end
  end.
Qed.

Lemma verifyrule_nb_change_none :
  forall g p nleft nb nb' v,
  verifyrule g p nleft nb None v ->
  verifyrule g p nleft nb' None v.
Proof.
  intros * H.
  eapply verifyrule_nb_change with (nb' := nb') in H as [res' [Hsrt H]].
  inversion Hsrt; subst.
  auto.
Qed.

Ltac pose_verifyrule_nb_none :=
  try match goal with
    [ Hx1: verifyrule ?g ?p ?nleft _ None ?v,
      Hx2: verifyrule ?g ?p ?nleft ?nb _ _ |- _ ] =>
          assert (verifyrule g p nleft nb None v)
          by eauto using verifyrule_nb_change_none
  end.

Lemma verifyrule_v_independent_from_nb :
  forall g p nleft nb nb' res res' v v',
  verifyrule g p nleft nb res v ->
  verifyrule g p nleft nb' res' v' ->
  v = v'.
Proof.
  intros * H H'.
  generalize dependent v'.
  generalize dependent res'.
  generalize dependent nb'.
  induction H;
  intros;
  inversion H';
  subst;
  pose_verifyrule_nb_none;
  pose_verifyrule_determinism;
  try eq_nth_error;
  try discriminate;
  try f_equal;
  eauto.
Qed.

Lemma verifyrule_nullable_approx :
  forall g p s nleft nb res v,
  matches g p s (Success s) ->
  verifyrule g p nleft nb res v ->
  res = None \/ res = Some true.
Proof.
  intros * Hm Hv.
  remember (Success s).
  generalize dependent v.
  generalize dependent res.
  generalize dependent nb.
  generalize dependent nleft.
  induction Hm; intros;
  inversion Hv; subst;
  try destruct1;
  try discriminate;
  try match goal with
  [ Hx: ?s = String _ ?s |- _ ] =>
    exfalso; induction s; congruence; fail
  end;
  try match goal with
  [ Hm1: matches _ _ ?s1 (Success ?s2),
    Hm2: matches _ _ ?s2 (Success ?s1) |- _ ] =>
        assert (s1 = s2) by
        (eauto using matches_suffix, suffix_antisymmetric);
        subst
  end;
  try eq_nth_error;
  eauto using verifyrule_res_none_or_some_true;
  try match goal with
  [ IHx: _ -> forall nleft nb res v, verifyrule ?g ?p nleft nb res v -> _,
    Hx: verifyrule ?g ?p _ _ _ _ |- _ ] =>
      apply IHx in Hx; auto;
      destruct Hx; try discriminate; try destruct1;
      eauto using verifyrule_res_none_or_some_true;
      fail
  end.
Qed.

Theorem verifyrule_fast_forward_exists :
  forall g p nleft nb res v1 i v2,
  verifyrule g p nleft nb res (v1 ++ i :: v2) ->
  exists nleft' nb' res', verifyrule g (PNT i) nleft' nb' res' (i :: v2).
Proof.
  intros * H.
  remember (v1 ++ i :: v2) as v.
  generalize dependent v2.
  generalize dependent i.
  generalize dependent v1.
  induction H;
  intros;
  eauto using verifyrule;
  destruct v1;
  simpl in *;
  try discriminate;
  try destruct2;
  subst;
  eauto using verifyrule.
Qed.

Theorem verifyrule_fast_forward_none_exists :
  forall g p nleft nb v1 i v2,
  verifyrule g p nleft nb None (v1 ++ i :: v2) ->
  exists nleft' nb', verifyrule g (PNT i) nleft' nb' None (i :: v2).
Proof.
  intros * H.
  assert (exists nleft' nb' res', verifyrule g (PNT i) nleft' nb' res' (i :: v2))
  as [nleft' [nb' [res' ?]]]
  by eauto using verifyrule_fast_forward_exists.
  destruct res' as [b|]; eauto;
  remember (v1 ++ i :: v2) as v;
  generalize dependent v2;
  generalize dependent i;
  generalize dependent v1;
  generalize dependent nb';
  generalize dependent nleft';
  generalize dependent b;
  remember None as res;
  induction H;
  intros;
  eauto using verifyrule;
  destruct v1;
  simpl in *;
  try discriminate;
  try destruct2;
  eauto using verifyrule.
Qed.

Theorem verifyrule_fast_forward_none :
  forall g p nb nb' nleft v1 i v2,
  verifyrule g p nleft nb None (v1 ++ i :: v2) ->
  verifyrule g (PNT i) (1 + length v2) nb' None (i :: v2).
Proof.
  intros * H.
  assert (exists nleft' nb', verifyrule g (PNT i) nleft' nb' None (i :: v2))
  as [nleft' [nb'' ?]]
  by eauto using verifyrule_fast_forward_none_exists.
  assert (length (i :: v2) = nleft')
  by eauto using verifyrule_length_v_eq_nleft.
  subst.
  simpl in *.
  eauto using verifyrule_nb_change_none.
Qed.

Theorem verifyrule_replace_end :
  forall g p nleft nleft' nb nb' v1 i v2 v3,
  verifyrule g p nleft nb None (v1 ++ i :: v2) ->
  verifyrule g (PNT i) nleft' nb' None (i :: v3) ->
  length v2 <= length v3 ->
  verifyrule g p (1 + length v1 + length v3) nb None (v1 ++ i :: v3).
Proof.
  intros * Hvp Hvi Hle.
  assert (nleft = 1 + length v1 + length v2).
  {
    apply verifyrule_length_v_eq_nleft in Hvp.
    rewrite app_length in Hvp.
    simpl in Hvp.
    lia.
  }
  subst nleft.
  assert (nleft' = 1 + length v3).
  {
    apply verifyrule_length_v_eq_nleft in Hvi.
    simpl in Hvi.
    lia.
  }
  subst nleft'.
  assert (1 + length v1 + length v2 <= 1 + length v1 + length v3) by lia.
  remember (1 + length v1 + length v2) as nleft.
  remember None as res.
  remember (v1 ++ i :: v2) as v.
  generalize dependent v3.
  generalize dependent v2.
  generalize dependent i.
  generalize dependent v1.
  generalize dependent nb'.
  induction Hvp;
  intros;
  subst;
  try discriminate;
  repeat specialize_eq_refl;
  eauto using verifyrule, verifyrule_nleft_le_some_determinism.
  - (* PNT i *)
    destruct v1;
    simpl in *;
    try destruct1;
    try destruct2;
    eauto using verifyrule, verifyrule_nb_change_none, le_S_n.
Qed.

Theorem verifyrule_repetition_in_v :
  forall g p nleft v1 v2 v3 nb i,
  verifyrule g p nleft nb None (v1 ++ i :: v2 ++ i :: v3) ->
  exists nleft', verifyrule g p nleft' nb None (v1 ++ i :: v2 ++ i :: v2 ++ i :: v3).
Proof.
  intros * H.
  assert (verifyrule g (PNT i) (1 + length (v2 ++ i :: v3)) false None (i :: v2 ++ i :: v3))
  by eauto using verifyrule_fast_forward_none.
  assert (
    length v3 <= length (v2 ++ i :: v3)
  ).
  {
    rewrite app_length.
    simpl.
    lia.
  }
  assert (
    v1 ++ i :: v2 ++ i :: v2 ++ i :: v3 =
    (v1 ++ i :: v2) ++ i :: v2 ++ i :: v3
  ).
  {
    rewrite <- app_assoc.
    simpl.
    trivial.
  }
  assert (
    v1 ++ i :: v2 ++ i :: v3 =
    (v1 ++ i :: v2) ++ i :: v3
  ).
  {
    rewrite <- app_assoc.
    simpl.
    trivial.
  }
  match goal with
    [ Hverifyrule: verifyrule _ _ _ _ _ ?v,
      Heqv: ?v = _ |- _ ] =>
          rewrite Heqv in Hverifyrule
  end.
  match goal with
    [ Heqv: ?v = _
      |- exists _, verifyrule _ _ _ _ _ ?v ] =>
          rewrite Heqv
  end.
  eauto using verifyrule_replace_end.
Qed.

Theorem verifyrule_convergence_S_nleft :
  forall g p nleft nb res v,
  length g < nleft ->
  verifyrule g p nleft nb res v ->
  exists v', verifyrule g p (S nleft) nb res v'.
Proof.
  intros * Hlt Hv.
  destruct res.
  - (* Some b *)
    eauto using verifyrule_nleft_le_some_determinism.
  - (* None *)
    assert (length v = nleft)
    by eauto using verifyrule_length_v_eq_nleft.
    subst nleft.
    assert (exists i v1 v2 v3, v = v1 ++ i :: v2 ++ i :: v3)
    as [i [v1 [v2 [v3 Heqv]]]]
    by eauto using pigeonhole_principle, verifyrule_i_in_v_lt_length_g.
    subst v.
    apply verifyrule_repetition_in_v in Hv as [nleft Hv].
    assert (length (v1 ++ i :: v2 ++ i :: v2 ++ i :: v3) = nleft)
    by eauto using verifyrule_length_v_eq_nleft.
    subst nleft.
    match goal with
      [ Hx: verifyrule ?g ?p ?nleft ?nb None _
        |- exists v, verifyrule ?g ?p ?nleft' ?nb None v ] =>
            assert (nleft' <= nleft) by (repeat (rewrite app_length; simpl); lia)
    end.
    match goal with
      [ Hx: verifyrule _ _ ?nleft _ _ _, Hy: _ <= ?nleft |- _ ] =>
        specialize (verifyrule_nleft_le_coherent_result_type _ _ _ _ _ _ _ Hx Hy) as [? [? [? ?]]]
    end.
    match goal with
      [ Hx: coherent_return_type_after_nleft_increase _ _ |- _ ] =>
          inversion Hx; subst
    end.
    eauto.
Qed.

Theorem verifyrule_convergence :
  forall g p nleft nleft' nb res v,
  length g < nleft ->
  verifyrule g p nleft nb res v ->
  nleft <= nleft' ->
  exists v', verifyrule g p nleft' nb res v'.
Proof.
  intros * Hlt Hv Hle.
  induction Hle as [|nleft' Hle [v' IH]];
  eauto using verifyrule_convergence_S_nleft, Nat.lt_le_trans.
Qed.

(** VerifyRule function with gas **)

Fixpoint verifyrule_comp g p nleft nb gas {struct gas} :=
  match gas with
  | O => None
  | S gas' => match p with
              | PEmpty => Some (Some true, nil)
              | PChar _ => Some (Some nb, nil)
              | PAnyChar => Some (Some nb, nil)
              | PSequence p1 p2 => match verifyrule_comp g p1 nleft false gas' with
                                   | Some (Some true, _) => verifyrule_comp g p2 nleft nb gas'
                                   | Some (Some false, v) => Some (Some nb, v)
                                   | res => res
                                   end
              | PChoice p1 p2 => match verifyrule_comp g p1 nleft nb gas' with
                                 | Some (Some nb', _) => verifyrule_comp g p2 nleft nb' gas'
                                 | res => res
                                 end
              | PRepetition p' => verifyrule_comp g p' nleft true gas'
              | PNot p' => verifyrule_comp g p' nleft true gas'
              | PNT i => match nth_error g i with
                         | None => None
                         | Some p' => match nleft with
                                      | O => Some (None, nil)
                                      | S nleft' => match verifyrule_comp g p' nleft' nb gas' with
                                                    | Some (res, v) => Some (res, i :: v)
                                                    | None => None
                                                    end
                                      end
                         end
              end
  end.

Lemma verifyrule_comp_soundness :
  forall g p nleft nb gas res v,
  verifyrule_comp g p nleft nb gas = Some (res, v) ->
  verifyrule g p nleft nb res v.
Proof.
  intros * H.
  generalize dependent v.
  generalize dependent res.
  generalize dependent nb.
  generalize dependent nleft.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros;
  try discriminate;
  simpl in H;
  destruct p;
  try destruct1;
  eauto using verifyrule;
  try match goal with
    [ Hx: match nth_error ?g ?i with | _ => _ end = _ |- _ ] =>
        destruct (nth_error g i) eqn:?;
        try discriminate;
        match goal with
          [ Hx: match ?nleft with | _ => _ end = _ |- _ ] =>
              destruct nleft eqn:?;
              try destruct1;
              eauto using verifyrule
        end
  end;
  try match goal with
    [ Hx: match verifyrule_comp ?g ?p ?nleft ?nb ?gas with | _ => _ end = _ |- _ ] =>
        destruct (verifyrule_comp g p nleft nb gas) as [[[[]|]]|] eqn:?;
        try discriminate;
        try destruct1;
        eauto using verifyrule;
        fail
  end.
Qed.

Lemma verifyrule_comp_S_gas :
  forall g p nleft nb res v gas,
  verifyrule_comp g p nleft nb gas = Some (res, v) ->
  verifyrule_comp g p nleft nb (S gas) = Some (res, v).
Proof.
  intros.
  generalize dependent v.
  generalize dependent res.
  generalize dependent nb.
  generalize dependent nleft.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros;
  try discriminate;
  simpl in H;
  destruct p;
  try destruct1;
  remember (S gas) as gas';
  simpl;
  auto;
  try match goal with
      [ |- match nth_error ?g ?i with | _ => _ end = _ ] =>
        destruct (nth_error g i) eqn:?; auto;
        match goal with
          [ |- match ?nleft with | _ => _ end = _ ] =>
            destruct nleft; auto
        end
  end;
  try match goal with
    [ Hx: match verifyrule_comp ?g ?p ?nleft ?nb ?gas with | _ => _ end = _ |- _ ] =>
        let H := fresh in
        destruct (verifyrule_comp g p nleft nb gas) as [[[[]|]]|] eqn:H;
        try discriminate;
        try destruct1;
        apply IHgas in H;
        rewrite H;
        auto
  end.
Qed.

Lemma verifyrule_comp_le_gas :
  forall g p nleft nb gas1 gas2 res v,
  verifyrule_comp g p nleft nb gas1 = Some (res, v) ->
  gas1 <= gas2 ->
  verifyrule_comp g p nleft nb gas2 = Some (res, v).
Proof.
  intros * H Hle.
  induction Hle;
  auto using verifyrule_comp_S_gas.
Qed.

Lemma verifyrule_comp_termination :
  forall g p nleft nb,
  (forall r, In r g -> coherent g r true) ->
  coherent g p true ->
  exists gas res v,
  verifyrule_comp g p nleft nb gas = Some (res, v).
Proof.
  intros * Hgc Hpc.
  generalize dependent nb.
  generalize dependent p.
  generalize dependent g.
  induction nleft using strong_induction.
  intros.
  generalize dependent nb.
  generalize dependent nleft.
  generalize dependent g.
  induction p; intros;
  inversion Hpc; subst;
  try (exists 1; simpl; eauto; fail);
  try (
    let H := fresh in
    assert (exists gas res v, verifyrule_comp g p nleft true gas = Some (res, v))
    as [gas [res [v H]]] by auto;
    exists (1 + gas);
    simpl;
    rewrite H;
    eauto;
    fail
  ).
  - (* PSequence p1 p2 *)
    assert (exists gas res v, verifyrule_comp g p1 nleft false gas = Some (res, v))
    as [gas1 [res1 [v1 ?]]] by auto.
    assert (exists gas res v, verifyrule_comp g p2 nleft nb gas = Some (res, v))
    as [gas2 [res2 [v2 ?]]] by auto.
    assert (gas1 <= gas1 + gas2) by lia.
    assert (gas2 <= gas1 + gas2) by lia.
    assert (verifyrule_comp g p2 nleft nb (gas1 + gas2) = Some (res2, v2))
    by eauto using verifyrule_comp_le_gas.
    exists (1 + gas1 + gas2).
    simpl.
    let H := fresh in
    assert (verifyrule_comp g p1 nleft false (gas1 + gas2) = Some (res1, v1))
    as H by eauto using verifyrule_comp_le_gas;
    rewrite H.
    destruct res1 as [[|]|];
    eauto.
  - (* PChoice p1 p2 *)
    let H := fresh in
    assert (exists gas res v, verifyrule_comp g p1 nleft nb gas = Some (res, v))
    as [gas1 [res1 [v1 H]]] by auto;
    destruct res1 as [nb'|];
    try (
      exists (1 + gas1);
      simpl;
      rewrite H;
      eauto;
      fail
    ).
    assert (exists gas res v, verifyrule_comp g p2 nleft nb' gas = Some (res, v))
    as [gas2 [res2 [v2 ?]]] by auto.
    assert (gas1 <= gas1 + gas2) by lia.
    assert (gas2 <= gas1 + gas2) by lia.
    assert (verifyrule_comp g p2 nleft nb' (gas1 + gas2) = Some (res2, v2))
    by eauto using verifyrule_comp_le_gas.
    exists (1 + gas1 + gas2).
    simpl.
    let H := fresh in
    assert (verifyrule_comp g p1 nleft nb (gas1 + gas2) = Some (Some nb', v1))
    as H by eauto using verifyrule_comp_le_gas;
    rewrite H.
    eauto.
  - (* PNT n *)
    destruct nleft.
    + (* O *)
      exists 1. simpl.
      match goal with
        [ |- exists _ _, match ?x with | _ => _ end = _ ] =>
          destruct x; try discriminate; eauto
      end.
    + (* S nleft *)
      let H := fresh in
      assert (exists gas res v, verifyrule_comp g p nleft nb gas = Some (res, v))
      as [gas [res [v H]]] by eauto using nth_error_In;
      exists (1 + gas);
      simpl;
      match goal with
        [ Hx: ?lhs = ?rhs |- exists _ _, match ?lhs with | _ => _ end = _ ] =>
          rewrite Hx
      end;
      rewrite H;
      eauto.
Qed.

(** Nullable predicate **)
(** A "nullable" pattern may match successfully without consuming any characters **)

Inductive nullable : grammar -> pat -> nat -> option bool -> Prop :=
  | NEmpty :
      forall g nleft,
      nullable g PEmpty nleft (Some true)
  | NChar :
      forall g a nleft,
      nullable g (PChar a) nleft (Some false)
  | NAnyChar :
      forall g nleft,
      nullable g PAnyChar nleft (Some false)
  | NSequenceNone :
      forall g p1 p2 nleft,
      nullable g p1 nleft None ->
      nullable g (PSequence p1 p2) nleft None
  | NSequenceSomeFalse :
      forall g p1 p2 nleft,
      nullable g p1 nleft (Some false) ->
      nullable g (PSequence p1 p2) nleft (Some false)
  | NSequenceSomeTrue :
      forall g p1 p2 nleft res,
      nullable g p1 nleft (Some true) ->
      nullable g p2 nleft res ->
      nullable g (PSequence p1 p2) nleft res
  | NChoiceNone :
      forall g p1 p2 nleft,
      nullable g p1 nleft None ->
      nullable g (PChoice p1 p2) nleft None
  | NChoiceSomeFalse :
      forall g p1 p2 nleft res,
      nullable g p1 nleft (Some false) ->
      nullable g p2 nleft res ->
      nullable g (PChoice p1 p2) nleft res
  | NChoiceSomeTrue :
      forall g p1 p2 nleft,
      nullable g p1 nleft (Some true) ->
      nullable g (PChoice p1 p2) nleft (Some true)
  | NRepetition :
      forall g p nleft,
      nullable g (PRepetition p) nleft (Some true)
  | NNot :
      forall g p nleft,
      nullable g (PNot p) nleft (Some true)
  | NNTZero :
      forall g i p,
      nth_error g i = Some p ->
      nullable g (PNT i) O None
  | NNTSucc :
      forall g i p res nleft,
      nth_error g i = Some p ->
      nullable g p nleft res ->
      nullable g (PNT i) (S nleft) res
  .

(* ! {A <- A} |= A *)
Example nullable_ex1 :
  forall nleft b,
    ~ nullable
    [PNT 0]
    (PNT 0)
    nleft
    (Some b).
Proof.
  intros * H.
  remember (PNT 0) as p.
  remember [p] as g.
  remember (Some b) as res.
  induction H;
  try discriminate;
  try destruct1;
  simpl in H;
  destruct1;
  auto.
Qed.

(* G |= ε *)
Example nullable_ex2 :
  forall g nleft,
  nullable g PEmpty nleft (Some true).
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= 'a' *)
Example nullable_ex3 :
  forall g a nleft,
  nullable g (PChar a) nleft (Some false).
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= . *)
Example nullable_ex4 :
  forall g nleft,
  nullable g PAnyChar nleft (Some false).
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= ε ε *)
Example nullable_ex5 :
  forall g nleft,
  nullable g (PSequence PEmpty PEmpty) nleft (Some true).
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= . ε *)
Example nullable_ex6 :
  forall g nleft,
  nullable g (PSequence PAnyChar PEmpty) nleft (Some false).
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= ε . *)
Example nullable_ex7 :
  forall g nleft,
  nullable g (PSequence PEmpty PAnyChar) nleft (Some false).
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= . . *)
Example nullable_ex8 :
  forall g nleft,
  nullable g (PSequence PAnyChar PAnyChar) nleft (Some false).
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= ε / ε *)
Example nullable_ex9 :
  forall g nleft,
  nullable g (PChoice PEmpty PEmpty) nleft (Some true).
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= . / ε *)
Example nullable_ex10 :
  forall g nleft,
  nullable g (PChoice PAnyChar PEmpty) nleft (Some true).
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= ε / . *)
Example nullable_ex11 :
  forall g nleft,
  nullable g (PChoice PEmpty PAnyChar) nleft (Some true).
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= . / . *)
Example nullable_ex12 :
  forall g nleft,
  nullable g (PChoice PAnyChar PAnyChar) nleft (Some false).
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= p* *)
Example nullable_ex13 :
  forall g p nleft,
  nullable g (PRepetition p) nleft (Some true).
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= !p *)
Example nullable_ex14 :
  forall g p nleft,
  nullable g (PNot p) nleft (Some true).
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! { P <- . P } |= P *)
Example nullable_ex15 :
  forall nleft,
  nullable
    [PSequence PAnyChar (PNT 0)]
    (PNT 0)
    (S nleft)
    (Some false).
Proof.
  intros.
  econstructor; simpl; eauto.
  eauto using nullable.
Qed.

(* { P <- . P / ε } |= P *)
Example nullable_ex16 :
  forall nleft,
  nullable
    [PChoice (PSequence PAnyChar (PNT 0)) PEmpty]
    (PNT 0)
    (S nleft)
    (Some true).
Proof.
  intros.
  econstructor; simpl; eauto.
  eauto using nullable.
Qed.

(* ! {} |= A *)
Example nullable_ex17 :
  forall nleft res,
  ~ nullable [] (PNT 0) nleft res.
Proof.
  intros * H.
  inversion H;
  subst;
  try discriminate.
Qed.

(* { A <- 'a' A | ε ; B <- A A } |= A B *)
Example nullable_ex18 :
  forall nleft,
  nullable
  [PChoice (PSequence (PChar "a") (PNT 0)) PEmpty; PSequence (PNT 0) (PNT 0)]
  (PSequence (PNT 0) (PNT 1))
  (S (S nleft))
  (Some true).
Proof.
  intros.
  repeat match goal with
         | [ |- nullable _ (PSequence _ _) _ _ ] => econstructor
         | [ |- nullable _ (PNT _) _ _ ] => econstructor; simpl; eauto
         | [ |- nullable _ (PChoice _ _) _ _ ] => eauto using nullable
         | _ => fail
         end.
Qed.

Lemma nullable_determinism :
  forall g p nleft res1 res2,
  nullable g p nleft res1 ->
  nullable g p nleft res2 ->
  res1 = res2.
Proof.
  intros * H1 H2.
  generalize dependent res2.
  induction H1;
  intros;
  inversion H2; subst;
  try eq_nth_error;
  try match goal with
  [ IHx: forall resx, nullable ?g ?p ?nleft resx -> ?res1 = resx,
    Hx: nullable ?g ?p ?nleft ?res2 |- _ ] =>
        apply IHx in Hx;
        discriminate
  end;
  auto.
Qed.

Ltac pose_nullable_determinism :=
  match goal with
    [ Hx1: nullable ?g ?p ?nleft ?res1,
      Hx2: nullable ?g ?p ?nleft ?res2 |- _ ] =>
          assert (res1 = res2)
          by eauto using nullable_determinism;
          clear Hx2
  end.

Lemma nullable_Some_S_nleft :
  forall g p nleft b,
  nullable g p nleft (Some b) ->
  nullable g p (S nleft) (Some b).
Proof.
  intros * H.
  remember (Some b) as res.
  generalize dependent b.
  induction H; intros;
  try discriminate;
  eauto using nullable.
Qed.

Lemma nullable_Some_nleft_le :
  forall g p nleft nleft' b,
  nullable g p nleft (Some b) ->
  nleft <= nleft' ->
  nullable g p nleft' (Some b).
Proof.
  intros * H Hle.
  induction Hle;
  eauto using nullable_Some_S_nleft.
Qed.

Lemma verifyrule_similar_to_nullable :
  forall g p nleft b v,
  verifyrule g p nleft false (Some b) v ->
  nullable g p nleft (Some b).
Proof.
  intros * H.
  remember (Some b) as res.
  remember false as nb.
  generalize dependent b.
  induction H; intros;
  try destruct1;
  try discriminate;
  subst;
  eauto using nullable;
  try match goal with
    [ Hx: verifyrule _ _ _ false (Some ?nb') _ |- _ ] =>
        destruct nb'
  end;
  try match goal with
    [ Hx: verifyrule _ _ _ true (Some ?b) _ |- _ ] =>
        apply verifyrule_res_none_or_some_true in Hx as [|];
        try discriminate;
        try destruct1
  end;
  eauto using nullable.
Qed.

(** Nullable function with gas **)

Fixpoint nullable_comp g p nleft gas {struct gas} :=
  match gas with
  | O => None
  | S gas' => match p with
              | PEmpty => Some (Some true)
              | PChar _ => Some (Some false)
              | PAnyChar => Some (Some false)
              | PSequence p1 p2 => match nullable_comp g p1 nleft gas' with
                                   | Some (Some true) => nullable_comp g p2 nleft gas'
                                   | ob => ob
                                   end
              | PChoice p1 p2 => match nullable_comp g p1 nleft gas' with
                                 | Some (Some false) => nullable_comp g p2 nleft gas'
                                 | ob => ob
                                 end
              | PRepetition _ => Some (Some true)
              | PNot _ => Some (Some true)
              | PNT i => match nth_error g i with
                         | Some p' => match nleft with
                                      | O => Some None
                                      | S nleft' => nullable_comp g p' nleft' gas'
                                      end
                         | None => None
                         end
              end
  end.

Lemma nullable_comp_soundness :
  forall g p nleft gas res,
  nullable_comp g p nleft gas = Some res ->
  nullable g p nleft res.
Proof.
  intros * H.
  generalize dependent res.
  generalize dependent nleft.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros; try discriminate.
  destruct p; eauto using nullable;
  try (simpl in H; discriminate; fail);
  try (
    simpl in H;
    try destruct (nullable_comp g p1 nleft gas)
    as [[[|]|]|] eqn:?;
    try discriminate;
    try destruct1;
    eauto using nullable;
    fail
  );
  try (
    simpl in H;
    destruct (nth_error g n) eqn:?;
    try discriminate;
    try destruct1;
    destruct nleft;
    try discriminate;
    try destruct1;
    assert (In p g) as HIn by (eauto using nth_error_In);
    eauto using nullable;
    fail
  ).
Qed.

Ltac destruct_match_subject_in_goal :=
  match goal with
    [ |- match ?x with _ => _ end = _ ] =>
      destruct x
  end.

Ltac destruct_match_subject_in_hyp :=
  match goal with
    [ Hx: match ?x with _ => _ end = _ |- _ ] =>
      destruct x eqn:?
  end.

Lemma nullable_comp_S_gas :
  forall g p nleft gas res,
  nullable_comp g p nleft gas = Some res ->
  nullable_comp g p nleft (S gas) = Some res.
Proof.
  intros * H.
  generalize dependent res.
  generalize dependent nleft.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros; try discriminate;
  destruct p; simpl in H;
  try destruct1;
  auto;
  try (
    destruct (nullable_comp g p1 nleft gas) as [[[|]|]|] eqn:Hn1;
    destruct (nullable_comp g p2 nleft gas) as [[[|]|]|] eqn:Hn2;
    try discriminate;
    destruct1;
    try apply IHgas in Hn1;
    try apply IHgas in Hn2;
    remember (S gas);
    simpl;
    repeat destruct_match_subject_in_goal;
    try destruct1;
    try discriminate;
    auto
  ).
  try (
    destruct (nth_error g n) eqn:Hn;
    remember (S gas);
    simpl;
    destruct_match_subject_in_goal;
    try destruct1;
    try discriminate;
    auto;
    destruct_match_subject_in_goal;
    auto
  ).
Qed.

Lemma nullable_comp_le_gas :
  forall g p nleft gas1 gas2 res,
  nullable_comp g p nleft gas1 = Some res ->
  gas1 <= gas2 ->
  nullable_comp g p nleft gas2 = Some res.
Proof.
  intros * H Hle.
  induction Hle;
  auto using nullable_comp_S_gas.
Qed.

Fixpoint pat_size p :=
  match p with
  | PEmpty => 1
  | PChar _ => 1
  | PAnyChar => 1
  | PSequence p1 p2 => 1 + pat_size p1 + pat_size p2
  | PChoice p1 p2 => 1 + pat_size p1 + pat_size p2
  | PRepetition p => 1 + pat_size p
  | PNot p => 1 + pat_size p
  | PNT _ => 1
  end.

Fixpoint grammar_size g :=
  match g with
  | cons p g' => pat_size p + grammar_size g'
  | nil => 0
  end.

Lemma pat_size_le_grammar_size :
  forall p g,
  In p g ->
  pat_size p <= grammar_size g.
Proof.
  intros * HIn.
  generalize dependent p.
  induction g as [|p' g' IHg]; intros.
  + (* nil *)
    inversion HIn.
  + (* cons p' g' *)
    inversion HIn as [|HIn']; subst.
    - (* p = p' *)
      simpl.
      lia.
    - (* In p (p' :: g') *)
      simpl.
      specialize (IHg _ HIn').
      lia.
Qed.

(* Here, we could have used the max pat_size of the grammar
   instead of summing up the pat_size of each rule of the grammar,
   but the sum makes the proof of lower bound easier *)
Lemma nullable_comp_termination_lower_bound :
  forall g p nleft gas,
  (forall r, In r g -> coherent g r true) ->
  coherent g p true ->
  gas >= pat_size p + nleft * (grammar_size g) ->
  exists res, nullable_comp g p nleft gas = Some res.
Proof.
  intros * Hgc Hpc Hge.
  generalize dependent nleft.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros;
  try (destruct p; inversion Hge; fail);
  destruct p;
  inversion Hpc; subst;
  try (simpl; eauto; fail);
  try (
    simpl in Hge;
    assert (gas >= pat_size p1 + nleft * grammar_size g) by lia;
    assert (gas >= pat_size p2 + nleft * grammar_size g) by lia;
    assert (exists res, nullable_comp g p1 nleft gas = Some res) as [res1 Hn1] by auto;
    assert (exists res, nullable_comp g p2 nleft gas = Some res) by auto;
    simpl;
    rewrite Hn1;
    destruct res1 as [[|]|];
    eauto;
    fail
  );
  try (
    simpl in Hge;
    simpl;
    match goal with
      [ Hx: ?lhs = _ |-
        exists _, match ?lhs with | _ => _ end = _ ] =>
          rewrite Hx
    end;
    assert (In p g) as HIn by (eauto using nth_error_In);
    destruct nleft; eauto;
    specialize (pat_size_le_grammar_size _ _ HIn) as Hle;
    assert (gas >= pat_size p + nleft * grammar_size g) by lia;
    auto;
    fail
  ).
Qed.

(* Here, we don't care about any particular lower bound value.
   We just know there exists SOME gas for which nullable_comp
   gives SOME result. :-) *)
Lemma nullable_comp_termination :
  forall g p nleft,
  (forall r, In r g -> coherent g r true) ->
  coherent g p true ->
  exists gas b,
  nullable_comp g p nleft gas = Some b.
Proof.
  eauto using nullable_comp_termination_lower_bound.
Qed.

(** CheckLoops predicate **)
(** Check whether a pattern has potential infinite loops **)

Inductive checkloops : grammar -> pat -> nat -> option bool -> Prop :=
  | CLEmpty :
      forall g nleft,
      checkloops g PEmpty nleft (Some false)
  | CLChar :
      forall g a nleft,
      checkloops g (PChar a) nleft (Some false)
  | CLAnyChar :
      forall g nleft,
      checkloops g PAnyChar nleft (Some false)
  | CLSequenceNone :
      forall g p1 p2 nleft,
      checkloops g p1 nleft None ->
      checkloops g (PSequence p1 p2) nleft None
  | CLSequenceSomeTrue :
      forall g p1 p2 nleft,
      checkloops g p1 nleft (Some true) ->
      checkloops g (PSequence p1 p2) nleft (Some true)
  | CLSequenceSomeFalse :
      forall g p1 p2 res nleft,
      checkloops g p1 nleft (Some false) ->
      checkloops g p2 nleft res ->
      checkloops g (PSequence p1 p2) nleft res
  | CLChoiceNone :
      forall g p1 p2 nleft,
      checkloops g p1 nleft None ->
      checkloops g (PChoice p1 p2) nleft None
  | CLChoiceSomeTrue :
      forall g p1 p2 nleft,
      checkloops g p1 nleft (Some true) ->
      checkloops g (PChoice p1 p2) nleft (Some true)
  | CLChoiceSomeFalse :
      forall g p1 p2 nleft res,
      checkloops g p1 nleft (Some false) ->
      checkloops g p2 nleft res ->
      checkloops g (PChoice p1 p2) nleft res
  | CLRepetitionLR :
      forall g p nleft,
      nullable g p nleft None ->
      checkloops g (PRepetition p) nleft None
  | CLRepetitionNullable :
      forall g p nleft,
      nullable g p nleft (Some true) ->
      checkloops g (PRepetition p) nleft (Some true)
  | CLRepetitionNotNullable :
      forall g p nleft res,
      nullable g p nleft (Some false) ->
      checkloops g p nleft res ->
      checkloops g (PRepetition p) nleft res
  | CLNot :
      forall g p nleft res,
      checkloops g p nleft res ->
      checkloops g (PNot p) nleft res
  | CLNT :
      forall g i nleft,
      checkloops g (PNT i) nleft (Some false)
  .

Theorem checkloops_determinism :
  forall g p nleft b1 b2,
  checkloops g p nleft b1 ->
  checkloops g p nleft b2 ->
  b1 = b2.
Proof.
  intros * H1 H2.
  generalize dependent b2.
  induction H1; intros;
  inversion H2; subst;
  try assert (Some true = Some false) by auto;
  try assert (Some false = Some true) by auto;
  try assert (Some false = None) by auto;
  try assert (None = Some false) by auto;
  try pose_nullable_determinism;
  try discriminate;
  auto.
Qed.
