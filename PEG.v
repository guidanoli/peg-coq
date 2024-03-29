From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lists.List.
From Coq Require Import Lia.
From Peg Require Import Strong.
From Peg Require Import Suffix.

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
      inversion H; clear H; subst
  end.

Ltac destruct2 :=
  match goal with
  [ H: ?C _ _ = ?C _ _ |- _ ] =>
      inversion H; clear H; subst
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

Theorem matches_det :
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

Ltac pose_matches_det :=
  match goal with
  [ H1: matches ?g ?p ?s ?r1,
    H2: matches ?g ?p ?s ?r2 |- _ ] =>
        pose (matches_det g p s r1 r2 H1 H2)
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
  try pose_matches_det;
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

Theorem matches_comp_correct :
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

Corollary matches_comp_det :
  forall g p s gas1 gas2 res1 res2,
  matches_comp g p s gas1 = Some res1 ->
  matches_comp g p s gas2 = Some res2 ->
  res1 = res2.
Proof.
  eauto using matches_comp_correct, matches_det.
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

Theorem matches_comp_complete :
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

(** Nullable predicate **)
(** A "nullable" pattern may match successfully without consuming any characters **)

Inductive nullable : grammar -> pat -> Prop :=
  | NEmpty :
      forall g,
      nullable g PEmpty
  | NSequence :
      forall g p1 p2,
      nullable g p1 ->
      nullable g p2 ->
      nullable g (PSequence p1 p2)
  | NChoice1 :
      forall g p1 p2,
      nullable g p1 ->
      nullable g (PChoice p1 p2)
  | NChoice2 :
      forall g p1 p2,
      nullable g p2 ->
      nullable g (PChoice p1 p2)
  | NRepetition :
      forall g p,
      nullable g (PRepetition p)
  | NNot :
      forall g p,
      nullable g (PNot p)
  | NNonTerminal :
      forall g i p,
      nth_error g i = Some p ->
      nullable g p ->
      nullable g (PNT i)
  .

Ltac invert_nullable_and_clear :=
  match goal with
    [ Hx: nullable _ _ |- _ ] =>
        inversion Hx;
        clear Hx;
        subst
  end.

Ltac simpl_nth_error :=
  match goal with
    [ Hx: nth_error _ _ = _ |- _ ] =>
        simpl in Hx
  end.

(* ! {A <- A} |= A *)
Example nullable_ex1 :
  ~ nullable
    [PNT 0]
    (PNT 0).
Proof.
  intro.
  remember (PNT 0) as p.
  remember ([p]) as g.
  induction H;
  try discriminate;
  subst;
  destruct1;
  simpl in H;
  destruct1;
  auto.
Qed.

(* G |= ε *)
Example nullable_ex2 :
  forall g,
  nullable g PEmpty.
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= 'a' *)
Example nullable_ex3 :
  forall g a,
  ~ nullable g (PChar a).
Proof.
  intros * H.
  inversion H.
Qed.

(* ! G |= . *)
Example nullable_ex4 :
  forall g,
  ~ nullable g PAnyChar.
Proof.
  intros * H.
  inversion H.
Qed.

(* G |= ε ε *)
Example nullable_ex5 :
  forall g,
  nullable g (PSequence PEmpty PEmpty).
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= . ε *)
Example nullable_ex6 :
  forall g,
  ~ nullable g (PSequence PAnyChar PEmpty).
Proof.
  intros * H.
  repeat invert_nullable_and_clear.
Qed.

(* ! G |= ε . *)
Example nullable_ex7 :
  forall g,
  ~ nullable g (PSequence PEmpty PAnyChar).
Proof.
  intros * H.
  repeat invert_nullable_and_clear.
Qed.

(* ! G |= . . *)
Example nullable_ex8 :
  forall g,
  ~ nullable g (PSequence PAnyChar PAnyChar).
Proof.
  intros * H.
  repeat invert_nullable_and_clear.
Qed.

(* G |= ε / ε *)
Example nullable_ex9 :
  forall g,
  nullable g (PChoice PEmpty PEmpty).
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= . / ε *)
Example nullable_ex10 :
  forall g,
  nullable g (PChoice PAnyChar PEmpty).
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= ε / . *)
Example nullable_ex11 :
  forall g,
  nullable g (PChoice PEmpty PAnyChar).
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! G |= . / . *)
Example nullable_ex12 :
  forall g,
  ~ nullable g (PChoice PAnyChar PAnyChar).
Proof.
  intros * H.
  repeat invert_nullable_and_clear.
Qed.

(* G |= p* *)
Example nullable_ex13 :
  forall g p,
  nullable g (PRepetition p).
Proof.
  intros.
  eauto using nullable.
Qed.

(* G |= !p *)
Example nullable_ex14 :
  forall g p,
  nullable g (PNot p).
Proof.
  intros.
  eauto using nullable.
Qed.

(* ! { P <- . P } |= P *)
Example nullable_ex15 :
  ~ nullable
    [PSequence PAnyChar (PNT 0)]
    (PNT 0).
Proof.
  intros * H.
  invert_nullable_and_clear.
  simpl_nth_error.
  destruct1.
  invert_nullable_and_clear.
  match goal with
    [ Hx: nullable _ PAnyChar |- _ ] =>
      inversion Hx
  end.
Qed.

(* { P <- . P / ε } |= P *)
Example nullable_ex16 :
  nullable
    [PChoice (PSequence PAnyChar (PNT 0)) PEmpty]
    (PNT 0).
Proof.
  econstructor; simpl; eauto.
  eauto using nullable.
Qed.

(* ! {} |= A *)
Example nullable_ex17 :
  ~ nullable [] (PNT 0).
Proof.
  intros * H.
  inversion H; subst.
  simpl in *.
  discriminate.
Qed.

(* { A <- 'a' A | ε ; B <- A A } |= A B *)
Example nullable_ex18 :
  nullable
  [PChoice (PSequence (PChar "a") (PNT 0)) PEmpty; PSequence (PNT 0) (PNT 0)]
  (PSequence (PNT 0) (PNT 1)).
Proof.
  repeat match goal with
         | [ |- nullable _ (PSequence _ _) ] => econstructor
         | [ |- nullable _ (PNT _) ] => econstructor; simpl; eauto
         | [ |- nullable _ (PChoice _ _) ] => eauto using nullable
         | _ => fail
         end.
Qed.

Lemma nullable_approx :
  forall g p s,
  matches g p s (Success s) ->
  nullable g p.
Proof.
  intros * H.
  remember (Success s).
  induction H;
  try discriminate;
  try destruct1;
  try (exfalso; induction s; congruence; fail);
  try (
    subst;
    match goal with
    [ Hm1: matches _ _ ?s1 (Success ?s2),
      Hm2: matches _ _ ?s2 (Success ?s1) |- _ ] =>
          assert (s1 = s2) by
          (eauto using matches_suffix, suffix_antisymmetric)
    end;
    subst
  );
  eauto using nullable.
Qed.

Theorem proper_suffix_if_not_nullable :
  forall g p s s',
  ~ nullable g p ->
  matches g p s (Success s') ->
  proper_suffix s' s.
Proof.
  intros * H1 H2.
  specialize (matches_suffix _ _ _ _ H2) as H3.
  induction H3 as [|s s' a H3 IHsuffix].
  - (* SuffixRefl *)
    exfalso.
    eauto using nullable_approx.
  - (* SuffixChar *)
    eauto using suffix_is_proper_suffix_with_char.
Qed.

(** Nullable function with gas
    "rr" stands for "remaining rules" **)

Fixpoint nullable_comp g p rr gas {struct gas} :=
  match gas with
  | O => None
  | S gas' => match p with
              | PEmpty => Some true
              | PChar _ => Some false
              | PAnyChar => Some false
              | PSequence p1 p2 => match nullable_comp g p1 rr gas' with
                                   | Some true => nullable_comp g p2 rr gas'
                                   | ob => ob
                                   end
              | PChoice p1 p2 => match nullable_comp g p1 rr gas' with
                                 | Some false => nullable_comp g p2 rr gas'
                                 | ob => ob
                                 end
              | PRepetition _ => Some true
              | PNot _ => Some true
              | PNT i => match nth_error g i with
                         | Some p' => match rr with
                                      | O => Some false
                                      | S rr' => nullable_comp g p' rr' gas'
                                      end
                         | None => Some false
                         end
              end
  end.

Ltac destruct_match_subject :=
  match goal with
    [ |- match ?x with _ => _ end = _ ] =>
      destruct x
  end.

Lemma nullable_comp_S_gas :
  forall g p rr gas b,
  nullable_comp g p rr gas = Some b ->
  nullable_comp g p rr (S gas) = Some b.
Proof.
  intros * H.
  generalize dependent b.
  generalize dependent rr.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros; try discriminate;
  destruct p; simpl in H;
  try destruct1;
  auto;
  try (
    destruct (nullable_comp g p1 rr gas) as [[|]|] eqn:Hn1;
    destruct (nullable_comp g p2 rr gas) as [[|]|] eqn:Hn2;
    try discriminate;
    destruct1;
    try apply IHgas in Hn1;
    try apply IHgas in Hn2;
    remember (S gas);
    simpl;
    repeat destruct_match_subject;
    try destruct1;
    try discriminate;
    auto
  ).
  try (
    destruct (nth_error g n) eqn:Hn;
    remember (S gas);
    simpl;
    destruct_match_subject;
    try destruct1;
    try discriminate;
    auto;
    destruct_match_subject;
    auto
  ).
Qed.

Lemma nullable_comp_le_gas :
  forall g p v gas1 gas2 b,
  nullable_comp g p v gas1 = Some b ->
  gas1 <= gas2 ->
  nullable_comp g p v gas2 = Some b.
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

Lemma nullable_comp_complete :
  forall g p rr gas,
  gas >= pat_size p + rr * (grammar_size g) ->
  exists b, nullable_comp g p rr gas = Some b.
Proof.
  intros * Hge.
  generalize dependent rr.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros;
  try (destruct p; inversion Hge; fail);
  destruct p;
  try (simpl; eauto; fail);
  try (
    simpl in Hge;
    assert (gas >= pat_size p1 + rr * grammar_size g) as Hge1 by lia;
    assert (gas >= pat_size p2 + rr * grammar_size g) as Hge2 by lia;
    clear Hge;
    specialize (IHgas _ _ _ Hge1) as H1;
    destruct H1 as [n1 H1];
    specialize (IHgas _ _ _ Hge2) as H2;
    simpl;
    simpl in H1;
    rewrite H1;
    destruct n1;
    eauto;
    fail
  );
  try (
    simpl in Hge;
    simpl;
    destruct (nth_error g n) as [p|] eqn:Hnth; eauto;
    assert (In p g) as HIn by (eauto using nth_error_In);
    destruct rr; eauto;
    specialize (pat_size_le_grammar_size _ _ HIn) as Hle;
    assert (gas >= pat_size p + rr * grammar_size g) by lia;
    auto
  ).
Qed.

Lemma nullable_comp_some_true_is_nullable :
  forall g p rr gas,
  nullable_comp g p rr gas = Some true ->
  nullable g p.
Proof.
  intros * H.
  generalize dependent rr.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros; try discriminate.
  destruct p; eauto using nullable;
  try (simpl in H; discriminate; fail);
  try (
    simpl in H;
    destruct (nullable_comp g p1 rr gas) as [[|]|] eqn:H1; try discriminate;
    eauto using nullable;
    fail
  );
  try (
    simpl in H;
    destruct (nth_error g n) eqn:Hnth; try discriminate;
    destruct rr; try discriminate;
    eauto using nullable;
    fail
  ).
Qed.

(** Hungry predicate **)
(** A "hungry" pattern always consumes a character on a successful match **)

Inductive hungry : grammar -> pat -> bool -> Prop :=
  | HEmpty :
      forall g,
      hungry g PEmpty false
  | HChar :
      forall g a,
      hungry g (PChar a) true
  | HAnyChar :
      forall g,
      hungry g PAnyChar true
  | HSequenceTrue1 :
      forall g p1 p2,
      hungry g p1 true ->
      hungry g (PSequence p1 p2) true
  | HSequenceTrue2 :
      forall g p1 p2,
      hungry g p2 true ->
      hungry g (PSequence p1 p2) true
  | HSequenceFalse :
      forall g p1 p2,
      hungry g p1 false ->
      hungry g p2 false ->
      hungry g (PSequence p1 p2) false
  | HChoiceTrue :
      forall g p1 p2,
      hungry g p1 true ->
      hungry g p2 true ->
      hungry g (PChoice p1 p2) true
  | HChoiceFalse1 :
      forall g p1 p2,
      hungry g p1 false ->
      hungry g (PChoice p1 p2) false
  | HChoiceFalse2 :
      forall g p1 p2,
      hungry g p2 false ->
      hungry g (PChoice p1 p2) false
  | HRepetition :
      forall g p,
      hungry g (PRepetition p) false
  | HNot :
      forall g p,
      hungry g (PNot p) false
  | HNonTerminal :
      forall g i p b,
      nth_error g i = Some p ->
      hungry g p b ->
      hungry g (PNT i) b
  .

Lemma string_not_infinite :
  forall a s,
  s <> String a s.
Proof.
  intros * Hcontra.
  induction s; congruence.
Qed.

Theorem hungry_correct :
  forall g p, hungry g p true -> ~ exists s, matches g p s (Success s).
Proof.
  intros * H1 H2.
  remember true as b.
  induction H1;
  try discriminate;
  destruct H2 as [s H2];
  inversion H2; subst;
  try (eapply string_not_infinite; eauto; fail);
  try eq_nth_error;
  try match goal with [
    Hx1: matches _ _ s (Success ?saux),
    Hx2: matches _ _ ?saux (Success s) |- _
  ] =>
    assert (s = saux) by (eauto using suffix_antisymmetric, matches_suffix);
    subst
  end;
  eauto.
Qed.

Lemma hungry_det :
  forall g p b1 b2,
  hungry g p b1 ->
  hungry g p b2 ->
  b1 = b2.
Proof.
  intros * H1 H2.
  induction H1; intros;
  inversion H2; subst;
  try eq_nth_error;
  eauto.
Qed.

Theorem matches_hungry_proper_suffix :
  forall g p s s',
  hungry g p true ->
  matches g p s (Success s') ->
  proper_suffix s' s.
Proof.
  intros * H1 H2.
  specialize (matches_suffix _ _ _ _ H2) as H3.
  induction H3 as [|s s' a H3 IHsuffix].
  - (* SuffixRefl *)
    exfalso.
    eauto using (hungry_correct _ _ H1).
  - (* SuffixChar *)
    eauto using suffix_is_proper_suffix_with_char.
Qed.

(** Hungry function with gas **)

Fixpoint hungry_comp g p gas {struct gas} :=
  match gas with
  | O => None
  | S gas' => match p with
              | PChar _ => Some true
              | PAnyChar => Some true
              | PSequence p1 p2 => let b1 := hungry_comp g p1 gas' in
                                   let b2 := hungry_comp g p2 gas' in
                                   match b1, b2 with
                                   | Some true, _ => Some true
                                   | _, Some true => Some true
                                   | Some false, Some false => Some false
                                   | _, _ => None
                                   end
              | PChoice p1 p2 => let b1 := hungry_comp g p1 gas' in
                                 let b2 := hungry_comp g p2 gas' in
                                 match b1, b2 with
                                 | Some true, Some true => Some true
                                 | Some false, _ => Some false
                                 | _, Some false => Some false
                                 | _, _ => None
                                 end
              | PNT i => match nth_error g i with
                         | Some p' => hungry_comp g p' gas'
                         | None => None
                         end
              | _ => Some false
              end
  end.

Theorem hungry_comp_correct :
  forall g p gas b,
  hungry_comp g p gas = Some b ->
  hungry g p b.
Proof.
  intros * H.
  generalize dependent b.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros;
  destruct p; simpl in H;
  try (
    remember (hungry_comp g p1 gas) as ores1 eqn:H1;
    remember (hungry_comp g p2 gas) as ores2 eqn:H2;
    symmetry in H1;
    symmetry in H2;
    destruct ores1 as [[]|];
    destruct ores2 as [[]|];
    try discriminate;
    eauto using hungry
  );
  try (
    destruct b;
    try discriminate;
    eauto using hungry;
    fail
  ).
  - (* PNT n *)
    destruct (nth_error g n) eqn:Hnth; try discriminate.
    eauto using hungry.
Qed.

Theorem hungry_comp_det :
  forall g p gas1 gas2 b1 b2,
  hungry_comp g p gas1 = Some b1 ->
  hungry_comp g p gas2 = Some b2 ->
  b1 = b2.
Proof.
  eauto using hungry_comp_correct, hungry_det.
Qed.

Lemma hungry_comp_S_gas_some :
  forall g p gas b,
  hungry_comp g p gas = Some b ->
  hungry_comp g p (S gas) = Some b.
Proof.
  intros * H.
  generalize dependent b.
  generalize dependent p.
  generalize dependent g.
  induction gas; intros; try discriminate.
  destruct p; simpl in H;
  try (injection H as H; subst; auto);
  try (
    destruct (hungry_comp g p1 gas) as [[]|] eqn:Haux1;
    destruct (hungry_comp g p2 gas) as [[]|] eqn:Haux2;
    try discriminate;
    try apply IHgas in Haux1;
    try apply IHgas in Haux2;
    remember (S gas) as gas';
    simpl;
    try rewrite Haux1;
    try rewrite Haux2;
    destruct (hungry_comp g p1 gas') as [[]|];
    auto;
    fail
  );
  try (
    remember (S gas);
    simpl;
    auto;
    fail
  ).
  - (* PNT n *)
    destruct (nth_error g n) eqn:H1;
    try apply IHgas in H;
    remember (S gas);
    simpl;
    rewrite H1;
    auto.
Qed.

Lemma hungry_comp_S_gas_none :
  forall g p gas,
  hungry_comp g p (S gas) = None ->
  hungry_comp g p gas = None.
Proof.
  intros.
  destruct (hungry_comp g p gas) eqn:H'; trivial.
  apply hungry_comp_S_gas_some in H'.
  rewrite H' in H.
  discriminate.
Qed.

Lemma hungry_comp_gas_some_le :
  forall g p gas gas' b,
  hungry_comp g p gas = Some b ->
  gas <= gas' ->
  hungry_comp g p gas' = Some b.
Proof.
  intros * H1 Hle.
  induction Hle; auto.
  eauto using hungry_comp_S_gas_some.
Qed.

Lemma hungry_comp_gas_none_le :
  forall g p gas gas',
  hungry_comp g p gas' = None ->
  gas <= gas' ->
  hungry_comp g p gas = None.
Proof.
  intros * H1 Hle.
  induction Hle; auto.
  eauto using hungry_comp_S_gas_none.
Qed.

Theorem hungry_comp_complete_true :
  forall g p b,
  hungry g p b ->
  (exists gas, hungry_comp g p gas = Some b).
Proof.
  intros * H.
  induction H;
  (* Cases with no recursive calls *)
  try (exists 1; auto; fail);
  (* Cases with one recursive call *)
  try (
    destruct IHhungry as [gas IH];
    exists (1 + gas);
    simpl;
    try rewrite_match_subject_in_goal;
    eauto;
    fail
  );
  (* Cases with two recursive calls *)
  try (
    destruct IHhungry as [gas IH];
    exists (1 + gas);
    simpl;
    destruct (hungry_comp g p1 gas) as [[]|] eqn:Haux1; auto;
    destruct (hungry_comp g p2 gas) as [[]|] eqn:Haux2; auto;
    try discriminate
  );
  try (
    destruct IHhungry1 as [gas1 IH1];
    destruct IHhungry2 as [gas2 IH2];
    exists (1 + gas1 + gas2);
    simpl;
    specialize (Nat.le_add_r gas1 gas2) as Hle1;
    rewrite (hungry_comp_gas_some_le _ _ _ _ _ IH1 Hle1);
    specialize (Plus.le_plus_r gas1 gas2) as Hle2;
    rewrite (hungry_comp_gas_some_le _ _ _ _ _ IH2 Hle2);
    trivial
  ).
Qed.

(** Well-formed predicate **)
(** A "well-formed" pattern is guaranteed to yield a match result for any input string **)

Inductive well_formed : list pat -> pat -> Prop :=
  | WFEmpty :
      forall g,
      well_formed g PEmpty
  | WFChar :
      forall g a,
      well_formed g (PChar a)
  | WFAnyChar :
      forall g,
      well_formed g PAnyChar
  | WFSequence :
      forall g p1 p2,
      well_formed g p1 ->
      well_formed g p2 ->
      well_formed g (PSequence p1 p2)
  | WFChoice :
      forall g p1 p2,
      well_formed g p1 ->
      well_formed g p2 ->
      well_formed g (PChoice p1 p2)
  | WFRepetition :
      forall g p,
      well_formed g p ->
      ~ nullable g p ->
      well_formed g (PRepetition p)
  | WFNot :
      forall g p,
      well_formed g p ->
      well_formed g (PNot p)
  | WFNonTerminal :
      forall g p i,
      nth_error g i = Some p ->
      well_formed g (PNT i)
  .

Theorem well_formed_correct :
  forall g p s, well_formed g p -> exists res, matches g p s res.
Proof with eauto using matches.
  intros * H.
  generalize dependent s.
  induction H; intros.
  - (* PEmpty *)
    eauto using matches.
  - (* PChar a *)
    destruct s as [|a'].
    + (* EmptyString *)
      eauto using matches.
    + (* String a' s' *)
      destruct (ascii_dec a a');
      subst...
  - (* PAnyChar *)
    destruct s...
  - (* PSequence p1 p2 *)
    destruct (IHwell_formed1 s) as [[|s1]].
    + (* Failure *)
      eauto using matches.
    + (* Success s1 *)
      destruct (IHwell_formed2 s1)...
  - (* PChoice p1 p2 *)
    destruct (IHwell_formed2 s).
    destruct (IHwell_formed1 s) as [[|]]...
  - (* PRepetition p *)
    remember (String.length s) as n.
    generalize dependent s.
    induction n as [n IHn] using strong_induction; intros.
    destruct (IHwell_formed s) as [[|s1]].
    + (* Failure *)
      eauto using matches.
    + (* Success s1 *)
      subst.
      match goal with [
        Hx: ~ nullable ?g ?p,
        Hy: matches ?g ?p _ (Success ?s) |- _
      ] =>
        specialize (proper_suffix_if_not_nullable _ _ _ _ Hx Hy) as Hps;
        specialize (proper_suffix_length_lt _ _ Hps) as Hlt;
        specialize (eq_refl (String.length s)) as Hlen;
        destruct (IHn _ Hlt _ Hlen)
      end.
      eauto using matches.
  - (* PNot p *)
    destruct (IHwell_formed s) as [[|]]...
  - (* PNT i *)
Abort.

(** Well-formed function with gas **)

Fixpoint well_formed_comp g p gas :=
  match gas with
  | O => None
  | S gas' => match p with
              | PEmpty => Some true
              | PChar _ => Some true
              | PAnyChar => Some true
              | PSequence p1 p2 => let b1 := well_formed_comp g p1 gas' in
                                   let b2 := well_formed_comp g p2 gas' in
                                   match b1, b2 with
                                   | Some true, Some true => Some true
                                   | None, None => None
                                   | _, _ => Some false
                                   end
              | PChoice p1 p2 => let b1 := well_formed_comp g p1 gas' in
                                 let b2 := well_formed_comp g p2 gas' in
                                 match b1, b2 with
                                 | Some true, Some true => Some true
                                 | None, None => None
                                 | _, _ => Some false
                                 end
              | PRepetition p => let b1 := well_formed_comp g p gas' in
                                 let b2 := hungry_comp g p gas' in
                                 match b1, b2 with
                                 | Some true, Some true => Some true
                                 | None, None => None
                                 | _, _ => Some false
                                 end
              | PNot p => well_formed_comp g p gas'
              | PNT i => match nth_error g i with
                         | Some p => Some true
                         | None => Some false
                         end
              end
  end.

Theorem well_formed_comp_correct_true :
  forall g p gas,
  (forall p', In p' g -> well_formed g p') ->
  well_formed_comp g p gas = Some true ->
  well_formed g p.
Proof.
  intros g p.
  generalize dependent g.
  induction p; intros * Hg H;
  eauto using well_formed;
  try (
    destruct gas;
    try discriminate;
    simpl in H;
    destruct (well_formed_comp g p1 gas) as [[]|] eqn:H1;
    destruct (well_formed_comp g p2 gas) as [[]|] eqn:H2;
    try discriminate;
    eauto using well_formed
  ).
  - (* PRepetition p *)
    destruct gas; try discriminate.
    simpl in H.
    destruct (well_formed_comp g p gas) as [[]|] eqn:H1;
    destruct (hungry_comp g p gas) as [[]|] eqn:H2;
    try discriminate.
    eauto using well_formed, hungry_comp_correct_true.
  - (* PNot p *)
    destruct gas; try discriminate.
    simpl in H.
    destruct (well_formed_comp g p gas) as [[]|] eqn:H1;
    try discriminate.
    eauto using well_formed.
  - (* PNT n *)
    destruct gas; try discriminate.
    simpl in H.
    destruct (nth_error g n) eqn:H1; try discriminate;
    destruct (well_formed_comp g p gas) as [[]|] eqn:H2;
    try discriminate.
    eauto using well_formed, nth_error_In.
Qed.
