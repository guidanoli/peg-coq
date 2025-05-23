From Coq Require Import Lists.List.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import Arith.PeanoNat.
From Peg Require Import Syntax.
From Peg Require Import Tactics.
From Peg Require Import Suffix.
From Peg Require Import Charset.

Inductive MatchResult : Type :=
  | Failure : MatchResult            (* Pattern failed to match.            *)
  | Success : string -> MatchResult  (* Pattern matched and left string s.  *)
  .

Inductive matches : grammar -> pat -> string -> MatchResult -> Prop :=
  | MEmptySuccess :
      forall g s,
      matches g PEmpty s (Success s)
  | MSetSuccess :
      forall g cs a s,
      cs a = true ->
      matches g (PSet cs) (String a s) (Success s)
  | MSetFailureEmptyString :
      forall g cs,
      matches g (PSet cs) EmptyString Failure
  | MSetFailureString :
      forall g cs a s,
      cs a = false ->
      matches g (PSet cs) (String a s) Failure
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
  | MAndSuccess :
      forall g p s s',
      matches g p s (Success s') ->
      matches g (PAnd p) s (Success s)
  | MAndFailure :
      forall g p s,
      matches g p s Failure ->
      matches g (PAnd p) s Failure
  | MNonTerminalSome :
      forall g i p s res,
      nth_error g i = Some p ->
      matches g p s res ->
      matches g (PNT i) s res
  .

(** Match tactics **)

Ltac apply_matches_IH :=
  match goal with [
    IHx: forall r, matches ?g ?p ?s r -> _ = r,
    Hx: matches ?g ?p ?s _ |- _
  ] =>
    apply IHx in Hx
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
  try destruct1sep;
  try destruct2sep;
  auto.
Qed.

Ltac pose_matches_determinism :=
  match goal with
  [ H1: matches ?g ?p ?s ?r1,
    H2: matches ?g ?p ?s ?r2 |- _ ] =>
        assert (r1 = r2) by eauto using matches_determinism
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

Example infinite_loop_rule :
  forall g i s,
  nth_error g i = Some (PNT i) ->
  ~ (exists res, matches g (PNT i) s res).
Proof.
  intros * H1 [res H2].
  remember (PNT i).
  induction H2;
  try destruct1;
  try destruct2sep;
  try discriminate;
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

(** If-then-else pattern **)

Ltac assert_matches g p s res :=
  assert (matches g p s res) by eauto using matches.

Ltac invert_matches p :=
  match goal with
    [ Hx: matches _ p _ _ |- _ ] =>
        inversion Hx; subst
  end.

Lemma matches_if_then_else :
  forall g pcond p1 p2 s rescond res,
  matches g pcond s rescond ->
  matches g (PChoice (PSequence (PAnd pcond) p1) (PSequence (PNot pcond) p2)) s res <->
  matches g (match rescond with Success _ => p1 | Failure => p2 end) s res.
Proof.
  intros * Hcond.
  split; intro H.
  - (* -> *)
    destruct rescond.
    + (* pcond fails *)
      assert_matches g (PAnd pcond) s Failure.
      assert_matches g (PSequence (PAnd pcond) p1) s Failure.
      assert_matches g (PNot pcond) s (Success s).
      inversion H; subst;
      try (pose_matches_determinism; discriminate).
      invert_matches (PSequence (PNot pcond) p2);
      pose_matches_determinism;
      try discriminate;
      destruct1.
      auto.
    + (* pcond matches *)
      assert_matches g (PNot pcond) s Failure.
      assert_matches g (PSequence (PNot pcond) p2) s Failure.
      assert_matches g (PAnd pcond) s (Success s).
      inversion H; subst.
      -- (* &pcond p1 matches *)
         invert_matches (PSequence (PAnd pcond) p1).
         pose_matches_determinism.
         destruct1.
         auto.
      -- (* &pcond p1 fails *)
         invert_matches (PSequence (PAnd pcond) p1).
         ++ (* p1 fails *)
            pose_matches_determinism.
            destruct1.
            pose_matches_determinism.
            subst.
            auto.
         ++ (* &pcond fails *)
            pose_matches_determinism.
            discriminate.
  - (* <- *)
    destruct rescond.
    + (* pcond fails *)
      eauto 6 using matches.
    + (* pcond matches *)
      destruct res;
      eauto 6 using matches.
Qed.

(** Match function with gas **)

Fixpoint matches_comp g p s gas {struct gas} :=
  match gas with
  | O => None
  | S gas' => match p with
              | PEmpty => Some (Success s)
              | PSet cs => match s with
                           | EmptyString => Some Failure
                           | String a s' => if cs a
                                            then Some (Success s')
                                            else Some Failure
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
              | PAnd p' => match matches_comp g p' s gas' with
                           | Some Failure => Some Failure
                           | Some (Success _) => Some (Success s)
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
  - (* PSet cs *)
    match goal with
      [ |- matches g (PSet ?cs) s res ] =>
        destruct s as [|a s'];
        try destruct (cs a) eqn:?;
        try destruct1;
        eauto using matches
    end.
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

Theorem matches_comp_gas_exists :
  forall g p s res,
  matches g p s res ->
  exists gas,
  matches_comp g p s gas = Some res.
Proof.
  intros * H.
  induction H;
  (* Cases with no recursive calls *)
  try (exists 1; auto; fail);
  (* Cases with charset *)
  try (
    exists 1;
    simpl;
    rewrite_match_subject_in_goal;
    auto;
    fail
  );
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
    specialize (Nat.le_add_l gas2 gas1) as Hle2;
    eauto using matches_comp_gas_some_le
  ).
Qed.
