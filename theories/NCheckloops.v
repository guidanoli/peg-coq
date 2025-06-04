From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Arith.
From Peg Require Import Syntax.

From Peg Require Import Syntax.
From Peg Require Import NMatch.
From Peg Require Import Nullable.
From Peg Require Import Tactics.
From Peg Require Import NVerifyrule.
From Peg Require Import NVerifygrammar.

Import ListNotations.


Fixpoint nullable_comp lr p :=
  match p with
  | PEmpty => true
  | PSet _ => false
  | PSequence p1 p2 =>
      if nullable_comp lr p1 then
        nullable_comp lr p2
      else false
  | PChoice p1 p2 =>
      if nullable_comp lr p1 then
        true
      else
        nullable_comp lr p2
  | PRepetition _ => true
  | PNot _ => true
  | PAnd _ => true
  | PNT i => match nth i lr Visiting with
             | Visited false => false
             | _ => true
             end
  end.


Ltac destructCond :=
  match goal with
  [H: (match ?cond with | _ => _ end)  = _ |- _] =>
    destruct cond eqn:?; try discriminate
end.


Lemma nullable_comp_correct : forall g lr p,
    VG g = Some lr ->
    nullable_comp lr p = false ->
    not_nullable g p.
Proof.
  induction p; intros HVG HNull; try discriminate;
  simpl in HNull;
  repeat destructCond;
      eauto using not_null_set, not_null_seq2, not_null_seq1,
        nb_true, not_null_choice, VGcorrect_nonull.
Qed.


(** CheckLoops predicate **)
(** Check whether a pattern has potential infinite loops **)

Inductive noloops : list RuleStatus -> pat -> Prop :=
  | CLEmpty : forall lr, noloops lr PEmpty
  | CLSet : forall lr cs, noloops lr (PSet cs)
  | CLSequence : forall lr p1 p2,
      noloops lr p1 ->
      noloops lr p2 ->
      noloops lr (PSequence p1 p2)
  | CLChoice : forall lr p1 p2,
      noloops lr p1 ->
      noloops lr p2 ->
      noloops lr (PChoice p1 p2)
  | CLRepetition : forall lr p,
      nullable_comp lr p = false ->
      noloops lr p ->
      noloops lr (PRepetition p)
  | CLNot : forall lr p,
      noloops lr p ->
      noloops lr (PNot p)
  | CLAnd : forall lr p,
      noloops lr p ->
      noloops lr (PAnd p)
  | CLNT : forall lr i,
      noloops lr (PNT i)
  .


(** CheckLoops function **)

Fixpoint noloops_comp lr p :=
  match p with
  | PEmpty => true
  | PSet _ => true
  | PSequence p1 p2 =>
      (noloops_comp lr p1 && noloops_comp lr p2)%bool
  | PChoice p1 p2 =>
      (noloops_comp lr p1 && noloops_comp lr p2)%bool
  | PRepetition p' =>
      if nullable_comp lr p' then false
      else noloops_comp lr p'
  | PNot p' => noloops_comp lr p'
  | PAnd p' => noloops_comp lr p'
  | PNT _ => true
end.


Lemma noloops_comp_necessary :
  forall lr p,
  noloops lr p ->
  noloops_comp lr p = true.
Proof.
  induction 1; trivial; simpl;
    specialize (Bool.andb_true_l true); try congruence.
  rewrite H. trivial.
Qed.


Lemma noloops_comp_sufficient :
  forall lr p,
  noloops_comp lr p = true ->
  noloops lr p.
Proof.
  induction p; intros Hnl; simpl in Hnl;
    try apply andb_prop in Hnl; intuition (auto using noloops).
  destructCond.
  auto using noloops.
Qed.


Fixpoint Gnoloops_comp n lr g : bool :=
  match n with
  | 0 => true
  | S n' => match Gnoloops_comp n' lr g with
            | false => false
            | true => noloops_comp lr (nth n' g PEmpty)
            end
  end.


Lemma Gnoloops_comp_complete_aux : forall n lr g,
  Gnoloops_comp n lr g = true ->
  forall i, i < n -> noloops lr (nth i g PEmpty).
Proof.
  induction n; intros * HGnl i Hlt; try lia.
  simpl in HGnl.
  destructCond.
  assert (Hlt1: i <= n) by lia. clear Hlt.
  specialize (Lt.le_lt_or_eq_stt _ _ Hlt1) as [? | ?]; subst;
    auto using noloops_comp_sufficient.
Qed.

  
Lemma Gnoloops_comp_complete : forall lr g,
  Gnoloops_comp (length g) lr g = true ->
  forall n, noloops lr (nth n g PEmpty).
Proof.
  intros * H n.
  specialize (Gnoloops_comp_complete_aux _ _ _ H) as ?.
  specialize (Nat.lt_ge_cases n (length g)) as [? | ?]; auto.
  apply nth_overflow with (d := PEmpty) in H1.
  rewrite H1. auto using noloops.
Qed.


Definition well_formed (g : grammar) : option (list RuleStatus) :=
  match VG g with
  | Some lr => 
      if Gnoloops_comp (length g) lr g then Some lr
      else None
  | None => None
end.


Module Examples.
(* R0 -> R0 *)

Goal well_formed [PNT 0] = None. reflexivity. Qed.

Definition dot : pat := PSet (fun c => true).

(* R0 -> R1 R1; R1 -> ε / . *)
Goal well_formed [PSequence (PNT 1) (PNT 1); PChoice PEmpty dot] =
     Some [Visited true; Visited true]. reflexivity. Qed.

(* R0 -> . R0 / . *)
Goal well_formed [PChoice (PSequence dot (PNT 0)) dot] =
       Some [Visited false]. reflexivity. Qed.

(* R0 -> !. / &. . R0 *)
Goal well_formed [PChoice (PNot dot)
                          (PSequence (PAnd dot)
                          (PSequence dot (PNT 0)))] = Some [Visited true].
reflexivity. Qed.


(* R0 -> ( .* )*  *)
Goal well_formed [PRepetition (PRepetition dot)] = None.
reflexivity. Qed.


(* R0 -> ( .* . )*  *)
Goal well_formed [PRepetition (PSequence (PRepetition dot) dot)] =
      Some [Visited true]. reflexivity. Qed.

End Examples.



Lemma well_formed_correct_aux : forall g lr,
  well_formed g  = Some lr ->
  forall N s p,
  String.length s < N ->
  noloops lr p ->
  exists res, matches g p s res.
Proof with eauto using matches.
  intros * HWF.
  unfold well_formed in HWF.
  repeat destructCond.
  injection HWF; intro; subst; clear HWF.
  specialize (Gnoloops_comp_complete _ _ Heqb) as ?.
  induction N; intros * Hlen; simpl in Hlen; try lia.
  generalize dependent s.
  specialize (VGcomplete _ _ p Heqo) as ?.
  breakEx.
  induction H0; intros * HSlen HNL; inversion HNL; subst...
  - destruct s...
    destruct (cs a) eqn:?...
  - specialize (IHnoleftrec1 Heqb Heqo H IHN _ HSlen H3).
    breakEx.
    destruct x...
    specialize (match_len _ _ _ _ H0) as ?.
    assert (HLen: String.length s0 < S N) by lia.
    specialize (IHnoleftrec2 Heqb Heqo H IHN _ HLen H4).
    breakEx...
  - specialize (IHnoleftrec Heqb Heqo H IHN _ HSlen H4).
    breakEx.
    destruct x...
    assert (String.length s0 < N) as Hlen0.
    { eapply NLR.nlr_nullable in H0.
      eapply (proj1 (notnull_len g p1)) in H1; eauto; try lia. }
    specialize (IHN s0 p2 Hlen0 H5).
    breakEx...
  - specialize (IHnoleftrec1 Heqb Heqo H IHN _ HSlen H3).
    breakEx.
    destruct x...
    specialize (IHnoleftrec2 Heqb Heqo H IHN _ HSlen H4).
    breakEx...
  - specialize (IHnoleftrec Heqb Heqo H IHN _ HSlen H4).
    breakEx.
    destruct x...
    assert (String.length s0 < N) as Hlen0.
    { Search (nullable_comp _ _ = false).
      eapply nullable_comp_correct in H2; eauto.
      eapply (proj1 (notnull_len g p)) in H2; eauto; try lia. }
    specialize (IHN s0 _ Hlen0 HNL).
    breakEx...
  - specialize (IHnoleftrec Heqb Heqo H IHN _ HSlen H3).
    breakEx.
    destruct x...
  - specialize (IHnoleftrec Heqb Heqo H IHN _ HSlen H3).
    breakEx.
    destruct x...
  - assert (HNLnth: noloops lr (nth i g PEmpty)) by eauto.
    specialize (IHnoleftrec Heqb Heqo H IHN _ HSlen HNLnth).
    breakEx...
Qed.


Corollary well_formed_correct : forall g lr,
  well_formed g  = Some lr ->
  forall s,
    exists res, matches g (nth 0 g PEmpty) s res.
Proof.
  intros * HWF s.
  eapply well_formed_correct_aux; eauto.
  unfold well_formed in HWF.
  repeat destructCond.
  injection HWF; intro; subst; clear HWF.
  eauto using Gnoloops_comp_complete.
Qed.


  

