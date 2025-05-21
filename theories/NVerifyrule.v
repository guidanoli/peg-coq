From Coq Require Import Arith.
From Peg Require Import Syntax.
From Peg Require Import Match.
From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Lia.
From Coq Require Import Classes.EquivDec.

Require Extraction.


Ltac simplsome :=
  repeat match goal with
  | [H: Some ?x = Some ?x |- _] => clear H
  | [H: Some _ = Some _ |- _] => injection H; intros; subst; clear H
  end; try discriminate.


Lemma nth_ndef: forall {T} (l: list T) n a def def',
    nth n l def = a ->
    a <> def ->
    nth n l def' = a.
Proof.
  intros * Heq Hneq.
  erewrite nth_indep; eauto.
  destruct (le_lt_dec (length l) n); trivial.
  eapply nth_overflow with (d := def) in l0.
  congruence.
Qed.


Fixpoint update {T} (l : list T) (idx : nat) (newval : T) : list T :=
  match idx,  l with
  | _, nil => nil
  | 0,  (h :: t) => newval :: t
  | S idx', (h :: t) => h :: update t idx' newval
  end.


Lemma update_eq : forall {T} (l : list T) i a b,
    i < length l -> nth i (update l i a) b = a.
Proof.
  induction l; intros * Hlen.
  - simpl in *. lia.
  - induction i; trivial.
    simpl in *. apply IHl. lia.
Qed.


Lemma update_len: forall {T} (l : list T) idx val,
  length (update l idx val) = length l.
Proof.
  induction l; intros *; destruct idx; simpl; congruence.
Qed.


Lemma update_eq2 : forall {T} (l : list T) i a b,
  nth i (update l i a) b = a \/ nth i (update l i a) b = b.
Proof.
  intros *.
  destruct (le_lt_dec (length l) i).
  - right. apply nth_overflow. rewrite update_len. trivial.
  - left. auto using update_eq.
Qed.


Lemma nth_overflow':
  forall [A : Type] (l : list A) [n : nat] (a d : A),
  nth n l d = a -> a <> d -> n < length l.
Proof.
  intros * Hnth Hneq. destruct (le_lt_dec (length l) n); trivial.
  exfalso; apply Hneq. apply nth_overflow with (d := d) in l0.
  congruence.
Qed.


Lemma update_neq : forall {T} (l : list T) i n a b,
    i <> n -> nth i (update l n a) b = nth i l b.
Proof.
  induction l; intros * Hne.
  - simpl. destruct i; destruct n; simpl; trivial.
  - simpl. destruct i; destruct n; trivial.
    + exfalso. apply Hne. trivial.
    + simpl. apply IHl. lia.
Qed.


Lemma nth_nth_error: forall {T} n (l : list T) def res,
    nth n l def = res ->
    def <> res ->
    nth_error l n = Some res.
Proof.
  intros * Hnt Hneq.
  destruct (le_lt_dec (length l) n).
  - exfalso. eapply nth_overflow with (d := def) in l0. congruence.
  - rewrite nth_error_nth' with (d := def); auto; congruence.
Qed.


Inductive RuleStatus : Type :=
| NotVisited
| Visiting
| Visited : bool -> RuleStatus.


Definition dec_Rule : forall (r1 r2 : RuleStatus), {r1 = r2} + {r1 <> r2}.
Proof. repeat decide equality. Qed.


Definition Result := option (bool * list RuleStatus).


Inductive verifyrule :
  grammar ->
  pat ->
  list RuleStatus ->
  bool ->
  Result ->
  Prop :=
  | VREmpty :
      forall g lr nb,
      verifyrule g PEmpty lr nb (Some (true, lr))
  | VRSet :
      forall g cs lr nb,
      verifyrule g (PSet cs) lr nb (Some (nb, lr))
  | VRSequenceNone :
      forall g p1 p2 lr nb,
      verifyrule g p1 lr false None ->
      verifyrule g (PSequence p1 p2) lr nb None
  | VRSequenceSomeTrue :
      forall g p1 p2 lr lr' nb res,
      verifyrule g p1 lr false (Some (true, lr')) ->
      verifyrule g p2 lr' nb res ->
      verifyrule g (PSequence p1 p2) lr nb res
  | VRSequenceSomeFalse :
      forall g p1 p2 lr nb lr',
      verifyrule g p1 lr false (Some (false, lr')) ->
      verifyrule g (PSequence p1 p2) lr nb (Some (nb, lr'))
  | VRChoiceNone :
      forall g p1 p2 lr nb,
      verifyrule g p1 lr nb None ->
      verifyrule g (PChoice p1 p2) lr nb None
  | VRChoiceSome :
      forall g p1 p2 lr lr' nb nb' res,
      verifyrule g p1 lr nb (Some (nb', lr')) ->
      verifyrule g p2 lr' nb' res ->
      verifyrule g (PChoice p1 p2) lr nb res
  | VRRepetition :
      forall g p lr nb res,
      verifyrule g p lr true res ->
      verifyrule g (PRepetition p) lr nb res
  | VRNot :
      forall g p lr nb res,
      verifyrule g p lr true res ->
      verifyrule g (PNot p) lr nb res
  | VRAnd :
      forall g p lr nb res,
      verifyrule g p lr true res ->
      verifyrule g (PAnd p) lr nb res
  | VRNTVisiting :
      forall g i lr nb,
      nth i lr Visiting = Visiting ->
      verifyrule g (PNT i) lr nb None
  | VRNTNotvisitedSome :
      forall g i p lr nb nb' lr',
      nth i lr Visiting = NotVisited ->
      nth i g PEmpty = p ->
      verifyrule g p (update lr i Visiting) false (Some (nb', lr')) ->
      verifyrule g (PNT i) lr nb (Some (orb nb nb', update lr' i (Visited nb')))
  | VRNTNotvisitedNone :
      forall g i p lr nb,
      nth i lr Visiting = NotVisited ->
      nth i g PEmpty = p ->
      verifyrule g p (update lr i Visiting) false None ->
      verifyrule g (PNT i) lr nb None
  | VRNTVisited :
      forall g i lr nb nb',
      nth i lr Visiting = Visited nb' ->
      verifyrule g (PNT i) lr nb (Some (orb nb nb', lr))
.


Fixpoint count_notvisited (l : list RuleStatus) : nat :=
  match l with
  | nil => 0
  | (NotVisited :: tl) => S (count_notvisited tl)
  | (_ :: tl) => count_notvisited tl
  end.


Lemma countlelen : forall l, count_notvisited l <= length l.
Proof.
  induction l; trivial.
  destruct a; simpl; lia.
Qed.


Lemma updateVisited: forall lr n nb,
  count_notvisited (update lr n (Visited nb)) <= count_notvisited lr.
Proof.
  induction lr; intros *.
  - destruct n; simpl; trivial.
  - destruct n; simpl; try specialize (IHlr n nb);
      destruct a; try lia.
Qed.

Lemma updateVisiting: forall lr n,
  nth n lr Visiting = NotVisited ->
  count_notvisited (update lr n Visiting) < count_notvisited lr.
Proof.
  induction lr; intros *.
  - destruct n; simpl; discriminate.
  - destruct n; simpl.
    + intros H; subst; lia.
    + intros H. specialize (IHlr _ H).
      destruct a; lia.
Qed.


Ltac applyIH :=
  match goal with
  |[HI: context [verifyrule _ ?p _ _ _ -> _],
    HV: verifyrule _ ?p _ _ _ |- _] =>
      eapply HI in HV; clear HI; auto end.


Lemma MapVisited' : forall N g p lr nb nb' lr',
  count_notvisited lr < N ->
  verifyrule g p lr nb (Some (nb', lr')) ->
  count_notvisited lr' <= count_notvisited lr.
Proof.
  induction N.
  - intros * HNV. exfalso. eapply Nat.nlt_0_r. eauto.
  - induction p; intros * HNV HV;
      try (inversion HV; subst; repeat applyIH; lia).
    inversion HV; subst; trivial. clear HV.
    specialize (updateVisiting _ _ H3) as ?.
    specialize (updateVisited lr'0 n nb'0) as ?.
    apply IHN in H7; lia.
Qed.


Corollary MapVisited : forall g p lr nb nb' lr' N,
  count_notvisited lr < N ->
  verifyrule g p lr nb (Some (nb', lr')) ->
  count_notvisited lr' < N.
Proof.
  intros * HNV HV.
  apply (MapVisited' (S (count_notvisited lr))) in HV; lia.
Qed.


Lemma nb_true : forall g p lr nb lr',
    verifyrule g p lr true (Some (nb, lr')) -> nb = true.
Proof.
  induction p; intros * HV; inversion HV; subst; trivial; eauto.
  replace nb' with true in * by (symmetry; eauto).
  eauto.
Qed.


Ltac simplOrb :=
    repeat rewrite Bool.orb_false_r;
    repeat rewrite Bool.orb_true_r;
    repeat rewrite Bool.orb_true_l;
    repeat rewrite Bool.orb_false_l.

Lemma nb_false : forall g p lr nb lr',
    verifyrule g p lr false (Some (nb, lr')) ->
    verifyrule g p lr true (Some (true, lr')).
Proof.
  intros * H.
  remember false as nbF.
  remember (Some (nb, lr')) as res.
  generalize dependent nb.
  generalize dependent lr'.
  induction H; intros * Heq; subst; simplsome;
    try (destruct nb');
    try (replace nb0 with true in * by (symmetry; eauto using nb_true));
    eauto using verifyrule.
  - apply VRNTNotvisitedSome with (nb := true) in H1; trivial.
  - eapply VRNTVisited with (nb := true) in H.
    rewrite Bool.orb_true_l in H. eauto.
Qed.


Lemma nb_nb : forall g p lr nb nb' lr',
    verifyrule g p lr false (Some (nb', lr')) ->
    verifyrule g p lr nb (Some (orb nb' nb, lr')).
Proof.
  intros * H. destruct nb; simplOrb; eauto using nb_false.
Qed.


Lemma VRcomplete : forall N g p lr nb,
  count_notvisited lr < N -> {res : Result | verifyrule g p lr nb res}.
Proof.
  induction N.
  - intros * HNV. exfalso. eapply Nat.nlt_0_r. eauto.
  - induction p; intros * HC;
    try (try (specialize (IHp _ true HC) as [res1  HV1]);
          eexists; eauto using verifyrule; fail).
    + (* Sequence *)
      specialize (IHp1 _ false HC) as [res1  HV1].
      destruct res1;
        try (eexists; eauto using verifyrule; fail).
      destruct p as [b lr']; destruct b;
      try (eexists; eauto using verifyrule; fail).
      (* VRSequenceSomeTrue *)
       assert (HC1 : count_notvisited lr' < S N) by eauto using MapVisited.
       specialize (IHp2 lr' nb HC1) as [res2 HV2].
       eexists. eauto using verifyrule.
    + (* Choice *)
      specialize (IHp1 _ nb HC) as [res1  HV1].
      destruct res1;
        try (eexists; eauto using verifyrule; fail).
      (* VRChoiceSome *)
      destruct p as [nb' lr'].
       assert (HC1 : count_notvisited lr' < S N) by eauto using MapVisited.
      specialize (IHp2 lr' nb' HC1) as [res2  HV2].
      eexists; eauto using verifyrule.
    + (* Non Terminal *)
      destruct (nth n lr Visiting) eqn:Hne;
         try (eexists; eauto using verifyrule; fail).
       specialize (updateVisiting _ _ Hne) as ?.
       assert (count_notvisited (update lr n Visiting) < N) as HN
         by lia.
      specialize (IHN g (nth n g PEmpty) (update lr n Visiting) false HN)
          as [res ?].
      destruct res as [[? ?] | ]; eexists; eauto using verifyrule.
Defined.

Definition WF (g : grammar) : Result.
  specialize (VRcomplete (S (length g))
                         g
                         (PNT 0)
                         (repeat NotVisited (length g))
                         false) as H.
  assert (Hlt : count_notvisited (repeat NotVisited (length g)) < S (length g)).
  { specialize (countlelen (repeat NotVisited (length g))) as HC.
    rewrite repeat_length in HC. lia. }
  apply H in Hlt.
  destruct Hlt as [? ?].
  exact x.
Defined.

Definition A : (Ascii.ascii -> bool) := fun c => false.

Goal WF [PNT 0] = None. reflexivity. Qed.
Goal WF [PSequence (PSet A) (PNT 0)] = Some (false, [Visited false]).
  reflexivity. Qed.
Goal WF [PNT 1; PNT 0] = None. reflexivity. Qed.

(* Extraction VRcomplete. *)


Ltac breakH :=
    match goal with
    |[H1 : forall _, verifyrule _ ?p ?lr ?br _ -> _,
      H2 : verifyrule _ ?p ?lr ?br _ |- _
     ] => apply H1 in H2;
            try (injection H2; intros; subst); try discriminate
    end.


Lemma verifyrule_unique : forall g p lr nb res res',
    verifyrule g p lr nb res ->
    verifyrule g p lr nb res' ->
    res = res'.
Proof.
  intros * H1.
  generalize dependent res'.
  induction H1; intros * H2;
    try (inversion H2; subst; trivial; repeat f_equal;
         repeat breakH; trivial; try congruence).
Qed.


Fixpoint verifyrule_comp gas
    (g : grammar) (p : pat) (lr : list RuleStatus) (nb : bool) :
      option Result :=
  match gas with
  | 0 => None
  | S gas' =>
    match p with
    | PEmpty => Some (Some (true, lr))
    | PSet _ => Some (Some (nb, lr))
    | PSequence p1 p2 =>
      match verifyrule_comp gas' g p1 lr false with
      | None => None  (* out of gas *)
      | Some None => Some None  (* ill formed *)
      | Some (Some (false, lr')) => Some (Some (nb, lr'))
      | Some (Some (true, lr')) => verifyrule_comp gas' g p2 lr' nb
      end
    | PChoice p1 p2 =>
      match verifyrule_comp gas' g p1 lr nb with
      | None => None  (* out of gas *)
      | Some None => Some None  (* ill formed *)
      | Some (Some (nb', lr')) => verifyrule_comp gas' g p2 lr' nb'
      end
    | PRepetition p' => verifyrule_comp gas' g p' lr true
    | PNot p' => verifyrule_comp gas' g p' lr true
    | PAnd p' => verifyrule_comp gas' g p' lr true
    | PNT i =>
      match nth i lr Visiting with
      | Visiting => Some (None)  (* ill formed *)
      | Visited nb' => Some (Some (orb nb nb', lr))
      | NotVisited =>
        match verifyrule_comp gas' g (nth i g PEmpty)
                              (update lr i Visiting) false with
        | None => None  (* out of gas *)
        | Some None => Some None  (* ill formed *)
        | Some (Some (nb', lr')) =>
            Some (Some (orb nb nb', update lr' i (Visited nb')))
        end
      end
    end
  end.


Ltac destVR :=
  match goal with
  | [H: context [verifyrule_comp ?gas ?g ?p1 ?lr ?nb] |- _]
        => destruct (verifyrule_comp gas g p1 lr nb) as [[[? ?] | ] | ] eqn:Heq
  | [|- context [verifyrule_comp ?gas ?g ?p1 ?lr ?nb]]
        => destruct (verifyrule_comp gas g p1 lr nb) as [[[? ?] | ] | ] eqn:Heq
  end.


Lemma verifyrule_comp_sound : forall gas g p lr nb res,
  verifyrule_comp gas g p lr nb = Some res ->
  verifyrule g p lr nb res.
Proof with eauto using verifyrule.
  induction gas; intros * H; try discriminate.
  destruct p; simpl in H;
    try (injection H; intros; subst);
      try discriminate...
  - destVR; try discriminate; simplsome...
    destruct b; simplsome...
  - destVR; simplsome...
  - destruct (nth n lr Visiting) eqn:?; simplsome...
    destVR; simplsome...
Qed.


Ltac breakEx :=
  repeat match goal with
  [H: exists _, _ |- _] => destruct H as [? ?]
  end.

Lemma verifyrule_comp_gas_exists : forall g p lr nb res,
    verifyrule g p lr nb res ->
    exists gas,
      forall gas', gas < gas' -> verifyrule_comp gas' g p lr nb = Some res.
Proof.
  induction 1; intros *;
    try (exists 0; destruct gas'; try lia; trivial; fail);
    try (breakEx; exists (S x); intros * Hlt;
    destruct gas'; try lia; simpl;
    apply H0; lia; fail).
  - breakEx. exists (S x). intros * Hlt.
    destruct gas'. try lia. simpl.
    rewrite H0; trivial; lia.
  - breakEx. exists (S (x + x0)).
    destruct gas'; try lia. simpl.
    intros Hlt. rewrite H2; try lia; rewrite H1; trivial; lia.
  - breakEx. exists (S x).
    intros * Htl.
    destruct gas'; try lia. simpl.
    rewrite H0; trivial; try lia.
  - breakEx. exists (S x).
    destruct gas'; try lia; simpl.
    intros ?. rewrite H0; trivial; try lia.
  - breakEx. exists (S (x + x0)).
    destruct gas'; try lia; simpl.
    intros ?. rewrite H2; try lia.
    apply H1; lia.
  - exists 1. intros gas' Hlt.
    destruct gas'; try lia; simpl.
    rewrite H; trivial.
  - breakEx. exists (S x). intros gas' Hlt.
    destruct gas'; try lia; simpl.
    rewrite H. subst.
    rewrite H2; trivial; lia.
  - breakEx. exists (S x). subst.
    intros gas' Hlt.
    destruct gas'; try lia; simpl.
    rewrite H.
    rewrite H2; trivial; try lia.
  - exists 1; intros gas' Hlt.
    destruct gas'; try lia; simpl.
    rewrite H. trivial.
Qed.


Fixpoint costP p : nat :=
  match p with
  | PEmpty => 1
  | PSet _ => 1
  | PSequence p1 p2 => S (costP p1 + costP p2)
  | PChoice p1 p2 => S (costP p1 + costP p2)
  | PRepetition p => S (costP p)
  | PNot p => S (costP p)
  | PAnd p => S (costP p)
  | PNT _ => 1
  end.


Lemma costP1 : forall p, 0 < costP p.
Proof. induction p; simpl; lia. Qed.


Fixpoint costG g lr : nat :=
  match lr with
  | nil => 0
  | NotVisited :: lr' =>
      match g with
      | nil => S (1 + costG nil lr')
      | (p :: g') => S (costP p + costG g' lr')
      end
  | _ :: lr' =>
      match g with
      | nil => costG nil lr'
      | (_ :: g') => costG g' lr'
      end
  end.


Lemma CostUpdateVIsitingP : forall lr g n,
    nth n lr Visiting = NotVisited ->
    costP (nth n g PEmpty) + costG g (update lr n Visiting) <= costG g lr.
Proof.
  induction lr; intros * Hn.
  - simpl in Hn. destruct n; discriminate.
  - simpl. destruct n; destruct a; destruct g; simpl; try lia;
     try discriminate; simpl in Hn;
     try (apply IHlr with (g := g) in Hn; simpl in Hn; lia);
     try (apply IHlr with (g := nil) in Hn; destruct n; simpl in Hn; lia).
Qed.


Lemma costUpdateVisited : forall lr g i nb,
  costG g (update lr i (Visited nb)) <= costG g lr.
Proof.
  induction lr; intros *.
  - simpl. destruct i; trivial.
  - destruct g.
    + simpl. destruct i; simpl.
      * simpl. destruct a; lia.
      * simpl. destruct a; specialize (IHlr nil i nb) as ?; lia.
    + simpl. destruct i; simpl; destruct a; try lia;
      specialize (IHlr g i nb) as ?; lia.
Qed.


Lemma costUpdateVisiting : forall lr g i,
  costG g (update lr i Visiting) <= costG g lr.
Proof.
  induction lr; intros *.
  - simpl. destruct i; trivial.
  - destruct g.
    + simpl. destruct i; simpl.
      * simpl. destruct a; lia.
      * simpl. destruct a; specialize (IHlr nil i) as ?; lia.
    + simpl. destruct i; simpl; destruct a; try lia;
      specialize (IHlr g i) as ?; lia.
Qed.


Lemma sameLen : forall g p lr lr' nb nb',
    verifyrule g p lr nb (Some (nb', lr')) ->
    length lr = length lr'.
Proof.
  intros * HVR.
  remember (Some (nb', lr')) as res.
  generalize dependent nb'.
  generalize dependent lr'.
  induction HVR; intros * Heq;
  try (injection Heq; intros; subst; clear Heq);
    subst; try discriminate; eauto;
    repeat match goal with
    [H: forall _ _, _ = _ -> _ |- _] =>
      specialize (H _ _ eq_refl)
    end; try congruence.
  rewrite update_len in IHHVR.
  rewrite update_len.
  trivial.
Qed.


Lemma dimCost : forall gas g p lr lr' nb nb',
    verifyrule_comp gas g p lr nb = Some (Some (nb', lr')) ->
    costG g lr' <= costG g lr.
Proof.
  induction gas; intros * HVr; try discriminate.
  destruct p; simpl in HVr; simplsome; trivial;
    repeat match goal with
    [H : verifyrule_comp _ _ _ _ _ = Some _ |- _] =>
       eapply IHgas in H
    end; try lia.
  - destVR; try congruence.
    destruct b.
    + eapply IHgas in Heq.
      eapply IHgas in HVr.
      lia.
    + simplsome.
      eapply IHgas in Heq.
      trivial.
  - destVR; try congruence.
    eapply IHgas in Heq.
    eapply IHgas in HVr.
    lia.
  - destruct (nth n lr Visiting); try congruence.
    + destVR; try congruence.
      simplsome.
      apply IHgas in Heq; clear IHgas.
      specialize (costUpdateVisited l g n b) as ?.
      specialize (costUpdateVisiting lr g n) as ?.
      lia.
    + simplsome. trivial.
Qed.


Lemma VR_comp : forall gas g p lr nb,
    (costG g lr + costP p) <= gas ->
    verifyrule_comp gas g p lr nb <> None.
Proof.
  induction gas; intros * Hle.
  - specialize (costP1 p). lia.
  - destruct p.
    + simpl. congruence.
    + simpl. congruence.
    + simpl in Hle; simpl.
      destVR; try congruence.
      destruct b; try congruence.
      * eapply IHgas.
        eapply dimCost in Heq. lia.
      * exfalso. eapply IHgas; eauto. lia.
    + simpl in Hle; simpl.
      destVR; try congruence.
      * eapply IHgas.
        apply dimCost in Heq. lia.
      * exfalso. eapply IHgas; eauto. lia.
    + apply IHgas. simpl in Hle. lia.
    + apply IHgas. simpl in Hle. lia.
    + apply IHgas. simpl in Hle. lia.
    + simpl in Hle; simpl.
      destruct (nth n lr Visiting) eqn:?; try congruence.
      destVR; try congruence.
      exfalso.
      eapply IHgas; eauto.
      specialize (CostUpdateVIsitingP lr g n Heqr) as ?.
      lia.
Qed.


Lemma VRVR : forall g p lr nb res,
  verifyrule_comp (S (costG g lr + costP p)) g p lr nb = Some res <->
  verifyrule g p lr nb res.
Proof.
  intros *; split; intro H.
  - eauto using verifyrule_comp_sound.
  - assert (H1 : costG g lr + costP p <= S (costG g lr + costP p)) by lia.
    specialize (VR_comp (S (costG g lr + costP p)) g p lr nb H1) as H2.
    destruct (verifyrule_comp (S (costG g lr + costP p)) g p lr nb) eqn:?.
    + apply verifyrule_comp_sound in Heqo.
      f_equal. eauto using verifyrule_unique.
    + exfalso. apply H2. trivial.
Qed.


Definition not_nullable g p := forall s, ~matches g p s (Success s).


Lemma match_len : forall g p,
  forall s s', matches g p s (Success s') -> String.length s' <= String.length s.
Proof.
  intros * Hm. eauto using Suffix.suffix_length_le, matches_suffix. Qed.


Lemma notnull_len : forall g p,
  not_nullable g p <->
  forall s s', matches g p s (Success s') -> String.length s' < String.length s.
Proof.
  intros *; split; intros H.
  - intros * Hm.
    specialize (matches_suffix _ _ _ _  Hm) as HL.
    specialize (Suffix.suffix_length_le _ _ HL) as HS.
    apply Lt.le_lt_or_eq_stt in HS.
    destruct HS; trivial.
    exfalso.
    replace s with s' in * by eauto using Suffix.suffix_length_eq.
    eapply H. eauto.
  - intros s HM.
    apply H in HM. lia.
Qed.


Definition stateCorrect g lr :=
  forall n, nth n lr NotVisited = Visited false ->
            not_nullable g (PNT n).


Lemma stcorrupdate : forall g lr i,
    stateCorrect g lr -> stateCorrect g (update lr i Visiting).
Proof.
  unfold stateCorrect.
  intros * H n Hn.
  destruct (Nat.eq_dec n i); subst; apply H.
  - destruct (update_eq2 lr i Visiting NotVisited); congruence.
  - rewrite update_neq in Hn; trivial.
Qed.


Lemma not_null_set : forall g set, not_nullable g (PSet set).
Proof.
  intros *.
  apply notnull_len.
  inversion 1; subst. simpl. lia.
Qed.


Lemma not_null_seq1 : forall g p1 p2,
  not_nullable g p1 -> not_nullable g (PSequence p1 p2).
Proof.
  intros * H.
  inversion 1; subst.
  apply match_len in H7; eauto.
  apply notnull_len in H4; eauto.
  lia.
Qed.


Lemma not_null_seq2 : forall g p1 p2,
  not_nullable g p2 -> not_nullable g (PSequence p1 p2).
Proof.
  intros * H.
  inversion 1; subst.
  apply match_len in H4; eauto.
  apply notnull_len in H7; eauto.
  lia.
Qed.


Lemma not_null_choice : forall g p1 p2,
  not_nullable g p1 ->
  not_nullable g p2 ->
  not_nullable g (PChoice p1 p2).
Proof.
  intros * H1 H2.
  inversion 1; subst.
  - apply H1 in H6. trivial.
  - apply H2 in H8. trivial.
Qed.


Ltac ff :=
  repeat match goal with
  [H: false = false -> _ |- _] => specialize (H eq_refl)
  end.

Ltac appHI :=
match goal with
    [IH: stateCorrect ?g ?lr -> _,
     H: stateCorrect ?g ?lr |- _] =>
          eapply IH in H; eauto;
          destruct H as [[? | ?] ?]; clear IH
    end.

(* 'verifyrule' only "increases" rules status: It can only change
   rules not-yet visited. *)
Lemma vrinc: forall g p nb nb' lr lr' n stat,
  verifyrule g p lr nb (Some (nb', lr')) ->
  nth n lr NotVisited = stat ->
  stat <> NotVisited ->
  nth n lr' NotVisited = stat.
Proof.
  intros * HVR.
  remember (Some (nb', lr')) as res.
  generalize dependent nb'.
  generalize dependent lr'.
  generalize dependent n.
  induction HVR; intros * Heq Hnt Hneq; try discriminate; subst;
  try (injection Heq; intros; subst); eauto.
  destruct (Nat.eq_dec n i); subst.
  - exfalso. eapply nth_ndef in H; eauto; discriminate.
  - clear Heq.
    eapply IHHVR in Hneq; clear IHHVR; trivial.
    + rewrite <- Hneq.
      eauto using update_neq.
    + eapply update_neq; trivial.
Qed.


Lemma nullableVR: forall g p nb nb' lr lr',
  verifyrule g p lr nb (Some (nb', lr')) ->
  stateCorrect g lr ->
  (nb' = true \/ not_nullable g p) /\ stateCorrect g lr'.
Proof.
  intros * HV HSC.
  remember (Some (nb', lr')) as res.
  generalize dependent nb'.
  generalize dependent lr'.
  induction HV; intros * HS; subst; simplsome; ff;
    repeat appHI; subst; try discriminate;
    intuition (eauto using not_null_set, not_null_seq2, not_null_seq1,
      nb_true, not_null_choice).
  - apply stcorrupdate with (i := i) in HSC.
    appHI; subst.
    + left. simpl. simplOrb. trivial.
    + right. unfold not_nullable in *.
      intros s Hm. inversion Hm; subst; clear Hm.
      eapply nth_error_nth in H3.
      rewrite H3 in H0.
      eapply H0. eauto.
  - apply stcorrupdate with (i := i) in HSC.
    appHI; subst.
    * unfold stateCorrect in *; intros n H2.
      destruct (Nat.eq_dec n i); subst.
      + destruct (update_eq2 lr' i (Visited true) NotVisited); congruence.
      + eapply H1.
        rewrite update_neq in H2; auto.
    * unfold stateCorrect in *; intros n H2.
      destruct (Nat.eq_dec n i); subst.
      + destruct (update_eq2 lr' i (Visited nb') NotVisited);
          try congruence.
        replace nb' with false in * by congruence.
        unfold not_nullable in *; intros s HM.
        inversion HM; subst. eapply H0.
        erewrite nth_error_nth; eauto.
      + apply H1; clear H1.
        rewrite update_neq in H2; auto.
  - destruct nb'.
      + left. simplOrb. trivial.
      + right. apply HSC.
        eapply nth_ndef; eauto; discriminate.
Qed.


Definition stateComplete g lr :=
  forall n nb, nth n lr NotVisited = Visited nb ->
     exists nb' lr', verifyrule g (PNT n) lr false (Some (nb', lr')).


Lemma SCVR: forall g p nb nb' lr lr',
  verifyrule g p lr nb (Some (nb', lr')) ->
  stateComplete g lr ->
  stateComplete g lr'.
Proof.
  intros * HVR HSC.
  remember (Some (nb', lr')) as res.
  generalize dependent nb'.
  generalize dependent lr'.
  induction HVR; intros * Heq;
  try (injection Heq; intros; subst; clear Heq);
  try discriminate; eauto.
  assert (stateComplete g (update lr i Visiting)).
  { clear IHHVR. unfold stateComplete in *.
    intros * H1.
    destruct (Nat.eq_dec i n); subst.
    - exfalso. erewrite update_eq in H1; try discriminate.
      eapply nth_overflow'; eauto; congruence.
    - eexists. eexists.
      eapply VRNTVisited.
      rewrite update_neq; try congruence.
      rewrite update_neq in H1; try congruence.
      eapply nth_ndef in H1; eauto; congruence. }
  eapply IHHVR in H0. 2: eauto.
  unfold stateComplete; intros * H1.
  assert (Hleq: length lr' = length lr).
  { eapply sameLen in HVR.
    rewrite update_len in HVR.
    congruence. }
  assert (i < length lr').
  { rewrite Hleq.
    eapply nth_overflow'; eauto; congruence. }
  destruct (Nat.eq_dec i n); subst.
  - rewrite update_eq in H1; trivial.
    injection H1; intros; subst; clear H1.
    eexists; eexists. eapply VRNTVisited.
    rewrite update_eq; trivial.
  - eexists; eexists. eapply VRNTVisited.
    rewrite update_neq; try congruence.
    rewrite update_neq in H1; try congruence.
    replace (nth n lr' Visiting) with (nth n lr' NotVisited); eauto.
    rewrite H1; symmetry.
    eapply nth_ndef; eauto; congruence.
Qed.



(*
Lemma stcompupdate : forall g lr i,
    stateComplete g lr -> stateComplete g (update lr i Visiting).
Proof.
  intros * H.
  unfold stateComplete in *.
  intros * Heq.
  destruct (Nat.eq_dec n i); subst.
  - destruct (update_eq2 lr i Visiting NotVisited); congruence.
  - rewrite update_neq in Heq.
    apply H in Heq.
    simpl.
Qed.


Lemma not_null_set : forall g set, not_nullable g (PSet set).
Proof.
  intros *.
  apply notnull_len.
  inversion 1; subst. simpl. lia.
Qed.


Lemma not_null_seq1 : forall g p1 p2,
  not_nullable g p1 -> not_nullable g (PSequence p1 p2).
Proof.
  intros * H.
  inversion 1; subst.
  apply match_len in H7; eauto.
  apply notnull_len in H4; eauto.
  lia.
Qed.


Lemma not_null_seq2 : forall g p1 p2,
  not_nullable g p2 -> not_nullable g (PSequence p1 p2).
Proof.
  intros * H.
  inversion 1; subst.
  apply match_len in H4; eauto.
  apply notnull_len in H7; eauto.
  lia.
Qed.


Lemma not_null_choice : forall g p1 p2,
  not_nullable g p1 ->
  not_nullable g p2 ->
  not_nullable g (PChoice p1 p2).
Proof.
  intros * H1 H2.
  inversion 1; subst.
  - apply H1 in H6. trivial.
  - apply H2 in H8. trivial.
Qed.


Ltac ff :=
  repeat match goal with
  [H: false = false -> _ |- _] => specialize (H eq_refl)
  end.

Ltac appHI :=
match goal with
    [IH: stateCorrect ?g ?lr -> _,
     H: stateCorrect ?g ?lr |- _] =>
          eapply IH in H; eauto;
          destruct H as [[? | ?] ?]; clear IH
    end.

(* 'verifyrule' only "increases" rules status: It can only change
   rules not-yet visited. *)
Lemma vrinc: forall g p nb nb' lr lr' n stat,
  verifyrule g p lr nb (Some (nb', lr')) ->
  nth n lr NotVisited = stat ->
  stat <> NotVisited ->
  nth n lr' NotVisited = stat.
Proof.
  intros * HVR.
  remember (Some (nb', lr')) as res.
  generalize dependent nb'.
  generalize dependent lr'.
  generalize dependent n.
  induction HVR; intros * Heq Hnt Hneq; try discriminate; subst;
  try (injection Heq; intros; subst); eauto.
  destruct (Nat.eq_dec n i); subst.
  - exfalso. eapply nth_ndef in H; eauto; discriminate.
  - clear Heq.
    eapply IHHVR in Hneq; clear IHHVR; trivial.
    + rewrite <- Hneq.
      eauto using update_neq.
    + eapply update_neq; trivial.
Qed.


Lemma nullableVR: forall g p nb nb' lr lr',
  verifyrule g p lr nb (Some (nb', lr')) ->
  stateCorrect g lr ->
  (nb' = true \/ not_nullable g p) /\ stateCorrect g lr'.
Proof.
  intros * HV HSC.
  remember (Some (nb', lr')) as res.
  generalize dependent nb'.
  generalize dependent lr'.
  induction HV; intros * HS; subst; simplsome; ff;
    repeat appHI; subst; try discriminate;
    intuition (eauto using not_null_set, not_null_seq2, not_null_seq1,
      nb_true, not_null_choice).
  - apply stcorrupdate with (i := i) in HSC.
    appHI; subst.
    + left. simpl. simplOrb. trivial.
    + right. unfold not_nullable in *.
      intros s Hm. inversion Hm; subst; clear Hm.
      eapply nth_error_nth in H3.
      rewrite H3 in H0.
      eapply H0. eauto.
  - apply stcorrupdate with (i := i) in HSC.
    appHI; subst.
    * unfold stateCorrect in *; intros n H2.
      destruct (Nat.eq_dec n i); subst.
      + destruct (update_eq2 lr' i (Visited true) NotVisited); congruence.
      + eapply H1.
        rewrite update_neq in H2; auto.
    * unfold stateCorrect in *; intros n H2.
      destruct (Nat.eq_dec n i); subst.
      + destruct (update_eq2 lr' i (Visited nb') NotVisited);
          try congruence.
        replace nb' with false in * by congruence.
        unfold not_nullable in *; intros s HM.
        inversion HM; subst. eapply H0.
        erewrite nth_error_nth; eauto.
      + apply H1; clear H1.
        rewrite update_neq in H2; auto.
  - destruct nb'.
      + left. simplOrb. trivial.
      + right. apply HSC.
        eapply nth_ndef; eauto; discriminate.
Qed.

*)
