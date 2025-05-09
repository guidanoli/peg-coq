From Coq Require Import Arith.
From Peg Require Import Syntax.
From Peg Require Import Match.
From Coq Require Import Lists.List.
From Coq Require Import Lia.


Fixpoint update {T} (l : list T) (idx : nat) (newval : T) : list T :=
  match idx,  l with
  | _, nil => nil
  | 0,  (h :: t) => newval :: t
  | S idx', (h :: t) => h :: update t idx' newval
  end.


Lemma update_len: forall {T} (l : list T) idx val,
  length (update l idx val) = length l.
Proof.
  induction l; intros *; destruct idx; simpl; congruence.
Qed.


Lemma nth_update: forall {T} (l : list T) idx val,
  idx < length l -> nth_error (update l idx val) idx = Some val.
Proof.
  induction l; intros * H.
  - simpl in H. exfalso. eapply Nat.nlt_0_r. eauto.
  - simpl. destruct idx; trivial.
    simpl in *. apply IHl. lia.
Qed.


Inductive RuleStatus : Type :=
| NotVisited
| Visiting
| Visited : bool -> RuleStatus.


Inductive verifyrule :
  grammar ->
  pat ->
  list RuleStatus ->
  bool ->
  option (bool * list RuleStatus) ->
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
      nth_error lr i = Some NotVisited ->
      nth i g PEmpty = p ->
      verifyrule g p (update lr i Visiting) false (Some (nb', lr')) ->
      verifyrule g (PNT i) lr nb (Some (orb nb nb', update lr i (Visited nb')))
  | VRNTNotvisitedNone :
      forall g i p lr nb,
      nth_error lr i = Some NotVisited ->
      nth i g PEmpty = p ->
      verifyrule g p (update lr i Visiting) false None ->
      verifyrule g (PNT i) lr nb None
  | VRNTVisited :
      forall g i lr nb nb',
      nth_error lr i = Some (Visited nb') ->
      verifyrule g (PNT i) lr nb (Some (orb nb nb', lr))
.


Fixpoint count_notvisited (l : list RuleStatus) : nat :=
  match l with
  | nil => 0
  | (NotVisited :: tl) => S (count_notvisited tl)
  | (_ :: tl) => count_notvisited tl
  end.


Lemma updateVisited: forall lr n nb,
  count_notvisited (update lr n (Visited nb)) <= count_notvisited lr.
Proof.
  induction lr; intros *.
  - destruct n; simpl; trivial.
  - destruct n; simpl; try specialize (IHlr n nb);
      destruct a; try lia.
Qed.

Lemma updateVisiting: forall lr n,
  nth_error lr n = Some NotVisited ->
  count_notvisited (update lr n Visiting) < count_notvisited lr.
Proof.
  induction lr; intros *.
  - destruct n; simpl; discriminate.
  - destruct n; simpl.
    + intros H; injection H as Ha; subst; lia.
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
    inversion HV; subst; auto using updateVisited.
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
    verifyrule g p lr true (Some (nb, lr')) -> true = nb.
Proof.
  induction p; intros * HV; inversion HV; subst; trivial; eauto.
  replace nb' with true in * by eauto.
  eauto.
Qed.


Ltac simplOrb := 
    repeat rewrite Bool.orb_false_r;
    repeat rewrite Bool.orb_true_r;
    repeat rewrite Bool.orb_true_l;
    repeat rewrite Bool.orb_false_l.

Lemma nb_false : forall g p lr nb nb' lr',
    verifyrule g p lr false (Some (nb', lr')) ->
    verifyrule g p lr nb (Some (orb nb nb', lr')).
Proof.
  induction p; intros * HV; inversion HV; subst; simpl;
  simplOrb;
  eauto using verifyrule.
  - rewrite Bool.orb_comm. simpl.
    eapply VRChoiceSome.
    + clear IHp2.
      eapply IHp1. eauto.
    + clear IHp1 H2.
      destruct nb.
      * simpl. 
Abort.
  

Lemma nb_false : forall g p lr nb nb' lr',
    verifyrule g p lr nb (Some (nb', lr')) ->
    exists nb'', nb' = orb nb nb'' /\
      verifyrule g p lr false (Some (nb'', lr')).
Proof.
  induction p; intros * HV; destruct nb; inversion HV; subst;
    simpl; try (eexists; try exact true; split;
    eauto using verifyrule, nb_true, eq_sym; fail).
    - replace nb' with true in * by eauto using nb_true.
      specialize (IHp2 _ _ _ _ H6) as [? [? ?]].
      eexists; split; eauto using verifyrule.
    - replace nb' with true in * by eauto using nb_true.
      specialize (IHp1 _ _ _ _ H2) as [? [? ?]].
      specialize (IHp2 _ _ _ _ H6) as [? [? ?]].
      eexists; split; eauto using verifyrule.
      eapply VRChoiceSome.
      + eauto.
      + eauto.
    
Abort.




Lemma VRcomplete : forall N g p lr nb,
  count_notvisited lr < N -> exists res, verifyrule g p lr nb res.
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
      destruct (nth_error lr n) eqn:Hne.
      * destruct r;
          try (eexists; eauto using verifyrule, nth_error_nth; fail).
       (* VRNTNotvisitedSome/VRNTNotvisitedNone *)
       specialize (updateVisiting _ _ Hne) as ?.
       assert (count_notvisited (update lr n Visiting) < N) as HN
         by lia.
       specialize (IHN g (nth n g PEmpty)
                       (update lr n Visiting) false HN) as [res Hr].
       destruct res as [[nb' lr'] | ];
         eexists; eauto using verifyrule. 
      * eexists None. apply nth_error_None in Hne.
        eauto using VRNTVisiting, nth_overflow.
Qed.


Ltac breakH :=
    match goal with
    |[H1 : forall _, verifyrule _ ?p ?lr ?br _ -> _,
      H2 : verifyrule _ ?p ?lr ?br _ |- _
     ] => apply H1 in H2;
            try (injection H2; intros; subst); try discriminate
    end.

Ltac nthnth :=
  match goal with
  |[Hn: nth_error ?lr ?i = Some _,
    Hq: nth ?i ?lr Visiting = _ |- _] =>
       eapply nth_error_nth with (d := Visiting) in Hn;
       try congruence
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
         repeat breakH; trivial; try nthnth; try congruence).
Qed.


Fixpoint verifyrule_comp gas
    (g : grammar) (p : pat) (lr : list RuleStatus) (nb : bool) :
      option (option (bool * list RuleStatus)) :=
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
            Some (Some (orb nb nb', update lr i (Visited nb')))
        end
      end
    end
  end.


Lemma nth_nth_error : forall {A : Type} n map (x y : A),
   nth n map x = y -> x <> y -> nth_error map n = Some y.
Proof.
  intros * Hn Hneq.
  destruct (nth_error map n) eqn:?.
  - eapply nth_error_nth with (d := x) in Heqo.
    congruence.
  - exfalso.
    apply nth_error_None in Heqo.
    apply nth_overflow with (d := x) in Heqo.
    congruence.
Qed.


Lemma verifyrule_comp1 : forall gas g p lr nb nb' lr',
  verifyrule_comp gas g p lr nb = Some (Some (nb', lr')) ->
  verifyrule g p lr nb (Some (nb', lr')).
Proof.
  induction gas; intros * H; try discriminate.
  destruct p; simpl in H;
    try (injection H; intros; subst); eauto using verifyrule.
  - destruct (verifyrule_comp gas g p1 lr false) as [[[? ?] | ] | ] eqn:Heq;
       try discriminate.
    destruct b.
    + eauto using verifyrule.
    + injection H; intros; subst. eauto using verifyrule.
  - destruct (verifyrule_comp gas g p1 lr nb) as [[[? ?] | ] | ] eqn:Heq;
       try discriminate.
     eauto using verifyrule.
  - destruct (nth n lr Visiting) eqn:?; try discriminate.
    + destruct (verifyrule_comp gas g (nth n g PEmpty)
                           (update lr n Visiting) false) 
         as [[[? ?] | ] | ] eqn:?;
         try discriminate.
      injection H; intros; subst; clear H.
      econstructor; eauto.
      eapply  nth_nth_error; eauto. discriminate.
    + injection H; intros; subst; clear H.
        apply VRNTVisited.
        eapply  nth_nth_error; eauto.
        discriminate.
Qed.

 

Definition not_nullable g p := forall s, ~matches g p s (Success s).


Definition stateCorrect g lr :=
  forall n, nth_error lr n = Some (Visited false) ->
            not_nullable g (nth n g PEmpty).


Lemma nullableVR: forall N g p lr lr',
  count_notvisited lr < N ->
  verifyrule g p lr false (Some (false, lr')) ->
  stateCorrect g lr ->
  not_nullable g p.
Proof.


