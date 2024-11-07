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

Ltac specialize_eq_hyp :=
  match goal with
    [ Hx: ?x = ?y -> _, Hy: ?x = ?y |- _ ] =>
        specialize (Hx Hy)
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

Ltac destruct2sep :=
  match goal with [
    Hx1: ?C ?a ?b = _,
    Hx2: ?C ?a ?b = _ |- _ ] =>
        rewrite Hx1 in Hx2;
        try (injection Hx2 as Hx2; subst);
        try discriminate
  end.

Ltac rewrite_match_subject_in_goal :=
  match goal with
    [ Hx: ?lhs = _ |- match ?lhs with _ => _ end = _ ] =>
      rewrite Hx
  end.

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
