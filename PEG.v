From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.

Inductive pat : Type :=
  | PEmpty : pat
  | PChar : ascii -> pat
  | PDot : pat
  | PSequence : pat -> pat -> pat
  | PChoice : pat -> pat -> pat
  | PKleene : pat -> pat
  | PNot : pat -> pat
  .

Inductive matches : pat -> string -> option string -> Prop :=
  | MEmpty :
      forall s,
      matches PEmpty s (Some s)
  | MCharEmptyString :
      forall a,
      matches (PChar a) EmptyString None
  | MCharStringSameChar :
      forall a s,
      matches (PChar a) (String a s) (Some s)
  | MCharStringDifferentChar :
      forall a a' s,
      a <> a' ->
      matches (PChar a) (String a' s) None
  | MDotEmptyString :
      matches PDot EmptyString None
  | MDotString :
      forall a s,
      matches PDot (String a s) (Some s)
  | MSequenceNone :
      forall p1 p2 s1 s2,
      matches p1 s1 None ->
      matches (PSequence p1 p2) (append s1 s2) None
  | MSequenceSome :
      forall p1 p2 s1 s2 res,
      matches p1 s1 (Some s2) ->
      matches p2 s2 res ->
      matches (PSequence p1 p2) s1 res
  | MChoiceNone :
      forall p1 p2 s res,
      matches p1 s None ->
      matches p2 s res ->
      matches (PChoice p1 p2) s res
  | MChoiceSome :
      forall p1 p2 s s',
      matches p1 s (Some s') ->
      matches (PChoice p1 p2) s (Some s')
  | MKleeneNone :
      forall p s,
      matches p s None ->
      matches (PKleene p) s (Some s)
  | MKleeneSome :
      forall p s s' res,
      matches p s (Some s') ->
      matches (PKleene p) s' res ->
      matches (PKleene p) s res
  | MNotNone :
      forall p s,
      matches p s None ->
      matches (PNot p) s (Some s)
  | MNotSome :
      forall p s s',
      matches p s (Some s') ->
      matches (PNot p) s None
  .
