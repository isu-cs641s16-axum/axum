Require Export Coq.Sets.Multiset.
Require Import SfLib.


Inductive schema_ty : Set :=
  | STyPair: col_ty -> schema_ty -> schema_ty
  | STyNil: schema_ty
with col_ty : Set :=
  | CTyNat: col_ty
  | CTyBag: schema_ty -> col_ty.

Notation " x *** " := (STyPair x STyNil) (at level 51, right associativity).
Notation " x '***' y " := (STyPair x y) (at level 51, right associativity).


(* Indicates a column within a schema. Used in the JOIN query's BY clauses. *)
Definition col := nat.


(* Provides evidence that the given column of a given schema has given attr. *)
Inductive schema_column_has_type: schema_ty -> col -> col_ty -> Prop :=
  | SCHAZero: forall (s s': schema_ty) (c: col_ty),
      s = c *** s' ->
      schema_column_has_type s O c
  | SCHASucc: forall (s s': schema_ty) (i i': col) (c c': col_ty),
      i = S(i') ->
      s = c' *** s' ->
      schema_column_has_type s' i c'.


(* The type of each tuple within a relation with the given schema. *)
Fixpoint support (s: schema_ty) : Type :=
  match s with
  | STyNil => unit
  | a *** => helper a
  | a *** s' => (helper a) * support s'
  end
with helper(c: col_ty) : Type :=
  match c with
  | CTyNat => nat
  | CTyBag s_nested => multiset (support s_nested)
  end.


(* Construct a custom equality function over the support of s. *)
Definition support_eq (s: schema_ty) (row1 row2: support s) : Prop := (row1 = row2).

Lemma support_eq_dec (s: schema_ty):
  forall (x y : support s), {(support_eq s) x y} + {~ (support_eq s) x y}.
Proof.
  intros. unfold support_eq. Admitted.
