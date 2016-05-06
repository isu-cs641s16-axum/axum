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
Definition col: Set := nat.


(* Provides evidence that the given column of a given schema has given attr. *)

Inductive schema_column_has_type: schema_ty -> col -> col_ty -> Prop :=
  | SCHAZero: forall (s s': schema_ty) (c: col_ty),
      s = c *** s' ->
      schema_column_has_type s O c
  | SCHASucc: forall (s s': schema_ty) (i i': col) (c c': col_ty),
      i = S(i') ->
      s = c' *** s' ->
      schema_column_has_type s' i c'.


Fixpoint schema_concatenation (s1 s2 : schema_ty): schema_ty :=
  match s1 with
  | STyNil => s2
  | c *** => STyPair c s2
  | c *** s1' => c *** (schema_concatenation s1' s2)
  end.


Inductive concatenated_schema: schema_ty -> schema_ty -> schema_ty -> Prop :=
| CatSchemaZeroAttr: forall s,
    concatenated_schema STyNil s s
| CatSchemaOneAttr: forall a s,
    concatenated_schema (a ***) s (a *** s)
| CatSchemaCons: forall a s1 s2 s3,
    concatenated_schema s1 s2 s3 ->
    concatenated_schema (a *** s1) s2 (a *** s3).


Lemma schema_concatenation_correct: forall (s1 s2: schema_ty),
  concatenated_schema s1 s2 (schema_concatenation s1 s2).
Proof.
  intros. induction s1.
  - admit.
  - admit.
Admitted.


Inductive filter_fn : Set :=
| FilterFn: id -> schema_ty -> filter_fn.

Inductive map_fn : Set :=
| MapFn: id -> schema_ty -> map_fn.


(* IDEA: Maybe we don't need to model the tuples themselves, just their types.
         However, we do need to represent sorted lists of tuples, but we can
         do that using types (see stdlib's `Sorted`). Because of this I am
         hoping that we don't need to `fuse_tuples`. *)

(*
Fixpoint fuse_tuples (s1 s2: schema_ty) (t1: support s1) (t2: support s2) :
                                     support (schema_concatenation s1 s2) := ???
*)
