Require Export Pig.Relations.

Definition can_join_by (s: schema_ty) (c: col): Prop :=
  schema_column_has_type s c CTyNat.


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


(* IDEA: Maybe we don't need to model the tuples themselves, just their types.
         However, we do need to represent sorted lists of tuples, but we can
         do that using types (see stdlib's `Sorted`). Because of this I am
         hoping that we don't need to `fuse_tuples`. *)

(*
Fixpoint fuse_tuples (s1 s2: schema_ty) (t1: support s1) (t2: support s2) :
                                     support (schema_concatenation s1 s2) := ???
*)


Inductive joined (s1 s2: schema_ty): relation s1 -> col -> relation s2 -> col -> Prop :=
  | Joined : forall (r1: relation s1) (r2: relation s2) (c1 c2: col),
     (* TODO: Add constraints. *)
     joined s1 s2 r1 c1 r2 c2.
