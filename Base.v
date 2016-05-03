Require Export Pig.SfLib.

Inductive ty: Type :=
| TUnit : ty
| TFn : ty -> ty -> ty
| TPred : ty -> ty
| TNil: ty               (* Schema Tuple Terminator *)
| TCons: ty -> ty -> ty  (* Schema Tuple Extension Type *)
| TInt: ty               (* An Atomic Schema Attribute Type *)
| TBag: ty -> ty.        (* A Compound Schema Attribute Type *)


Inductive schema_ty : ty -> Prop :=
| STNil:
    schema_ty TNil
| STConsInt: forall T,
    schema_ty T ->
    schema_ty (TCons TInt T)
| STConsBag: forall T1 T2,
    schema_ty T1 ->
    schema_ty T2 ->
    schema_ty (TCons (TBag T1) T2).


Inductive udf_ty : ty -> Prop := 
| UDFTFn: forall S1 S2,
    schema_ty S1 ->
    schema_ty S2 ->
    udf_ty (TFn S1 S2)
| UDFTPred: forall S,
    schema_ty S ->
    udf_ty S.


Inductive loadable_ty : ty -> Prop :=
| LTSchema: forall S,
    schema_ty S ->
    loadable_ty S
| LTUDF: forall UDF,
    udf_ty UDF ->
    loadable_ty UDF.


(* Indicates a column within a schema. Used in the JOIN query's BY clauses. *)
Definition col: Type := nat.


(* Provides evidence that the given column of a given schema has given type. *)
Inductive schema_column_has_type: ty -> col -> ty -> Prop :=
  | SchemaColumnIsIntZero: forall (TSchema T: ty),
      schema_ty TSchema ->
      schema_column_has_type TSchema O T
  | SchemaColumnIsIntSucc: forall (TSchema TSchemaHead TSchemaTail T: ty) c,
      TSchema = TCons TSchemaHead TSchemaTail ->  (* `THead` is unused. *)
      schema_ty TSchema ->
      schema_column_has_type TSchemaTail c T ->
      schema_column_has_type TSchema (S c) T.


(* The concatenation of schemas T1 and T2 is T3. *)
Inductive concatenated_schema: ty -> ty -> ty -> Prop :=

  | CatSchemaNil: forall T,
      schema_ty TNil ->
      schema_ty T ->
      concatenated_schema TNil T T

  | CatSchemaCons: forall T1 THead T1tail T2 T3 T3tail,
      schema_ty T1 ->
      schema_ty T2 ->
      T1 = TCons THead T1tail ->
      T3 = TCons THead T3tail ->
      concatenated_schema T1tail T2 T3tail ->
      concatenated_schema T1 T2 T3.


(* The concatenation of schemas T1 and T2 is also a schema. *)
Lemma concatenation_of_schemas_is_schema : forall T1 T2 T3: ty,
  schema_ty T1 ->
  schema_ty T2 ->
  concatenated_schema T1 T2 T3 ->
  schema_ty T3.
Proof.
  intros T1 T2 T3 H_schema_T1 H_schema_T2 H_concat. induction H_concat.
  - (* CatSchemaNil *) auto.
  - (* CatSchemaCons *) rewrite -> H2. inversion H.
    + (* STNil *) rewrite <- H3 in H1. inversion H1.
    + (* STConsInt *)
      (* Concretize stmnt to prove to use TInt & make IHH_concat usable. *)
      rewrite <- H4 in H1.
      inversion H1.
      apply STConsInt.
      apply IHH_concat.
      * rewrite H7 in H3. assumption.
      * assumption.
    + (* STConsBag *)
      (* Concretize stmnt to prove to use TBag & make IHH_concat usable. *)
      rewrite <- H5 in H1.
      inversion H1.
      apply STConsBag.
      * assumption.
      * apply IHH_concat; subst; try assumption.
Qed.
