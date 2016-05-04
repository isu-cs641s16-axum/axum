Require Export Pig.SfLib.
Require Export Pig.Schema.


Inductive ty: Set :=
| TUnit : ty
| TFn : schema_ty -> schema_ty -> ty
| TPred : schema_ty -> ty
| TSchema : schema_ty -> ty.


Inductive udf_ty : ty -> Prop := 
| UDFTFn: forall S1 S2,
    udf_ty (TFn S1 S2)
| UDFTPred: forall S,
    udf_ty S.


Inductive loadable_ty : ty -> Prop :=
| LTSchema: forall S,
    loadable_ty S
| LTUDF: forall UDF,
    udf_ty UDF ->
    loadable_ty UDF.


Definition context := partial_map ty.