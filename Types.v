Require Export Pig.SfLib.
Require Export Pig.Schema.


Inductive ty: Set :=
| TUnit : ty
| TFn : schema_ty -> schema_ty -> ty
| TPred : schema_ty -> ty
| TSchema : schema_ty -> ty.


Inductive udf_ty : ty -> Prop := 
| UDFTFn: forall s1 s2: schema_ty,
    udf_ty (TFn s1 s2)
| UDFTPred: forall s,
    udf_ty (TPred s).


Inductive loadable_ty : ty -> Prop :=
| LTSchema: forall s: schema_ty,
    loadable_ty (TSchema s)
| LTUDF: forall UDF: ty,
    udf_ty UDF ->
    loadable_ty UDF.


Definition context := partial_map ty.