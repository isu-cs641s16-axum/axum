Require Import Pig.Schema.

Definition can_rearrange_by (s: schema_ty) (c: col) : Prop :=
  schema_column_has_type s c CTyNat.