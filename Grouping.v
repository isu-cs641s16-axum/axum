Require Export Pig.Schema.

Definition can_group_by (s: schema_ty) (c: col): Prop :=
  schema_column_has_type s c CTyNat.

Definition can_package_by := can_group_by.