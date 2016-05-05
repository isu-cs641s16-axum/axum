Require Export Pig.Relations.


(* Note: We assume that a GROUP-BY can only be performed using nat columns;
   it doesn't make sent to group by a bag column. *)

Definition can_group_by (s: schema_ty) (c: col): Prop :=
  schema_column_has_type s c CTyNat.


Definition group_schema (s: schema_ty) : schema_ty :=
  (CTyNat *** (CTyBag s) ***).


Inductive grouped (s: schema_ty) : relation s -> col -> relation (group_schema s) -> Prop :=
| Grouped: forall r c r',
    (* TODO: Add constraints. *)
    grouped s r c r'.


Definition can_package_by := can_group_by.

