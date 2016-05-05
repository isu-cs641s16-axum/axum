Require Export Pig.Relations.

Definition mapper (s s': schema_ty) : Type := (support s) -> (support s').

Inductive mapped (s s': schema_ty) : relation s -> mapper s s' -> relation s' -> Prop :=
| Mapped: forall (r: relation s) (m: mapper s s') (r': relation s'),
    (* TODO: Add constraints. *)
    mapped s s' r m r'.
