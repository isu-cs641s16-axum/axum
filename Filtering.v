Require Export Pig.Relations.


Definition filter (s: schema_ty) : Type := (support s) -> bool.


Inductive filtered (s: schema_ty): relation s -> filter s -> relation s -> Prop :=
  | Filtered : forall (f: filter s) (r r': relation s),
     (* TODO: Add constraints. *)
     filtered s r f r'.
