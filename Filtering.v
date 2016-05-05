Require Export Pig.Relations.


Definition filter (s: schema_ty) : Type := (support s) -> bool.


Definition is_filtered (s:schema_ty) (r: relation s) (f:filter s) (r': relation s) :=
  let m  := (relation_data s r) in
  let m' := (relation_data s r') in
  forall tup: (support s),
    multiplicity m tup = match (f tup) with
                         | true => multiplicity m' tup
                         | false => 0
                         end.

Inductive filtered (s: schema_ty): relation s -> filter s -> relation s -> Prop :=
  | Filtered : forall (f: filter s) (r r': relation s),
     is_filtered s r f r' ->
     filtered s r f r'.
