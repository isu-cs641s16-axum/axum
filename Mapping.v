Require Export Pig.Relations.


Definition mapper (s s': schema_ty) : Type := (support s) -> (support s').


(* One Bad Idea: Count the number of sources which hit the given sink. Use this
   to construct a specification for the mapped multiset. *)
Definition count_number_of_sources (s s':schema_ty) (r: relation s) (map: mapper s s') (sink: support s') : nat.
Admitted.


Definition is_mapped (s s': schema_ty) (r: relation s) (m: mapper s s') (r': relation s') : Prop.
Admitted.


Inductive mapped (s s': schema_ty) : relation s -> mapper s s' -> relation s' -> Prop :=
| Mapped: forall (r: relation s) (m: mapper s s') (r': relation s'),
    is_mapped s s' r m r' ->
    mapped s s' r m r'.


(* These examples build on the examples in `Relations`. *)
Example nat_identity_mapper := fun (n: nat) => n.
