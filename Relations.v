Require Export Coq.Sets.Multiset.
Require Export Pig.Schema.


(* The type of each tuple within a relation with the given schema. *)
Fixpoint support (s: schema_ty) : Type :=
  match s with
  | STyNil => unit
  | a *** => helper a
  | a *** s' => (helper a) * support s'
  end
with helper(c: col_ty) : Type :=
  match c with
  | CTyNat => nat
  | CTyBag s_nested => multiset (support s_nested)
  end.


Inductive relation (s: schema_ty) : Type := 
| Relation: multiset (support s) -> relation s.


(* TODO: relation equality. *)


(* An example schema with just one column: a nat column: *)
Example nat_schema : schema_ty := (CTyNat ***).
Example nat_tuple : support nat_schema := 1.
Example nat_relation : relation nat_schema := Relation nat_schema (EmptyBag nat).

(* An example schema with just one column: a bag (of nat): *)
Example bag_schema := (CTyBag (CTyNat ***) ***).
Example bag_tuple : support bag_schema := EmptyBag nat.
Example bag_relation : relation bag_schema := Relation bag_schema (EmptyBag (multiset nat)).

(* An example schema with two cols: nat and bag of nat. *)
Example nat_bag_schema : schema_ty := CTyNat *** CTyBag (CTyNat ***) ***.
Example nat_bag_tuple : support nat_bag_schema :=  (1, (EmptyBag nat)).
Example nat_bag_relation : relation nat_bag_schema := Relation nat_bag_schema (EmptyBag (nat * (multiset nat))).
