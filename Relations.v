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


Inductive relation : schema_ty -> Type :=
| Relation: forall (s: schema_ty),
    multiset (support s) -> relation s.

(* What's wrong with this way of defining it? *)
(* Definition relation (s: schema_ty) (rows: list (support s)) : (s, rows). *)

(* TODO: Make equality *)
Definition relation_eq (s: schema_ty) (r1 r2: relation s) : Prop := (r1 = r2).


(* An example schema with just one column: a nat column: *)
Example nat_schema : schema_ty := (CTyNat ***).
(*
Example nat_tuple : support nat_schema := 1.
Example nat_relation : relation nat_schema := relation (Bag (fun (x: nat) => 0)).
*)

(* An example schema with just one column: a bag (of nat): *)
Example bag_schema := (CTyBag (CTyNat ***) ***).
(*
Example bag_tuple : support bag_schema := [1; 1].
Example bag_relation : relation bag_schema := [[1; 2]; [1; 2]].
*)

(* An example schema with two cols: nat and bag of nat. *)
Example nat_bag_schema : schema_ty := CTyNat *** CTyBag (CTyNat ***) ***.
(*
Example nat_bag_tuple : support nat_bag_schema := (1, [1; 2; 1]).
Example nat_bag_relation : relation nat_bag_schema := [(1, [1; 2; 1]); (2, [])].
*)