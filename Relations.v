Require Export Coq.Sets.Multiset.
Require Export Pig.Schema.


Inductive relation (s: schema_ty) : Type := 
| Relation: multiset (support s) -> relation s.


Definition relation_data (s: schema_ty) (r: relation s) : multiset (support s) :=
  match r with
  | Relation _ mset => mset
  end.


Definition relation_eq (s: schema_ty) (r1 r2: relation s) : Prop :=
  meq (relation_data s r1) (relation_data s r2).


(* An example schema with just one column: a nat column: *)

Example nat_schema : schema_ty := ( CTyNat *** ).
Example nat_tuple : support nat_schema := 1.
Example empty_nat_relation : relation nat_schema :=
  Relation nat_schema (EmptyBag nat).

(* Can be used to generate various example singleton relations for various
   schema using the `SingletonBag` definition. *)
Example singleton_relation (s: schema_ty) :=
  (SingletonBag (support_eq s) (support_eq_dec s)).


(* TODO: Finish this example. *)
(*
Example singleton_nat_relation : relation nat_schema :=
  Relation nat_schema (singleton_relation nat_schema 5).
Example singleton_nat_relation' : relation nat_schema :=
  Relation nat_schema (Bag (fun (n: nat) => match n with
                                            | 5 => 1
                                            | _ => 0
                                            end)).
Lemma two_singletons_are_eq : relation_eq nat_schema singleton_nat_relation singleton_nat_relation'.
  unfold relation_eq. simpl.
  unfold meq. simpl.
  intro. induction a.
  - (* a = O *) admit.
  - (* a = S a *) admit.
Admitted.
*)

(* An example schema with just one column: a bag (of nat): *)
Example bag_schema := (CTyBag (CTyNat ***) ***).
Example bag_tuple : support bag_schema := EmptyBag nat.
Example bag_relation : relation bag_schema := Relation bag_schema (EmptyBag (multiset nat)).

(* An example schema with two cols: nat and bag of nat. *)
Example nat_bag_schema : schema_ty := CTyNat *** CTyBag (CTyNat ***) ***.
Example nat_bag_tuple : support nat_bag_schema :=  (1, (EmptyBag nat)).
Example nat_bag_relation : relation nat_bag_schema := Relation nat_bag_schema (EmptyBag (nat * (multiset nat))).
