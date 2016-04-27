
Require Export SfLib.

Module logical.

Inductive ty: Type :=
| TUnit : ty
| TFn : nat -> nat -> ty
| TPred : nat -> ty
| TQuery : nat -> ty.

Inductive tm: Type :=
| t_filter: id -> id -> tm
| t_foreach: id -> id -> tm 
(*
| t_group: id -> nat -> tm     (* TODO: Re-introduce this later! *)
*)
| t_join: id -> nat -> id -> nat -> tm
| t_load: id -> ty -> tm
| t_assign: id -> tm -> tm
| t_store: id -> tm
| t_seq: tm -> tm -> tm.

Module PartialMap.

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if eq_id_dec x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite eq_id. auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  x2 <> x1 ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite neq_id; auto.
Qed.

End PartialMap.

Definition context := partial_map ty.

(* ################################### *)
(** *** Typing Relation For Queries *)

(**
                             q = q_id x
                      Gamma |- x \in TQuery m
                     -------------------------                 (T_Id)
                      Gamma |- q \in TQuery m

                        q = q_filter x y
                             n <= m
            Gamma |- x \in TQuery m  Gamma |- y \in TPred n
            -----------------------------------------------    (T_Filter)
                    Gamma |- q \in TQuery m

                      q = q_foreach x y
            Gamma |- x \in TQuery m  Gamma |- y \in TFn m n
            -----------------------------------------------    (T_ForEach)
                     Gamma |- q \in TQuery n


                        q = q_group x y
                            n <= m
           Gamma |- x \in TQuery m  Gamma |- y \in TPred n
           -----------------------------------------------     (T_Group)
                     Gamma |- q \in TQuery m

                        q = q_join x m y n
                         m <= m'   n <= n'
          Gamma |- x \in TQuery m'  Gamma |- y \in TQuery n'
          -------------------------------------------------    (T_Join)
                     Gamma |- q \in TQuery (m'+n')


(** *** Typing Relation For Statements *)

(**

                            Gamma |- x \in T
                     --------------------------                (T_Store)
                     Gamma |- s_store x \in TUnit

                     -----------------------------             (T_Load)
                     Gamma |- s_load x T \in TUnit

                          s = s_assign x q
      forall T: Gamma |- x not \in T  Gamma |- q \in TQuery m
      -------------------------------------------------------  (T_Assign)
                     Gamma |- s \in TUnit

               s = s_seq s1 s2       s1 = s_load x T
                     x:T, Gamma |- s2 \in TUnit
               -------------------------------------           (T_Seq_Load)
                     Gamma |- s \in TUnit

        s = s_seq s1 s2                 s1 = s_assign x q
       Gamma |- x \in T              Gamma |- q \in TQuery  
                   x:T, Gamma |- s2 \in TUnit
       ---------------------------------------------------     (T_Seq_Assign)
                     Gamma |- s \in TUnit

                        s = s_seq s1 s2
         Gamma |- s1 \in TUnit        Gamma |- s2 \in TUnit
         --------------------------------------------------    (T_Seq)
                     Gamma |- s \in TUnit

*)
**)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=

  | T_Filter : forall Gamma x y m n,
      Gamma x = Some (TQuery m) ->
      Gamma y = Some (TPred n) ->
      ble_nat n m = true ->
      Gamma |- t_filter x y \in TQuery m

  | T_ForEach : forall Gamma x y m n,
      Gamma x = Some(TQuery m) ->
      Gamma y = Some(TFn m n) ->
      Gamma |- t_foreach x y \in TQuery n
(*
  | T_Group : forall Gamma x y m n,
      Gamma |- x \in TQuery m -> 
      Gamma |- y \in TPred n-> 
      ble_nat n m = true ->
      Gamma |- t_group x y \in TQuery m
*)
  | T_Join : forall Gamma x y m m' n n',
      Gamma x = Some(TQuery m') ->
      Gamma y = Some(TQuery n') ->
      ble_nat m m' = true ->
      ble_nat n n' = true ->
      Gamma |- t_join x m y n \in TQuery(m'+n')

  | T_Load : forall Gamma x T,
      Gamma x = None ->
      Gamma |- t_load x T \in TUnit

  | T_Assign : forall Gamma x q m,
      Gamma x = None ->
      Gamma |- q \in TQuery m ->
      Gamma |- t_assign x q \in TUnit

  | T_Store : forall Gamma x m,
      Gamma x = Some (TQuery m) ->
      Gamma |- t_store x \in TUnit

  | T_SeqLoad : forall Gamma x T s1 s2,
      s1 = t_load x T ->
      Gamma |- s1 \in TUnit ->
      (extend Gamma x T) |- s2 \in TUnit ->
      Gamma |- t_seq s1 s2 \in TUnit

  | T_SeqAssign : forall Gamma x q s1 s2 m,
      s1 = t_assign x q ->
      Gamma |- q \in TQuery m ->
      Gamma |- s1 \in TUnit ->
      extend Gamma x (TQuery m) |- s2 \in TUnit ->
      Gamma |- t_seq s1 s2 \in TUnit

  | T_SeqStore : forall Gamma x s1 s2,
      s1 = t_store x ->
      Gamma |- s1 \in TUnit ->
      Gamma |- s2 \in TUnit ->
      Gamma |- t_seq s1 s2 \in TUnit

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* ################################### *)

End logical.

Module physical.

Inductive ty: Type :=
 | TUnit : ty
 | TFn : nat -> nat -> ty
 | TPred : nat -> ty
 | TQuery : nat -> ty.

Inductive tm: Type :=
 | t_id: id -> tm
 | t_filter: tm -> tm -> tm
 | t_foreach: tm -> tm -> tm 
 | t_rearrange: tm -> tm
 | t_package : tm -> nat -> tm
 | t_load: id -> tm
 | t_assign: id -> tm -> tm
 | t_seq: tm -> tm -> tm
 | t_store: id -> tm.

End physical.