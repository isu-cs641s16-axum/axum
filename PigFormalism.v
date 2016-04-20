
Require Export SfLib.

(* Above combines query and stmnt *)
(* Below separates query and stmnt *)

(*
Inductive tm: Type :=
| t_query : query -> tm
| t_stmnt : stmnt -> tm
| t_id : id -> tm.
*)

Inductive ty: Type :=
| TUnit : ty
| TFn : nat -> nat -> ty
| TPred : nat -> ty
| TQuery : nat -> ty.

(*

Inductive tm : Type :=
| t_id : id -> tm
| t_query: query -> tm
| t_stmnt : stmnt -> tm.

Inductive query: Type :=
| q_filter : id -> id -> query
| q_foreach : id -> id -> query
| q_group : id -> nat -> query
| q_join : id -> nat -> id -> nat -> query.

Inductive stmnt: Type :=
| s_load : id -> ty -> stmnt
| s_assign : id -> query -> stmnt
| s_seq : stmnt -> stmnt -> stmnt
| s_store : id -> stmnt.
*)
Inductive tm: Type :=
| t_id: id -> tm
| t_filter: tm -> tm -> tm
| t_foreach: tm -> tm -> tm 
| t_group: tm -> tm -> tm
| t_join: tm -> nat -> tm -> nat -> tm
| t_load: id -> ty -> tm -> tm
| t_assign: id -> ty -> tm -> tm
| t_seq: tm -> tm -> tm
| t_store: id -> ty -> tm.

Module PartialMap.

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

(** Informally, we'll write [Gamma, x:T] for "extend the partial
    function [Gamma] to also map [x] to [T]."  Formally, we use the
    function [extend] to add a binding to a partial map. *)

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
(** *** Typing Relation For Queries*)

(** 
                                  q = q_id x
                               Gamma |- x \in TQuery m
                            ---------------------------                (T_ID)
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
                      ------------------------------------             (T_Group)
                             Gamma |- q \in TQuery m

                                q = q_join x m y n
                                 m <= m'   n <= n'
                      Gamma |- x \in TQuery m'  Gamma |- y \in TQuery n'
                      ---------------------------------------          (T_Join)
                             Gamma |- q \in TQuery (m'+n')


(** *** Typing Relation For Statements*)

(** 
           
                                    Gamma |- x \in T
                             --------------------------                (T_Store)
                             Gamma |- s_store x \in TUnit

                             -----------------------------             (T_Load)
                             Gamma |- s_load x T \in TUnit

                                  s = s_assign x q
               forall T: Gamma |- x not \in T  Gamma |- q \in TQuery m
               ------------------------------------------------------  (T_Assign)
                             Gamma |- s \in TUnit

                       s = s_seq s1 s2       s1 = s_load x T
                             x:T, Gamma |- s2 \in TUnit
                       -------------------------------------           (T_Seq_Load)
                             Gamma |- s \in TUnit

               s = s_seq s1 s2                   s1 = s_assign x q
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
(**  | T_ID : forall Gamma q x,
      q = q_id x ->
      Gamma |- x \in TQuery ->
      Gamma |- q_id x \in TQuery **)
  | T_Filter : forall Gamma x y m n,
      Gamma |- x \in TQuery m -> 
      Gamma |- y \in TPred n-> 
      ble_nat n m = true ->
      Gamma |- t_filter x y \in TQuery m
  | T_ForEach : forall Gamma x y m n,
      Gamma |- x \in TQuery m -> 
      Gamma |- y \in TFn m n -> 
      Gamma |- t_foreach x y \in TQuery n
  | T_Group : forall Gamma x y m n,
      Gamma |- x \in TQuery m -> 
      Gamma |- y \in TPred n-> 
      ble_nat n m = true ->
      Gamma |- t_group x y \in TQuery m
  | T_Join : forall Gamma x y m m' n n',
      Gamma |- x \in TQuery m' -> 
      Gamma |- y \in TPred n'->
      ble_nat m m' = true ->
      ble_nat n n' = true ->
      Gamma |- t_join x m y n \in TQuery(m'+n')

  | T_Load : forall Gamma x y T1,
      Gamma |- t_load x T1 y \in TUnit
  | T_Store : forall Gamma x T1,
      Gamma |- t_id x \in T1 ->
      Gamma |- t_store x T1 \in TUnit


  | T_Assign : forall Gamma x q T1 m,
 (*   
      COQ throwing error trying to resolve it.
  
      ~ (Gamma |- t_id x \in T1) -> *)
      Gamma |- q \in TQuery m ->
      Gamma |- t_assign x T1 q \in TUnit

  | T_SeqLoad : forall Gamma x y T1 s1 s2,
      s1 = t_load x T1 y ->
      (extend Gamma x T1) |- s2 \in TUnit ->
      Gamma |- t_seq s1 s2 \in TUnit
  | T_SeqAssign : forall Gamma x q T1 s1 s2 m,
      s1 = t_assign x T1 q ->
      Gamma |- t_id x \in T1 ->
      Gamma |- q \in TQuery m ->
      (extend Gamma x T1) |- s2 \in TUnit ->
      Gamma |- t_seq s1 s2 \in TUnit
  | T_Seq : forall Gamma s1 s2,
      Gamma |- s1 \in TUnit ->
      Gamma |- s2 \in TUnit ->
      Gamma |- t_seq s1 s2 \in TUnit

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* ################################### *)
