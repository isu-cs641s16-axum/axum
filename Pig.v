
Require Export SfLib.

Inductive ty: Type :=
| TUnit : ty
| TNat : ty
| TFn : ty -> ty -> ty
| TPred : ty -> ty
| TQuery : ty -> ty.

Inductive query: Type :=
| q_filter : id -> id -> query
| q_foreach : id -> id -> query
| q_group : id -> nat -> query
| q_join : id -> nat -> id -> nat -> query
| q_id : id -> query.

Inductive statement: Type :=
| s_store : id -> statement
| s_assign : id -> query -> statement
| s_load: id -> statement
| s_seq: statement -> statement -> statement.

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
                               Gamma x = TQuery m
                            -----------------------                    (T_ID)
                            Gamma |- q \in TQuery m

                                q = q_filter x y
                                     n <= m
                      Gamma x = TQuery m  Gamma y = TPred n
                      --------------------------------------           (T_Filter)
                            Gamma |- q \in TQuery m

                              q = q_foreach x y
                      Gamma x = TQuery m  Gamma y = TFn m n
                      ------------------------------------             (T_ForEach)
                             Gamma |- q \in TQuery n


                                q = q_group x y
                                    n <= m
                      Gamma x = TQuery m  Gamma y = TPred n
                      ------------------------------------             (T_Group)
                             Gamma |- q \in TQuery m

                                q = q_join x m y n
                                 m <= m'   n <= n'
                      Gamma x = TQuery m'  Gamma y = TQuery n'
                      ---------------------------------------          (T_Join)
                             Gamma |- q \in TQuery (m'+n')


(** *** Typing Relation For Statements*)

(** 
           
                                    Gamma x = T
                             --------------------------                (T_Store)
                             Gamma |- s_store \in TUnit

                             -----------------------------             (T_Load)
                             Gamma |- s_load x T \in TUnit

                                  s = s_assign x q
                      Gamma x not \in T      Gamma q = TQuery m
                      -----------------------------------------        (T_Assign)
                             Gamma |- s \in TUnit

                       s = s_seq s1 s2       s1 = s_load x T
                       Gamma x = TNat       Gamma s2 = TUnit
                       -------------------------------------           (T_Seq_Load)
                             Gamma |- s \in TUnit

               s = s_seq s1 s2                   s1 = s_assign x q
               Gamma x \in T  Gamma q \in TQuery  Gamma s2 = TUnit
               ---------------------------------------------------     (T_Seq_Assign)
                             Gamma |- s \in TUnit

                                s = s_seq s1 s2
                   Gamma s1 = TUnit        Gamma s2 = TUnit
                   ----------------------------------------            (T_Seq)
                             Gamma |- s \in TUnit

*)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
    
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_ID : forall Gamma x T,
      Gamma x = TQuery ->
      Gamma |- q_id x \in TQuery
  | T_Filter : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_ForEach : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_Group : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_Join : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* ################################### *)
