
Require Export SfLib.


Module physical.


Inductive ty: Type :=
| TUnit : ty
| TFn : ty -> ty -> ty
| TPred : ty -> ty
| TNil: ty               (* Schema Tuple Terminator *)
| TCons: ty -> ty -> ty  (* Schema Tuple Extension Type *)
| TInt: ty               (* An Atomic Schema Attribute Type *)
| TBag: ty -> ty.        (* A Compound Schema Attribute Type *)


Definition col: Type := nat.


Inductive tm: Type :=
 | t_filter: id -> id -> tm
 | t_foreach: id -> id -> tm 
 | t_lrearrange: id -> col -> tm
 | t_grearrange: id -> col -> tm
 | t_package : id -> col -> tm
 | t_load: id -> ty -> tm
 | t_assign: id -> tm -> tm
 | t_store: id -> tm
 | t_seq: tm -> tm -> tm.


Inductive schema_ty : ty -> Prop :=
| STNil:
    schema_ty TNil
| STConsInt: forall T,
    schema_ty T ->
    schema_ty (TCons TInt T)
| STConsBag: forall T1 T2,
    schema_ty T1 ->
    schema_ty T2 ->
    schema_ty (TCons (TBag T1) T2).


Inductive udf_ty : ty -> Prop := 
| UDFTFn: forall S1 S2,
    schema_ty S1 ->
    schema_ty S2 ->
    udf_ty (TFn S1 S2)
| UDFTPred: forall S,
    schema_ty S ->
    udf_ty S.


Inductive loadable_ty : ty -> Prop :=
| LTSchema: forall S,
    schema_ty S ->
    loadable_ty S
| LTUDF: forall UDF,
    udf_ty UDF ->
    loadable_ty UDF.


(* Provides evidence that the given column of a given schema has given type. *)
Inductive schema_column_has_type: ty -> col -> ty -> Prop :=
  | SchemaColumnIsIntZero: forall (TSchema T: ty),
      schema_ty TSchema ->
      schema_column_has_type TSchema O T
  | SchemaColumnIsIntSucc: forall (TSchema TSchemaHead TSchemaTail T: ty) c,
      TSchema = TCons TSchemaHead TSchemaTail ->  (* `THead` is unused. *)
      schema_ty TSchema ->
      schema_column_has_type TSchemaTail c T ->
      schema_column_has_type TSchema (S c) T.


(* ################################### *)
(** *** Typing Relation For Queries *)

(* TODO: Update These! *)
(**

conventions:
 T : a type
 S : a type which satsifies schema_ty
 x, y: identifiers
 s : a statement
 q : a term of query form


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


Definition context := partial_map ty.


Reserved Notation "Gamma '|-' t '\in' T" (at level 40).


Inductive has_type : context -> tm -> ty -> Prop :=

  | T_Filter : forall Gamma x y S,
      Gamma x = Some S ->
      Gamma y = Some (TPred S) ->
      schema_ty S ->
      Gamma |- t_filter x y \in S

  | T_ForEach : forall Gamma x y S1 S2,
      Gamma x = Some(S1) ->
      Gamma y = Some(TFn S1 S2) ->
      schema_ty S1 ->
      schema_ty S2 ->
      Gamma |- t_foreach x y \in S2

  | T_LReArrange : forall Gamma x c S,
      Gamma x = Some S ->
      schema_ty S ->
      schema_column_has_type S c TInt ->
      Gamma |- t_lrearrange x c \in S

  | T_GReArrange : forall Gamma x c S,
      Gamma x = Some S ->
      schema_ty S ->
      schema_column_has_type S c TInt ->
      Gamma |- t_grearrange x c \in S

  | T_Package : forall Gamma x c S1 S2,
      Gamma x = Some S1 ->
      schema_ty S1 ->
      schema_ty S2 ->
      schema_column_has_type S1 c TInt ->
      S2 = TCons TInt (TBag S1) ->
      Gamma |- t_package x c \in S2

  | T_Load : forall Gamma x T,
      Gamma x = None ->
      loadable_ty T ->
      Gamma |- t_load x T \in TUnit

  | T_Assign : forall Gamma x q S,
      Gamma x = None ->
      Gamma |- q \in S ->
      schema_ty S ->
      Gamma |- t_assign x q \in TUnit

  | T_Store : forall Gamma x S,
      Gamma x = Some S ->
      schema_ty S ->
      Gamma |- t_store x \in TUnit

  | T_SeqLoad : forall Gamma x T s1 s2,
      s1 = t_load x T ->
      Gamma |- s1 \in TUnit ->
      (extend Gamma x T) |- s2 \in TUnit ->
      Gamma |- t_seq s1 s2 \in TUnit

  | T_SeqAssign : forall Gamma x q s1 s2 S,
      s1 = t_assign x q ->
      Gamma |- q \in S ->
      schema_ty S ->
      Gamma |- s1 \in TUnit ->
      extend Gamma x S |- s2 \in TUnit ->
      Gamma |- t_seq s1 s2 \in TUnit

  | T_SeqStore : forall Gamma x s1 s2 S,
      s1 = t_store x ->
      Gamma x = Some S ->
      schema_ty S ->
      Gamma |- s1 \in TUnit ->
      Gamma |- s2 \in TUnit ->
      Gamma |- t_seq s1 s2 \in TUnit

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.


(* ################################### *)


End physical.
