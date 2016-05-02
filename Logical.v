
Require Export SfLib.

Module logical.

Inductive ty: Type :=
| TUnit : ty
| TFn : ty -> ty -> ty
| TPred : ty -> ty
| TNil: ty               (* Schema Tuple Terminator *)
| TCons: ty -> ty -> ty  (* Schema Tuple Extension Type *)
| TInt: ty               (* An Atomic Schema Attribute Type *)
| TBag: ty -> ty.        (* A Compound Schema Attribute Type *)


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


(* Indicates a column within a schema. Used in the JOIN query's BY clauses. *)
Definition col: Type := nat.


Inductive tm: Type :=
| t_filter: id -> id -> tm
| t_foreach: id -> id -> tm 
| t_group: id -> col -> tm
| t_join: id -> col -> id -> col -> tm
| t_load: id -> ty -> tm
| t_assign: id -> tm -> tm
| t_store: id -> tm
| t_seq: tm -> tm -> tm.


(* Provides evidence that a particular column of a schema is of type `TInt`. *)
Inductive schema_column_is_int: ty -> col -> Prop :=

  | SchemaColumnIsIntZero: forall (T: ty),
      schema_ty T ->
      schema_column_is_int T O

  | SchemaColumnIsIntSucc: forall (T THead TTail: ty) (c: col),
      T = TCons THead TTail ->  (* Note that `THead` is unused. *)
      schema_ty T ->
      schema_column_is_int TTail c ->
      schema_column_is_int T (S c).


(* The concatenation of schemas T1 and T2 is T3. *)
Inductive concatenated_schema: ty -> ty -> ty -> Prop :=

  | CatSchemaNil: forall T,
      schema_ty TNil ->
      schema_ty T ->
      concatenated_schema TNil T T

  | CatSchemaCons: forall T1 THead T1tail T2 T3 T3tail,
      schema_ty T1 ->
      schema_ty T2 ->
      T1 = TCons THead T1tail ->
      T3 = TCons THead T3tail ->
      concatenated_schema T1tail T2 T3tail ->
      concatenated_schema T1 T2 T3.


(* The concatenation of schemas T1 and T2 is also a schema. *)
Lemma concatenation_of_schemas_is_schema : forall T1 T2 T3: ty,
  schema_ty T1 ->
  schema_ty T2 ->
  concatenated_schema T1 T2 T3 ->
  schema_ty T3.
Proof.
  intros T1 T2 T3 H_schema_T1 H_schema_T2 H_concat. induction H_concat.
  - (* CatSchemaNil *) auto.
  - (* CatSchemaCons *) rewrite -> H2. inversion H.
    + (* STNil *) rewrite <- H3 in H1. inversion H1.
    + (* STConsInt *)
      (* Concretize stmnt to prove to use TInt & make IHH_concat usable. *)
      rewrite <- H4 in H1.
      inversion H1.
      apply STConsInt.
      apply IHH_concat.
      * rewrite H7 in H3. assumption.
      * assumption.
    + (* STConsBag *)
      (* Concretize stmnt to prove to use TBag & make IHH_concat usable. *)
      rewrite <- H5 in H1.
      inversion H1.
      apply STConsBag.
      * assumption.
      * apply IHH_concat; subst; try assumption.
Qed.


Definition context := partial_map ty.

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

  | T_Group : forall Gamma x c S1 S2,
      Gamma x = Some S1 ->
      schema_ty S1 ->
      schema_ty S2 ->
      schema_column_is_int S1 c ->
      S2 = TCons TInt (TBag S1) ->
      Gamma |- t_group x c \in S2

  | T_Join : forall Gamma x y cx cy S1 S2 S3,
      Gamma x = Some(S1) ->
      Gamma y = Some(S2) ->
      schema_ty S1 ->
      schema_ty S2 ->
      schema_column_is_int S1 cx ->
      schema_column_is_int S2 cy ->
      concatenated_schema S1 S2 S3 ->
      Gamma |- t_join x cx y cx \in S3

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


End logical.
